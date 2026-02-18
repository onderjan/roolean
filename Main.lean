import RooleCheck

inductive Character
  -- white_space_char, space is printable_char
  | TabSpace
  -- white_space_char, ends comments
  | LineBreak
  -- printable_char, starts comments outside string literals / quoted symbols
  | Semicolon
  -- printable_char
  | ParenOpen
  -- printable_char
  | ParenClose
  | Digit (digit: Fin 10)
  -- TODO
  | Other (c: Char)
deriving Repr

inductive Token
  | ParenOpen
  | ParenClose
  | Numeral (num: Nat)
  | Text (text: String)
  -- TODO fail instead of giving an invalid token
  | Invalid
deriving Repr

-- Determines the state state of the lexer.
inductive State
  -- State holding a start of a token.
  | Start (token: Token)
  -- State within a comment, waiting for a line break.
  | Comment
  -- State holds no token and not within a comment.
  | Empty
deriving Repr

def new_state (character: Character): State :=
  match character with
  -- whitespace, no token nor comment
  | Character.TabSpace | Character.LineBreak => State.Empty
  -- semicolon, start a comment
  | Character.Semicolon => State.Comment
  -- each parenthesis is a token
  | Character.ParenOpen => State.Start Token.ParenOpen
  | Character.ParenClose => State.Start Token.ParenClose
  -- digit, start a numeral
  | Character.Digit d => State.Start (Token.Numeral d)
  -- TODO
  | Character.Other c => State.Start (Token.Text (String.singleton c))


-- Lexer contained start of a token, return an optionally produced token and new lexer state.
def lex_start_update (token: Token) (next: Character) : (Option Token) × State :=
  match token, next with
    -- incoming whitespace, produce the token and clear the state state
    | token, Character.TabSpace | token, Character.LineBreak => (token, State.Empty)
    -- we have a number, digit incoming
    | Token.Numeral number, Character.Digit digit =>
      if number == 0 then
        -- numbers starting with the digit zero, except for zero, are disallowed
        -- TODO error
        (some Token.Invalid, State.Empty)
      else
        -- multiply the previous numeral by base and add digit
        (none, State.Start (Token.Numeral (number * 10 + digit)))
    -- TODO
    | Token.Text text, Character.Other next_char =>
        (none, State.Start (Token.Text (String.push text next_char)))
    | Token.Text text, next  => ((Token.Text text), new_state next)
    -- could not update the state token, produce it and start a new one
    | token,next => (token, new_state next)

-- Lexer contained start of a comment, return the new lexer state.
def lex_comment_update (next: Character) : State :=
  match next with
    -- incoming line break, get back to non-comment empty state
    | Character.LineBreak => State.Empty
    -- not a line break, remain in the comment state
    | _ => State.Comment

-- From a state lexer state and a character, return an optionally produced token and new lexer state.
def lex_update (state: State) (next: Character) : (Option Token) × State :=
  match state with
    | State.Start (token) => lex_start_update token next
    | State.Comment => (none, lex_comment_update next)
    | State.Empty => (none, new_state next)

structure Lexer where
  state: State
  tokens: (List Token)

def lex_init: Lexer := { state := State.Empty, tokens := List.nil }

def lex_classify (char: Char) : Character :=
  let code := Char.toNat char
  let zero_code := Char.toNat '0'
  if code >= zero_code && code < zero_code + 10 then
    Character.Digit ((Fin.ofNat 10) (code - zero_code))
  else match char with
    | '\t' | ' '  => Character.TabSpace
    | '\r' | '\n'  => Character.LineBreak
    | ';' => Character.Semicolon
    | '(' => Character.ParenOpen
    | ')' => Character.ParenClose
    | _ => Character.Other char


-- Update the lexer with a new character.
def lex_char (lexer: Lexer) (char: Char) : Lexer :=
  -- classify the character and update the lexer
  let (produced, state) := lex_update lexer.state (lex_classify char)
  -- if a token was produced, add it to the list
  let tokens := if let some produced := produced then
    List.cons produced lexer.tokens
  else
    lexer.tokens

  { tokens, state }

-- Finish lexing, produce a list of tokens.
def lex_finish (lexer: Lexer) : List Token :=
  let tokens := match lexer.state with
    -- a token start is still waiting, add it to the list
    | State.Start (token) => List.cons token lexer.tokens
    -- nothing is waiting
    | State.Comment | State.Empty => lexer.tokens
  -- reverse the list as we added each new token to its start
  List.reverse tokens

def lex_iter {α : Type} [Std.Iterator α Id Char] [Std.IteratorLoop α Id Id]
  (it: Std.Iter (α:=α) Char): List Token :=
    let lexer := Std.Iter.fold lex_char lex_init it
    lex_finish lexer

def process: IO (List Token) := do
  let string ← IO.FS.readFile "benchmarks/addsub.smt2"
  IO.println s!"Read:\n---\n{string}\n---\n"
  let iter := String.chars string
  let init := lex_init
  let lexer := Std.Iter.fold lex_char init iter
  pure (lex_finish lexer)


def main : IO Unit := do
  let _discard ← process

#eval lex_iter (List.iter ['5', '7'])

#eval process
