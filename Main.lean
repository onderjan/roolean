import RooleCheck

inductive Character
  | TabSpace
  | LineBreak
  | Semicolon
  | ParenOpen
  | ParenClose
  | Other (c: Char)
deriving Repr

inductive Token
  | ParenOpen
  | ParenClose
  | Text (text: String)
deriving Repr

inductive Current
  | Start (token: Token)
  | Comment
  | Empty
deriving Repr

def new_current (character: Character): Current :=
  match character with
  | Character.TabSpace => Current.Empty
  | Character.LineBreak => Current.Empty
  | Character.Semicolon => Current.Comment
  | Character.ParenOpen => Current.Start Token.ParenOpen
  | Character.ParenClose => Current.Start Token.ParenClose
  | Character.Other c => Current.Start (Token.Text (String.singleton c))


structure Lexer where
  current: Current
  tokens: (List Token)

def lex_init: Lexer := { current := Current.Empty, tokens := List.nil }

def lex_classify (char: Char) : Character :=
  match char with
    | '\t' | ' '  => Character.TabSpace
    | '\r' | '\n'  => Character.LineBreak
    | ';' => Character.Semicolon
    | '(' => Character.ParenOpen
    | ')' => Character.ParenClose
    | _ => Character.Other char

def lex_start_update (token: Token) (next: Character) : (Option Token) × Current :=
  match token, next with
    | token, Character.TabSpace
      | token, Character.LineBreak => (token, Current.Empty)
    | Token.Text text, Character.Other next_char =>
        (none, Current.Start (Token.Text (String.push text next_char)))
    | Token.Text text, next  => ((Token.Text text), new_current next)
    | token,next => (token, new_current next)

def lex_comment_update (next: Character) : Current :=
  match next with
    | Character.LineBreak => Current.Empty
    | _ => Current.Comment


def lex_update (current: Current) (next: Character) : (Option Token) × Current :=
  match current with
    | Current.Start (token) => lex_start_update token next
    | Current.Comment => (none, lex_comment_update next)
    | Current.Empty => (none, new_current next)

def lex_char (lexer: Lexer) (char: Char) : Lexer :=
  let classified := (lex_classify char)
  let (previous, current) := lex_update lexer.current classified
  let tokens := if let some previous := previous then
    List.cons previous lexer.tokens
  else
    lexer.tokens

  { tokens, current }

def lex_finish (lexer: Lexer) : List Token :=
  List.reverse lexer.tokens

def lex_fold (init: Lexer) (char: Char) : Lexer :=
  lex_char init char

def lex: IO (List Token) := do
  let string ← IO.FS.readFile "benchmarks/addsub.smt2"
  IO.println s!"Read:\n---\n{string}\n---\n"
  let iter := String.chars string
  let init := lex_init
  let lexer := Std.Iter.fold lex_char init iter
  pure (lex_finish lexer)


def main : IO Unit := do
  let _discard ← lex

#eval lex
