import RooleCheck

inductive Character
  | Whitespace
  | ParenOpen
  | ParenClose
  | Other (c: Char)
deriving Repr

inductive Token
  | Whitespace
  | ParenOpen
  | ParenClose
  | Text (text: String)
deriving Repr

def new_token (character: Character): Token :=
  match character with
  | Character.Whitespace => Token.Whitespace
  | Character.ParenOpen => Token.ParenOpen
  | Character.ParenClose => Token.ParenClose
  | Character.Other c => Token.Text (String.singleton c)

structure Lexer where
  current: Option Token
  tokens: (List Token)

def lex_init: Lexer := { tokens := List.nil, current := none }

def lex_classify (char: Char) : Character :=
  match char with
    | '(' => Character.ParenOpen
    | ')' => Character.ParenClose
    | ' ' | '\n'  => Character.Whitespace
    | _ => Character.Other char


def lex_update (current: Option Token) (next: Character) : (Option Token) × (Option Token) :=
  match current,next with
    | some (Token.Text text), Character.Other next_char => (none, Token.Text (String.push text next_char))
    | current, Character.Whitespace => (current, none)
    | some (Token.Text text), _  => (some (Token.Text text), new_token next)
    | current,next => (current, new_token next)

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
