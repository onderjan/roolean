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
  | Letter (c: Char)
  | Digit (digit: Fin 10)
  | SymbolSpecial (c: Char)
  -- TODO
  | Other (c: Char)
deriving Repr

inductive Token
  | ParenOpen
  | ParenClose
  | Numeral (num: Nat)
  | Text (text: String)
deriving Repr


inductive ELexerLocation where
  | Basic
  | SymbolEnd
deriving Repr

structure ELexer where
  location: ELexerLocation
  char: Char
  remaining: List Char
  tokens: List Token
deriving Repr

def lex_classify (char: Char) : Character :=
  if char >= '0' && char <= '9' then
    let value := (Char.toNat char) - (Char.toNat '0')
    Character.Digit ((Fin.ofNat 10) value)
  else if (char >= 'a' && char <= 'z')
    || (char >= 'A' && char <= 'Z') then
    Character.Letter char
  else match char with
    | '\t' | ' '  => Character.TabSpace
    | '\r' | '\n'  => Character.LineBreak
    | ';' => Character.Semicolon
    | '(' => Character.ParenOpen
    | ')' => Character.ParenClose
    | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_'
    | '-' | '+' | '=' | '<' | '>' | '.' | '?' | '/' => Character.SymbolSpecial char
    | _ => Character.Other char

structure Lexer where
  tokens: List Token

def add_token(lexer: Lexer) (token: Token): Lexer :=
{ tokens := (List.cons (token) lexer.tokens) }

def lex_symbol (list: List Char) (string: String): Except Unit (List Char × Token) :=
  match list with
    | [] => pure ([], Token.Text string)
    | char :: tail =>
      match lex_classify char with
        | Character.Letter char | Character.SymbolSpecial char =>
          lex_symbol tail (String.push string char)
        | Character.Digit digit =>
          let char := Char.ofNat (Char.toNat '0' + Fin.toNat digit)
          lex_symbol tail (String.push string char)
        | Character.ParenOpen | Character.ParenClose
        | Character.TabSpace | Character.LineBreak => pure (list, Token.Text string)
        | _ => Except.error ()

def lex_digit (list: List Char) (num: Nat): Except Unit (List Char × Token) :=
  match list with
    | [] => pure ([], Token.Numeral num)
    | char :: tail =>
      match lex_classify char with
        | Character.Digit digit =>
          let num := num * 10 + digit
          lex_digit tail num
        | Character.ParenOpen | Character.ParenClose
        | Character.TabSpace | Character.LineBreak => pure (list, Token.Numeral num)
        | _ => Except.error ()

def lex_comment (list: List Char): List Char :=
  match list with
    | [] => []
    | char :: tail =>
      match lex_classify char with
        | Character.LineBreak => tail
        | _ => lex_comment tail

-- TODO termination proof
partial def lex_rec (list: List Char) (tokens: List Token): Except ELexer (List Token) :=
  match list with
    | [] => pure tokens
    | char :: tail =>
      match lex_classify char with
      | Character.Letter char | Character.SymbolSpecial char =>
         match lex_symbol tail (String.singleton char) with
         | Except.ok (tail, token) => lex_rec tail (token :: tokens)
         | Except.error () =>
            Except.error { location := ELexerLocation.SymbolEnd, remaining := tail, tokens, char }
      | Character.Digit digit =>
         match lex_digit tail digit with
         | Except.ok (tail, token) => lex_rec tail (token :: tokens)
         | Except.error () =>
            Except.error { location := ELexerLocation.SymbolEnd, remaining := tail, tokens, char }
      | Character.ParenOpen => lex_rec tail (Token.ParenOpen :: tokens)
      | Character.ParenClose => lex_rec tail (Token.ParenClose :: tokens)
      | Character.Semicolon =>
          let tail := lex_comment tail
          lex_rec tail tokens
      | Character.TabSpace | Character.LineBreak => lex_rec tail tokens
      | _ => Except.error { location := ELexerLocation.Basic, remaining := tail, tokens, char }

def lex (list: List Char): Except ELexer (List Token) := do
  (lex_rec list List.nil).map List.reverse

def process: IO (Except ELexer (List Token)) := do
  let string ← IO.FS.readFile "benchmarks/addsub.smt2"
  IO.println s!"Read:\n---\n{string}\n---\n"
  let chars := Std.Iter.toList (String.chars string)
  let lexed := lex chars
  pure lexed

def main : IO Unit := do
  let _discard ← process

 -- #eval lex (['a', 'b'])

 #eval process
