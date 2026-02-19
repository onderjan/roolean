import RooleCheck.Parser.Classifier

inductive Token
  | ParenOpen
  | ParenClose
  | Numeral (num: Nat)
  -- Decimals are represented as fractions.
  | Decimal (numer: Nat) (denom: Nat)
  -- TODO hexadecimal, binary, string, reserved, symbol, keyword
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

structure Lexer where
  tokens: List Token

def addToken(lexer: Lexer) (token: Token): Lexer :=
{ tokens := (List.cons (token) lexer.tokens) }

def lexSymbol (list: List Char) (string: String): List Char × Token :=
  match list with
    | [] => ([], Token.Text string)
    | char :: tail =>
      match charClass char with
        | CharClass.Letter char | CharClass.Digit char | CharClass.Special char =>
          lexSymbol tail (String.push string char)
        | CharClass.Dot =>
          lexSymbol tail (String.push string '.')
        | _ => (list, Token.Text string)

def lexFraction (list: List Char) (numer: Nat) (denom: Nat): List Char × Token :=
  -- technically, SMT-LIB2 allows decimals such as 7.0 and 7.0000,
  -- but does not have a rule for decimals of form 7. without trailing zero
  -- we we will accept this form too to avoid an error condition
  match list with
    | [] => ([], Token.Decimal numer denom)
    | char :: tail =>
      match charClass char with
        | CharClass.Digit c =>
          let digit := (Char.toNat c) - (Char.toNat '0')
          lexFraction tail (numer * 10 + digit) (denom * 10)
        | _ => (list, Token.Decimal numer denom)


def lexNumeralOrDecimal (list: List Char) (num: Nat): List Char × Token :=
  match list with
    | [] => ([], Token.Numeral num)
    | char :: tail =>
      match charClass char with
        | CharClass.Digit c =>
          let digit := (Char.toNat c) - (Char.toNat '0')
          lexNumeralOrDecimal tail (num * 10 + digit)
        | CharClass.Dot =>
          -- decimal, lex fraction, initially with numerator 1
          lexFraction tail num 1
        | _ => (list, Token.Numeral num)

def lexComment (list: List Char): List Char :=
  match list with
    | [] => []
    | char :: tail =>
      match charClass char with
        | CharClass.LineBreak => tail
        | _ => lexComment tail

-- TODO termination proof
partial def lexRec (list: List Char) (tokens: List Token): Except ELexer (List Token) :=
  match list with
    | [] => pure tokens
    | char :: tail =>
      match charClass char with
      | CharClass.Tab | CharClass.Space | CharClass.LineBreak =>
        -- whitespace, just continue parsing
        lexRec tail tokens
      | CharClass.Letter c | CharClass.Special c =>
        -- letter or special starts a symbol
        let (tail, token) := lexSymbol tail (String.singleton c)
        lexRec tail (token :: tokens)
      | CharClass.Digit c =>
        -- digit starts a numeral or a decimal
        let digit := (Char.toNat c) - (Char.toNat '0')
        let (tail, token) := lexNumeralOrDecimal tail digit
        lexRec tail (token :: tokens)
      | CharClass.ParenOpen => lexRec tail (Token.ParenOpen :: tokens)
      | CharClass.ParenClose => lexRec tail (Token.ParenClose :: tokens)
      | CharClass.Semicolon =>
          -- semicolon starts a comment
          let tail := lexComment tail
          lexRec tail tokens
      -- TODO quoted symbols (start with pipe), etc.
      | _ => Except.error { location := ELexerLocation.Basic, remaining := tail, tokens, char }

def lex (list: List Char): Except ELexer (List Token) := do
  (lexRec list List.nil).map List.reverse

def process: IO (Except ELexer (List Token)) := do
  let string ← IO.FS.readFile "benchmarks/lean.smt2"
  IO.println s!"Read:\n---\n{string}\n---\n"
  let chars := Std.Iter.toList (String.chars string)
  let lexed := lex chars
  pure lexed

def main : IO Unit := do
  let _discard ← process

 #eval process
