import RooleCheck.Parser.Classifier

inductive Reserved
  | Binary
  | Decimal
  | Hexadecimal
  | Numeral
  | String
  | Underscore
  | ExclamationMark
  | As
  | Lambda
  | Let
  | Exists
  | Forall
  | Match
  | Par
deriving Repr

inductive Token
  | ParenOpen
  | ParenClose
  | Numeral (num: Nat)
  -- Decimals are represented with minus-log10 multiplicand.
  | Decimal (numer: Nat) (minus_log_10: Nat)
  | Hexadecimal (num: Nat)
  | Binary (num: Nat)
  | Symbol (name: String)
  | Reserved (value: Reserved)
  | String (literal: String)
  | Keyword (name: String)
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

def lexFraction (list: List Char) (numer: Nat) (minus_log_10: Nat): List Char × Token :=
  -- technically, SMT-LIB2 allows decimals such as 7.0 and 7.0000,
  -- but does not have a rule for decimals of form 7. without trailing zero
  -- we we will accept this form too to avoid an error condition
  match list with
    | [] => ([], Token.Decimal numer minus_log_10)
    | char :: tail =>
      match charClass char with
        | CharClass.Digit c =>
          let digit := (Char.toNat c) - (Char.toNat '0')
          lexFraction tail (numer * 10 + digit) (minus_log_10 + 1)
        | _ => (list, Token.Decimal numer minus_log_10)


def lexNumeralOrDecimal (list: List Char) (num: Nat): List Char × Token :=
  match list with
    | [] => ([], Token.Numeral num)
    | char :: tail =>
      match charClass char with
        | CharClass.Digit c =>
          let digit := (Char.toNat c) - (Char.toNat '0')
          lexNumeralOrDecimal tail (num * 10 + digit)
        | CharClass.Dot =>
          -- decimal, lex fraction, initially with unit multiplicand (0 in minus log10)
          lexFraction tail num 0
        | _ => (list, Token.Numeral num)

def toHexadecimal (c: Char): Option Nat :=
  if c >= '0' && c <= '9' then
    some ((Char.toNat c) - (Char.toNat '0'))
  else if c >= 'a' && c <= 'f' then
    some (10 + (Char.toNat c) - (Char.toNat 'a'))
  else if c >= 'A' && c <= 'F' then
    some (10 + (Char.toNat c) - (Char.toNat 'A'))
  else
    none

def lexHexadecimal (list: List Char) (num: Nat): List Char × Token :=
  match list with
    | [] => ([], Token.Hexadecimal num)
    | char :: tail =>
      if let some digit := toHexadecimal char then
        lexHexadecimal tail (num * 16 + digit)
      else
        (tail, Token.Hexadecimal num)

def toBinary (c: Char): Option Nat :=
  if c >= '0' && c <= '1' then
    some ((Char.toNat c) - (Char.toNat '0'))
  else
    none

def lexBinary (list: List Char) (num: Nat): List Char × Token :=
  match list with
    | [] => ([], Token.Binary num)
    | char :: tail =>
      if let some digit := toHexadecimal char then
        lexBinary tail (num * 2 + digit)
      else
        (tail, Token.Binary num)

def lexStringLiteral (list: List Char) (literal: String): Except Unit (List Char × Token) :=
  match list with
    | [] => Except.error () -- forbidden as the literal must be totally enclosed by double quotes
    | char :: tail =>
      let classified := charClass char
      match classified with
        | CharClass.DoubleQuote =>
          -- look ahead to the next character
          match tail with
            | '"' :: nextTail => lexStringLiteral nextTail (literal.push '"') -- double quote escape
            | _ => pure (tail, Token.String literal) -- end of string literal
        | _ => if isPrintableOrWhitespace classified then
            lexStringLiteral tail (literal.push char)
          else
            Except.error () -- forbidden as not printable or whitespace


def lexSimpleSymbolString (list: List Char) (name: String): List Char × String :=
  match list with
    | [] => ([], name)
    | char :: tail =>
      match charClass char with
        | CharClass.Letter char | CharClass.Digit char | CharClass.Special char =>
          lexSimpleSymbolString tail (String.push name char)
        | CharClass.Dot =>
          lexSimpleSymbolString tail (String.push name '.')
        | _ => (list, name)

def lexSimpleSymbolOrReserved (list: List Char) (name: String): List Char × Token :=
  let (tail, name) := lexSimpleSymbolString list name
  -- process reserved words
  let token := match name with
    | "BINARY" => Token.Reserved Reserved.Binary
    | "DECIMAL" => Token.Reserved Reserved.Decimal
    | "HEXADECIMAL" => Token.Reserved Reserved.Hexadecimal
    | "NUMERAL" => Token.Reserved Reserved.Numeral
    | "STRING" => Token.Reserved Reserved.String
    | "!" => Token.Reserved Reserved.ExclamationMark
    | "as" => Token.Reserved Reserved.As
    | "lambda" => Token.Reserved Reserved.Lambda
    | "let" => Token.Reserved Reserved.Let
    | "exists" => Token.Reserved Reserved.Exists
    | "forall" => Token.Reserved Reserved.Forall
    | "match" => Token.Reserved Reserved.Match
    | "par" => Token.Reserved Reserved.Par
    | _ => Token.Symbol name
  (tail, token)

def lexQuotedSymbol (list: List Char) (name: String): Except Unit (List Char × String) :=
  match list with
    | [] => Except.error () -- forbidden as the symbol must be totally enclosed by pipes
    | char :: tail =>
      let classified := charClass char
      match classified with
        | CharClass.Backslash => Except.error () -- backslash forbidden in quoted symbols
        | CharClass.Pipe => pure (tail, name) -- end quoted symbol
        | _ => if isPrintableOrWhitespace classified then
            lexQuotedSymbol tail (name.push char)
          else
            Except.error () -- forbidden as not printable or whitespace


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
      | CharClass.ParenOpen => lexRec tail (Token.ParenOpen :: tokens)
      | CharClass.ParenClose => lexRec tail (Token.ParenClose :: tokens)

      | CharClass.Semicolon =>
          -- semicolon starts a comment
          let tail := lexComment tail
          lexRec tail tokens

      | CharClass.Digit c =>
        -- digit starts a numeral or a decimal
        let digit := (Char.toNat c) - (Char.toNat '0')
        let (tail, token) := lexNumeralOrDecimal tail digit
        lexRec tail (token :: tokens)

      | CharClass.Hash =>
        -- decide whether to lex hexadecimal or binary with the next character
        match tail with
          | 'x' :: first :: tail =>
            if let some first := toHexadecimal first then
              let (tail, token) := lexHexadecimal tail first
              lexRec tail (token :: tokens)
            else
              Except.error { location := ELexerLocation.Basic, remaining := tail, tokens, char }
          | 'b' :: first :: tail =>
            if let some first := toBinary first then
              let (tail, token) := lexBinary tail first
              lexRec tail (token :: tokens)
            else
              Except.error { location := ELexerLocation.Basic, remaining := tail, tokens, char }
          | _ => Except.error { location := ELexerLocation.Basic, remaining := tail, tokens, char }

      | CharClass.DoubleQuote =>
        -- double quote starts a string literal
        match lexStringLiteral tail "" with
          | Except.ok (tail, token) => lexRec tail (token :: tokens)
          | Except.error () =>
              Except.error { location := ELexerLocation.Basic, remaining := tail, tokens, char }

      | CharClass.Colon =>
        -- colon starts a keyword, which continues with a simple symbol string
        let (tail, name) := lexSimpleSymbolString tail ""
        match name with
          | "" => -- empty continuation is disallowed
            Except.error { location := ELexerLocation.Basic, remaining := tail, tokens, char }
          | _ => lexRec tail ((Token.Keyword name) :: tokens)

      | CharClass.Letter c | CharClass.Special c =>
        -- letter or special starts a symbol or a reserved word
        let (tail, token) := lexSimpleSymbolOrReserved tail (String.singleton c)
        lexRec tail ((token) :: tokens)

      | CharClass.Pipe =>
        -- quoted symbol
        match lexQuotedSymbol tail "" with
          | Except.ok (tail, token) => lexRec tail ((Token.Symbol token) :: tokens)
          | Except.error () =>
              Except.error { location := ELexerLocation.Basic, remaining := tail, tokens, char }

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
