module

import RooleCheck.Parser.Classifier

public inductive Reserved
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

public inductive Token
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

-- no error information for simplicity
public structure ELexer
deriving Repr

def lexFraction (chars: List Char) (numer: Nat) (minus_log_10: Nat): List Char × Token :=
  -- technically, SMT-LIB2 allows decimals such as 7.0 and 7.0000,
  -- but does not have a rule for decimals of form 7. without trailing zero
  -- we we will accept this form too to avoid an error condition
  match chars with
    | [] => ([], Token.Decimal numer minus_log_10)
    | c :: chars =>
      match classify c with
        | CharClass.Digit c =>
          let digit := (Char.toNat c) - (Char.toNat '0')
          lexFraction chars (numer * 10 + digit) (minus_log_10 + 1)
        | _ => (chars, Token.Decimal numer minus_log_10)


def lexNumeralOrDecimal (chars: List Char) (num: Nat): List Char × Token :=
  match chars with
    | [] => ([], Token.Numeral num)
    | c :: chars =>
      match classify c with
        | CharClass.Digit c =>
          let digit := (Char.toNat c) - (Char.toNat '0')
          lexNumeralOrDecimal chars (num * 10 + digit)
        | CharClass.Dot =>
          -- decimal, lex fraction, initially with unit multiplicand (0 in minus log10)
          lexFraction chars num 0
        | _ => (chars, Token.Numeral num)

def toHexadecimal (c: Char): Option Nat :=
  if c >= '0' && c <= '9' then
    some ((Char.toNat c) - (Char.toNat '0'))
  else if c >= 'a' && c <= 'f' then
    some (10 + (Char.toNat c) - (Char.toNat 'a'))
  else if c >= 'A' && c <= 'F' then
    some (10 + (Char.toNat c) - (Char.toNat 'A'))
  else
    none

def lexHexadecimal (chars: List Char) (num: Nat): List Char × Token :=
  match chars with
    | [] => ([], Token.Hexadecimal num)
    | c :: chars =>
      if let some digit := toHexadecimal c then
        lexHexadecimal chars (num * 16 + digit)
      else
        (chars, Token.Hexadecimal num)

def toBinary (c: Char): Option Nat :=
  if c >= '0' && c <= '1' then
    some ((Char.toNat c) - (Char.toNat '0'))
  else
    none

def lexBinary (chars: List Char) (num: Nat): List Char × Token :=
  match chars with
    | [] => ([], Token.Binary num)
    | c :: chars =>
      if let some digit := toHexadecimal c then
        lexBinary chars (num * 2 + digit)
      else
        (chars, Token.Binary num)

def lexStringLiteral (chars: List Char) (literal: String): Except ELexer (List Char × Token) :=
  match chars with
    | [] => Except.error {} -- forbidden as the literal must be totally enclosed by double quotes
    | c :: chars =>
      let classified := classify c
      match classified with
        | CharClass.DoubleQuote =>
          -- look ahead to the next character
          match chars with
            | '"' :: nextTail => lexStringLiteral nextTail (literal.push '"') -- double quote escape
            | _ => pure (chars, Token.String literal) -- end of string literal
        | _ => if isPrintableOrWhitespace classified then
            lexStringLiteral chars (literal.push c)
          else
            Except.error {} -- forbidden as not printable or whitespace


def lexSimpleSymbolString (chars: List Char) (name: String): List Char × String :=
  match chars with
    | [] => ([], name)
    | c :: chars =>
      match classify c with
        | CharClass.Letter char | CharClass.Digit char | CharClass.Special char =>
          lexSimpleSymbolString chars (String.push name char)
        | CharClass.Dot =>
          lexSimpleSymbolString chars (String.push name '.')
        | _ => (chars, name)

def lexSimpleSymbolOrReserved (chars: List Char) (name: String): List Char × Token :=
  let (chars, name) := lexSimpleSymbolString chars name
  -- process reserved words
  let token := match name with
    | "BINARY" => Token.Reserved Reserved.Binary
    | "DECIMAL" => Token.Reserved Reserved.Decimal
    | "HEXADECIMAL" => Token.Reserved Reserved.Hexadecimal
    | "NUMERAL" => Token.Reserved Reserved.Numeral
    | "STRING" => Token.Reserved Reserved.String
    | "_" => Token.Reserved Reserved.Underscore
    | "!" => Token.Reserved Reserved.ExclamationMark
    | "as" => Token.Reserved Reserved.As
    | "lambda" => Token.Reserved Reserved.Lambda
    | "let" => Token.Reserved Reserved.Let
    | "exists" => Token.Reserved Reserved.Exists
    | "forall" => Token.Reserved Reserved.Forall
    | "match" => Token.Reserved Reserved.Match
    | "par" => Token.Reserved Reserved.Par
    | _ => Token.Symbol name
  (chars, token)

def lexQuotedSymbol (chars: List Char) (name: String): Except ELexer (List Char × String) :=
  match chars with
    | [] => Except.error {} -- forbidden as the symbol must be totally enclosed by pipes
    | c :: chars =>
      let classified := classify c
      match classified with
        | CharClass.Backslash => Except.error {} -- backslash forbidden in quoted symbols
        | CharClass.Pipe => pure (chars, name) -- end quoted symbol
        | _ => if isPrintableOrWhitespace classified then
            lexQuotedSymbol chars (name.push c)
          else
            Except.error {} -- forbidden as not printable or whitespace


def lexComment (chars: List Char): List Char :=
  match chars with
    | [] => []
    | c :: chars =>
      match classify c with
        | CharClass.LineBreak => chars
        | _ => lexComment chars

-- TODO termination proof
partial def lexRec (chars: List Char) (tokens: Array Token): Except ELexer (Array Token) :=
  match chars with
    | [] => pure tokens
    | c :: chars =>
      match classify c with
      | CharClass.Tab | CharClass.Space | CharClass.LineBreak =>
        -- whitespace, just continue parsing
        lexRec chars tokens

      -- parentheses are tokens of their own
      | CharClass.ParenOpen => lexRec chars (tokens.push Token.ParenOpen)
      | CharClass.ParenClose => lexRec chars (tokens.push Token.ParenClose)

      | CharClass.Semicolon =>
          -- semicolon starts a comment
          lexRec (lexComment chars) tokens

      | CharClass.Digit c =>
        -- digit starts a numeral or a decimal
        let digit := (Char.toNat c) - (Char.toNat '0')
        let (chars, token) := lexNumeralOrDecimal chars digit
        lexRec chars (tokens.push token)

      | CharClass.Hash =>
        -- decide whether to lex hexadecimal or binary with the next character
        match chars with
          | 'x' :: first :: chars =>
            if let some first := toHexadecimal first then
              let (chars, token) := lexHexadecimal chars first
              lexRec chars (tokens.push token)
            else
              Except.error {}
          | 'b' :: first :: chars =>
            if let some first := toBinary first then
              let (chars, token) := lexBinary chars first
              lexRec chars  (tokens.push token)
            else
              Except.error {}
          | _ => Except.error {}

      | CharClass.DoubleQuote => do
        -- double quote starts a string literal
        let (chars, token) ← lexStringLiteral chars ""
        lexRec chars (tokens.push token)

      | CharClass.Colon =>
        -- colon starts a keyword, which continues with a simple symbol string
        let (chars, name) := lexSimpleSymbolString chars ""
        if name.isEmpty then
          Except.error {} -- empty continuation is disallowed
        else
          lexRec chars (tokens.push (Token.Keyword name))

      | CharClass.Letter c | CharClass.Special c =>
        -- letter or special starts a symbol or a reserved word
        let (chars, token) := lexSimpleSymbolOrReserved chars (String.singleton c)
        lexRec chars (tokens.push (token))

      | CharClass.Pipe => do
        -- quoted symbol
        let (chars, token) ← lexQuotedSymbol chars ""
        lexRec chars (tokens.push (Token.Symbol token))

        -- class disallowed here
      | _ => Except.error {}

public def lex (chars: List Char): Except ELexer (Array Token) := do
  lexRec chars #[]
