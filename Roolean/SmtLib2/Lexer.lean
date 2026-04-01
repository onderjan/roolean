module

import Roolean.SmtLib2.CharClass
public import Roolean.SmtLib2.String8
public import Roolean.SmtLib2.Reserved
public import Roolean.SmtLib2.Error
import Roolean.SmtLib2.CharClass
import Roolean.SmtLib2.CharClass

public inductive Token
  | ParenOpen
  | ParenClose
  | Numeral (value: Nat) (numDigits: Nat)
  | Decimal (value: Nat) (numNumeratorDigits: Nat) (numDenominatorDigits: Nat)
  | Hexadecimal (value: Nat) (numDigits: Nat)
  | Binary (value: Nat) (numDigits: Nat)
  | Symbol (name: String8)
  | Reserved (value: Reserved)
  | String (literal: String8)
  | Keyword (name: String8)
  | End
deriving Repr, Nonempty

public inductive LexerState
  | Normal
  | Fraction (value: Nat) (numNumeratorDigits: Nat) (numDenominatorDigits: Nat)
  | NumeralOrDecimal (value: Nat) (numDigits: Nat)
  | Hexadecimal (value: Nat) (numDigits: Nat)
  | Binary (value: Nat) (numDigits: Nat)
  | HexadecimalOrBinary
  | StringLiteral (literal: String8)
  | StringLiteralDoubleQuote (literal: String8)
  | SimpleSymbol (name: String8)
  | Keyword (name: String8)
  | QuotedSymbol (name: String8)
  | Comment

public structure LexerVars where
  tokens: Array Token

def LexerVars.pushToken (vars: LexerVars) (token: Token) : LexerVars :=
  { tokens := vars.tokens.push token }

structure LexerDuo where
  state: LexerState
  vars: LexerVars

def LexerState.Normal.lex (vars: LexerVars) (c: Option CharClass): Except ELexer LexerDuo := do
  let (state, vars) ← match c with
    -- end without problems on EOF
    | none => pure (LexerState.Normal, vars)

    -- whitespace, just continue lexing
    | some (CharClass.Tab) | some (CharClass.Space)
    | some (CharClass.LineBreak _) => pure (LexerState.Normal, vars)

    -- parentheses are tokens of their own
    | some (CharClass.ParenOpen) =>
      pure (LexerState.Normal, (vars.pushToken Token.ParenOpen))
    | some (CharClass.ParenClose) =>
      pure (LexerState.Normal, (vars.pushToken Token.ParenClose))

    -- semicolon starts a comment
    | some (CharClass.Semicolon) =>
      pure (LexerState.Comment, vars)

    | some (CharClass.Digit c) =>
      -- digit starts a numeral or a decimal
      -- and determines the first digit value
      let digit := (c.toNat) - ('0'.toNat)
      pure ((LexerState.NumeralOrDecimal digit 1), vars)

    | some (CharClass.Hash) => do
      -- hash starts a hexadecimal or a binary
      pure (LexerState.HexadecimalOrBinary, vars)

    | some (CharClass.DoubleQuote) => do
      -- double quote starts a string literal
      pure (LexerState.StringLiteral String8.empty, vars)

    | some (CharClass.Colon) =>
      -- colon starts a keyword, which continues with a simple symbol string
      pure (LexerState.Keyword String8.empty, vars)

    | some (CharClass.Letter c) | some (CharClass.Special c) =>
      -- letter or special starts a simple symbol or a reserved word
      -- the reserved words will be handled after the name is fully known
      pure (LexerState.SimpleSymbol (String8.singleton c), vars)

    | some (CharClass.Pipe) => do
      -- quoted symbol
      pure (LexerState.QuotedSymbol String8.empty, vars)

      -- class disallowed here
    | _ => Except.error (ELexer.mk LexerError.UnexpectedCharacter)

  pure (LexerDuo.mk state vars)


def LexerState.Fraction.lex (vars: LexerVars) (c: Option CharClass)
  (value: Nat) (numNumeratorDigits: Nat) (numDenominatorDigits: Nat): Except ELexer LexerDuo :=
  if let some digit := c >>= CharClass.toDecimal? then
    -- compute the new value, add one denominator digit
    let value := (value * 10 + digit)
    let state := LexerState.Fraction value numNumeratorDigits (numDenominatorDigits + 1)
    pure (LexerDuo.mk state vars)
  else if numDenominatorDigits == 0 then
    -- decimals of the form 7. without any digit in fraction part are disallowed
    Except.error (ELexer.mk LexerError.FractionDigitExpected)
  else
    -- push new token and lex the new character as token
    let token := Token.Decimal value numNumeratorDigits numDenominatorDigits
    LexerState.Normal.lex (vars.pushToken token) c

def LexerState.NumeralOrDecimal.lex (vars: LexerVars) (c: Option CharClass)
  (value: Nat) (numDigits: Nat): Except ELexer LexerDuo :=
  match c with
    | some (CharClass.Digit c) =>
      -- compute the new value, add one digit
      let digit := (c.toNat) - ('0'.toNat)
      let value := (value * 10 + digit)
      let state := LexerState.NumeralOrDecimal value (numDigits + 1)
      pure (LexerDuo.mk state vars)

    | some (CharClass.Dot) =>
      -- decimal, the next character will start fraction
      let state := LexerState.Fraction value numDigits 0
      pure (LexerDuo.mk state vars)

    | _ =>
      -- this was a numeral
      -- push new token and lex the new character as token
      let token := Token.Numeral value numDigits
      LexerState.Normal.lex (vars.pushToken token) c

def LexerState.Hexadecimal.lex (vars: LexerVars) (c: Option CharClass)
  (value: Nat) (numDigits: Nat): Except ELexer LexerDuo :=
  if let some digit := c >>= CharClass.toHexadecimal? then
    -- hexadecimal digit, multiply value by 16 and add it, increment num digits
    let value := (value * 16 + digit)
    let state := LexerState.Hexadecimal value (numDigits + 1)
    pure (LexerDuo.mk state vars)
  else if numDigits > 0 then
    -- had non-digit, nonzero digits
    -- push new token and lex the new character as token
    let token := Token.Hexadecimal value numDigits
    LexerState.Normal.lex (vars.pushToken token) c
  else
    -- had non-digit, zero digits disallowed
    Except.error (ELexer.mk LexerError.HexadecimalDigitExpected)

def LexerState.Binary.lex (vars: LexerVars) (c: Option CharClass)
  (value: Nat) (numDigits: Nat): Except ELexer LexerDuo :=
  if let some digit := c >>= CharClass.toBinary? then
    -- hexadecimal digit, multiply value by 2 and add it, increment num digits
    let value := (value * 2 + digit)
    let state := LexerState.Binary value (numDigits + 1)
    pure (LexerDuo.mk state vars)
  else if numDigits > 0 then
    -- had non-digit, nonzero digits
    -- push new token and lex the new character as token
    let token := Token.Binary value numDigits
    LexerState.Normal.lex (vars.pushToken token) c
  else
    -- had non-digit, zero digits disallowed
    Except.error (ELexer.mk LexerError.BinaryDigitExpected)

def LexerState.HexadecimalOrBinary.lex (vars: LexerVars) (c: Option CharClass): Except ELexer LexerDuo :=
  -- decide whether to lex hexadecimal or binary from the next character
  match c with
    | some (CharClass.Letter c) =>
      if c == 'x'.toUInt8 then
        pure (LexerDuo.mk (LexerState.Hexadecimal 0 0) vars)
      else if c == 'b'.toUInt8 then
        pure (LexerDuo.mk (LexerState.Binary 0 0) vars)
      else Except.error (ELexer.mk LexerError.BaseSelectionExpected)
    | _ => Except.error (ELexer.mk LexerError.BaseSelectionExpected)

def LexerState.StringLiteral.lex (vars: LexerVars) (c: Option CharClass) (literal: String8)
  : Except ELexer LexerDuo :=
  match c with
    | none =>
      -- forbidden as the literal must be totally enclosed by double quotes
      Except.error (ELexer.mk LexerError.UnclosedStringLiteral)
    | some (CharClass.DoubleQuote) =>
      -- we have a double quote in string literal
      -- it may be followed by another double quote for escaping
      -- otherwise, it will end the string literal
      -- put the LexerDuo in a special state to handle the next character
        pure (LexerDuo.mk (LexerState.StringLiteralDoubleQuote literal) vars)
    | some (c) =>
      if c.isPrintableOrWhitespace then
        -- add to literal
        let state := LexerState.StringLiteral (literal.push c.toChar8)
        pure (LexerDuo.mk state vars)
      else
        -- forbidden as not printable or whitespace
        Except.error (ELexer.mk LexerError.ForbiddenCharInString)

def LexerState.StringLiteralDoubleQuote.lex (vars: LexerVars) (c: Option CharClass) (literal: String8)
  : Except ELexer LexerDuo :=
  match c with
    | some (CharClass.DoubleQuote) =>
      -- this has been a double-quote escape
      -- push a double-quote and continue lexing the string literal
        let state := LexerState.StringLiteral (literal.push CharClass.DoubleQuote.toChar8)
        pure (LexerDuo.mk state vars)
    | _ =>
      -- literal has ended by the previous character
      -- push new token and lex the new character as token
      let token := Token.String literal
      LexerState.Normal.lex (vars.pushToken token) c

def simpleSymbolChar(c: Option CharClass) : Option Char8 :=
  match c with
    | some (CharClass.Letter c) | some (CharClass.Digit c)
    | some (CharClass.Special c) => some c
    | some (CharClass.Dot) => some CharClass.Dot.toChar8
    | _ => none

def LexerState.SimpleSymbol.lex (vars: LexerVars) (c: Option CharClass) (name: String8)
  : Except ELexer LexerDuo := do
  if let some c := simpleSymbolChar c then
    -- push character to the symbol name
    pure (LexerDuo.mk (LexerState.SimpleSymbol (name.push c)) vars)
  else
    -- simple symbol ended with previous character
    -- process reserved words
    let token := if let some reserved := Reserved.ofString8? name then
      -- reserved words are prohibited here
      Token.Reserved reserved
    else
      Token.Symbol name

    -- push new token and lex the new character as token
    LexerState.Normal.lex (vars.pushToken token) c

def LexerState.Keyword.lex (vars: LexerVars) (c: Option CharClass) (name: String8) : Except ELexer LexerDuo :=
  if let some c := simpleSymbolChar c then
    -- push character to the symbol name
    pure (LexerDuo.mk (LexerState.Keyword (name.push c)) vars)
  else
    -- keyword ended with previous character
    if name.isEmpty then
      -- empty keyword is prohibited
      Except.error (ELexer.mk LexerError.KeywordNameExpected)
    else if let some _reserved := Reserved.ofString8? name then
      Except.error (ELexer.mk LexerError.KeywordReserved)
    else
      -- push new token and lex the new character as token
      let token := Token.Keyword name
      LexerState.Normal.lex (vars.pushToken token) c


def LexerState.QuotedSymbol.lex (vars: LexerVars) (c: Option CharClass) (name: String8)
  : Except ELexer LexerDuo :=
  match c with
    | some (CharClass.Backslash) =>
      -- backslash forbidden in quoted symbols
      Except.error (ELexer.mk LexerError.BackslashInQuotedSymbol)

    | some (CharClass.Pipe) =>
      -- end of quoted symbol, push its token, continue normally with next character
      pure (LexerDuo.mk LexerState.Normal vars)

    | some (c) =>
      if c.isPrintableOrWhitespace then
        -- add the character to the quoted symbol and continue it
        pure (LexerDuo.mk (LexerState.QuotedSymbol (name.push c.toChar8)) vars)
      else
        -- character forbidden as not printable or whitespace
        Except.error (ELexer.mk LexerError.ForbiddenCharInQuotedSymbol)

    | none =>
      -- EOF forbidden as the symbol must be totally enclosed by pipes
      Except.error (ELexer.mk LexerError.UnclosedQuotedSymbol)

def LexerState.Comment.lex (vars: LexerVars) (c: Option CharClass) : Except ELexer LexerDuo :=
  match c with
    | some (CharClass.LineBreak _) =>
      -- end comment, ready for next token
      pure (LexerDuo.mk LexerState.Normal vars)
    | _ =>
      -- continue comment, no problem ending file on a comment
      pure (LexerDuo.mk LexerState.Comment vars)


def LexerState.lexChar (state: LexerState) (c: Option CharClass) : Except ELexer LexerDuo :=
  let vars := { tokens := #[] }
  match state with
    | .Normal => LexerState.Normal.lex vars c
    | .Fraction value numNumeratorDigits numDenominatorDigits =>
        LexerState.Fraction.lex vars c value numNumeratorDigits numDenominatorDigits
    | .NumeralOrDecimal value numDigits =>
        LexerState.NumeralOrDecimal.lex vars c value numDigits
    | .Hexadecimal value numDigits =>
        LexerState.Hexadecimal.lex vars c value numDigits
    | .Binary value numDigits =>
        LexerState.Binary.lex vars c value numDigits
    | .HexadecimalOrBinary =>
        LexerState.HexadecimalOrBinary.lex vars c
    | .StringLiteral literal =>
        LexerState.StringLiteral.lex vars c literal
    | .StringLiteralDoubleQuote literal =>
        LexerState.StringLiteralDoubleQuote.lex vars c literal
    | .SimpleSymbol name =>
        LexerState.SimpleSymbol.lex vars c name
    | .Keyword name =>
        LexerState.Keyword.lex vars c name
    | .QuotedSymbol name =>
        LexerState.QuotedSymbol.lex vars c name
    | .Comment => LexerState.Comment.lex vars c


public structure Lexer where
  private tokens: List Token
  private state: LexerState
  private handle: Option IO.FS.Handle
  private buffer: ByteArray
  private ix: Nat

def Lexer.tryNext (lexer: Lexer) : EIO ELexer (Lexer × Option Token) := do
  -- if we have a token available, return it
  if let token :: tokens := lexer.tokens then
      return ({lexer with tokens}, some token)

  -- if we have reached the end previously, keep returning end
  let handle ← if let some handle := lexer.handle then
    pure handle
  else
    return (lexer, some Token.End)

  let mut ix := lexer.ix
  let mut buffer := lexer.buffer

  if ix ≥ buffer.size then
    -- the index does not fit, fill the buffer again and set index to zero
    buffer ← (IO.FS.Handle.read handle 1024).toEIO (λ _ => ELexer.mk LexerError.FileRead)
    ix := 0

  if h: ix < buffer.size then
    -- process character
    let c := buffer[ix]
    let charClass := CharClass.ofChar8 c
    let duo ← EIO.ofExcept (lexer.state.lexChar (some charClass))
    let (token, tokens) := match duo.vars.tokens.toList with
      | token :: tokens => (some token, tokens)
      | [] => (none, [])

    let lexer := { tokens, state := duo.state, handle := some handle, buffer, ix := ix + 1 }
    pure (lexer, token)

  else
  -- the buffer is still empty, we have reached the end
  -- process none and drop the handle
    let duo ← EIO.ofExcept (lexer.state.lexChar none)
    let (token, tokens) := match duo.vars.tokens.toList with
      | token :: tokens => (some token, tokens)
      | [] => (none, [])

    let lexer := { tokens, state := duo.state, handle := none, buffer, ix := ix + 1 }
    pure (lexer, token)



public def lex (filename: String): EIO ELexer (Array Token) := do
  let handle ← (IO.FS.Handle.mk filename IO.FS.Mode.read).toEIO (λ _ => ELexer.mk LexerError.FileOpen)

  let mut lexer: Lexer := { tokens := [], state := LexerState.Normal, handle, buffer := ByteArray.empty, ix := 0 }

  let mut tokens := #[]

  repeat
    let (nextLexer, next) ← lexer.tryNext
    lexer := nextLexer
    match next with
    | some Token.End => break
    | some token => tokens := tokens.push token
    | none => pure ()

  pure tokens
