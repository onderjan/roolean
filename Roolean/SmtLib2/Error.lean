module

public structure Location where
  line: Nat
  column: Nat
deriving Repr

public inductive LexerError
  | FileOpen
  | FileRead
  | FractionDigitExpected
  | HexadecimalDigitExpected
  | BinaryDigitExpected
  | BaseSelectionExpected
  | UnclosedStringLiteral
  | ForbiddenCharInString
  | UnclosedQuotedSymbol
  | BackslashInQuotedSymbol
  | ForbiddenCharInQuotedSymbol
  | KeywordNameExpected
  | KeywordReserved
  | UnexpectedCharacter
deriving Repr

public structure ELexer where
  type: LexerError
deriving Repr
