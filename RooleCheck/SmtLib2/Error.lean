module

public structure Location where
  line: Nat
  column: Nat
deriving Repr

public inductive LexerError
  | UnclosedStringLiteral
  | ForbiddenCharInString
  | UnclosedQuotedSymbol
  | BackslashInQuotedSymbol
  | ForbiddenCharInQuotedSymbol
  | HexadecimalDigitExpected
  | BinaryDigitExpected
  | BaseSelectionExpected
  | KeywordNameExpected
  | UnexpectedCharacter
deriving Repr

public structure ELexer where
  type: LexerError
deriving Repr
