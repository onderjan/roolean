module

public import Roolean.SmtLib2.String8
public import Roolean.SmtLib2.Reserved
public import Roolean.SmtLib2.Error

import Roolean.SmtLib2.Lexer
public import Roolean.SmtLib2.Lexer

public inductive SmtIndex
  | Numeral (value: Nat) (length: Nat)
  | Symbol (name: String8)
deriving Repr

-- a simple ident has no indices
-- an indexed ident has at least one index
public structure SmtIdent where
  name: String8
  indices: Array SmtIndex
deriving Repr

public def SmtIdent.simple (name: String8) : SmtIdent := { name, indices := #[]}

public inductive SmtSpecialConstant
  | Numeral (value: Nat) (numDigits: Nat)
  | Decimal (value: Nat) (numNumeratorDigits: Nat) (numDenominatorDigits: Nat)
  | Hexadecimal (value: Nat) (numDigits: Nat)
  | Binary (value: Nat) (numDigits: Nat)
  | String (value: String8)
deriving Repr

public inductive SmtSExpr
  | SpecialConstant(value: SmtSpecialConstant)
  | Symbol (name: String8)
  | Reserved (value: Reserved)
  | Keyword (name: String8)
  | Exprs (exprs: Array SmtSExpr)
deriving Repr

public inductive SmtAttributeValue
  | SpecialConstant (value: SmtSpecialConstant)
  | Symbol (name: String8)
  | Exprs (exprs: Array SmtSExpr)
deriving Repr

public inductive SmtAttribute
  | Name (name: String8)
  | NameValue (name: String8) (value: SmtAttributeValue)
deriving Repr

public inductive SmtSort
  | Ident (ident: SmtIdent)
  -- sort applications not implemented
deriving Repr

public inductive SmtQualifiedIdent
  -- 'as' qualified idents not implemented
  | Ident (ident: SmtIdent)
deriving Repr

public inductive SmtTerm
  | SpecialConstant (constant: SmtSpecialConstant)
  | QualifiedIdent (qualified: SmtQualifiedIdent)
  -- there must be at least one term
  | Application (qualified: SmtQualifiedIdent) (terms: Array SmtTerm)
  -- there must be at least one binding
  | Let (bindings: Array (String8 × SmtTerm)) (term: SmtTerm)
  -- TODO let, lambda, forall, exists, match, !
deriving Repr

public inductive SmtCommand
  | SetLogic (logic: String8)
  | SetInfo (attr: SmtAttribute)
  | DeclareConst (name: String8) (sort: SmtSort)
  | Assert (term: SmtTerm)
  | CheckSat
  | Exit
deriving Repr

public inductive ParserError where
  | ExpectedParenOpen
  | ExpectedParenClose
  | ExpectedSymbol
  | ExpectedKeyword
  | EmptyIdentIndices
  | InvalidIdent
  | InvalidAttributeValue
  | EmptyApplication
  | EmptyLetBindings
  | ExpectedTerm
  | UnsupportedCommand

deriving Repr, Nonempty, Inhabited
deriving instance Nonempty for ParserError

public structure Parser where
  tokens: List Token
  initial: List Token
deriving Repr, Nonempty, Inhabited

public inductive EParser where
  | Lexer (err: ELexer)
  | Parser (err: ParserError) (parser: Parser)
deriving Repr, Nonempty, Inhabited

def Parser.error (parser: Parser) (err: ParserError) : EParser :=
  EParser.Parser err parser

def Parser.with (parser: Parser) (tokens: List Token) : Parser :=
  { tokens := tokens, initial := parser.initial }

def consumeParenOpen(parser: Parser): Except EParser (Parser) :=
  match parser.tokens with
  | Token.ParenOpen :: tokens => pure (parser.with tokens)
  | _ => Except.error (parser.error ParserError.ExpectedParenOpen)

def consumeParenClose(parser: Parser): Except EParser (Parser) :=
  match parser.tokens with
  | Token.ParenClose :: tokens => pure (parser.with tokens)
  | _ => Except.error (parser.error ParserError.ExpectedParenClose)

def consumeSymbol(parser: Parser): Except EParser (Parser × String8) :=
  match parser.tokens with
  | Token.Symbol name :: tokens => pure (parser.with tokens, name)
  | _ => Except.error (parser.error ParserError.ExpectedSymbol)

def consumeKeyword(parser: Parser): Except EParser (Parser × String8) :=
  match parser.tokens with
  | Token.Keyword name :: tokens => pure (parser.with tokens, name)
  | _ => Except.error (parser.error ParserError.ExpectedKeyword)

partial def parseIndices (parser: Parser) (indices: Array SmtIndex) : (Parser × Array SmtIndex) :=
  match parser.tokens with
    | Token.Numeral value length :: tokens => parseIndices (parser.with tokens) (indices.push (SmtIndex.Numeral value length))
    | Token.Symbol name :: tokens => parseIndices (parser.with tokens) (indices.push (SmtIndex.Symbol name))
    | _ => (parser, indices)

def parseIdent (parser: Parser) : Except EParser (Parser × SmtIdent) :=
  match parser.tokens with
  | Token.Symbol name :: tokens => pure ((parser.with tokens), (SmtIdent.simple name))
  | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: Token.Symbol name :: tokens => do
    -- indexed identifier, one or more indices
    let (tokens, indices) := parseIndices (parser.with tokens) #[]
    if indices.isEmpty then
      Except.error (parser.error ParserError.EmptyIdentIndices)
    else
      let tokens ← consumeParenClose tokens
      pure (tokens, SmtIdent.mk name indices)
  | _ => Except.error (parser.error ParserError.InvalidIdent)

def specialConstant? (token: Token) : Option SmtSpecialConstant :=
  match token with
    | Token.Numeral value numDigits => some (SmtSpecialConstant.Numeral value numDigits)
    | Token.Decimal value numNumeratorDigits numDenominatorDigits =>
      some (SmtSpecialConstant.Decimal value numNumeratorDigits numDenominatorDigits)
    | Token.Hexadecimal value numDigits => some (SmtSpecialConstant.Hexadecimal value numDigits)
    | Token.Binary value numDigits => some (SmtSpecialConstant.Binary value numDigits)
    | Token.String value => some (SmtSpecialConstant.String value)
    | _ => none

-- TODO prove termination
partial def parseSExprs (parser: Parser) (exprs: Array SmtSExpr) : Except EParser (Parser × (Array SmtSExpr)) :=
  match parser.tokens with
    | Token.Symbol name :: tokens => parseSExprs (parser.with tokens) (exprs.push (SmtSExpr.Symbol name))
    | Token.Reserved value :: tokens => parseSExprs (parser.with tokens) (exprs.push (SmtSExpr.Reserved value))
    | Token.Keyword keyword :: tokens => parseSExprs (parser.with tokens) (exprs.push (SmtSExpr.Keyword keyword))
    | Token.ParenOpen :: tokens => do
      let (parser, innerExprs) ← parseSExprs (parser.with tokens) #[]
      let parser ← consumeParenClose parser
      parseSExprs (parser.with tokens) (exprs.push (SmtSExpr.Exprs innerExprs))
    | token :: tokens =>
      if let some constant := specialConstant? token then
        parseSExprs (parser.with tokens) (exprs.push (SmtSExpr.SpecialConstant constant))
      else
        pure (parser, exprs)
    | [] => pure (parser, exprs)


def parseAttribute (parser: Parser) : Except EParser (Parser × SmtAttribute) := do
  let (parser, keyword) ← consumeKeyword parser

  let (parser, value) ← match parser.tokens with
    | Token.Symbol name :: tokens =>
      -- attribute value is a symbol
      let value := SmtAttributeValue.Symbol name
      pure (parser.with tokens, some value)
    | Token.ParenOpen :: tokens =>
      -- attribute value is an S-expression
      let (parser, exprs) ← parseSExprs (parser.with tokens) #[]
      let parser ← consumeParenClose parser
      let value := SmtAttributeValue.Exprs exprs
      pure (parser.with tokens, some value)
    | token :: tokens =>
      if let some constant := specialConstant? token then
        let value := SmtAttributeValue.SpecialConstant constant
        pure (parser.with tokens, some value)
      else
        pure (parser, none) -- attribute has no value
    | _ => pure (parser, none) -- attribute has no value

  if let some value := value then
    pure (parser, SmtAttribute.NameValue keyword value)
  else
    pure (parser, SmtAttribute.Name keyword)


-- TODO prove termination
mutual
partial def parseSortApplication (parser: Parser) (ident: SmtIdent) (sorts: Array SmtSort)
  : Except EParser (Parser × SmtSort)  := do
  -- only simple sorts implemented
    let (parser, sort) ← parseSort parser
    parseSortApplication parser ident (sorts.push sort)

partial def parseSort (parser: Parser) : Except EParser (Parser × SmtSort) := do
  match parser.tokens with
    | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: _ =>
      -- sort consists of an indexed ident
      let (parser, ident) ← parseIdent parser
      pure (parser, SmtSort.Ident ident)

    | Token.ParenOpen :: tokens =>
      -- sort consists of an application
      let (parser, ident) ← parseIdent (parser.with tokens)
      let (parser, sort) ← parseSortApplication parser ident #[]
      let parser ← consumeParenClose parser
      pure (parser, sort)
    | _ => -- sort consists of an ident
      let (parser, ident) ← parseIdent parser
      pure (parser, SmtSort.Ident ident)
end

def parseQualifiedIdent (parser: Parser) : Except EParser (Parser × SmtQualifiedIdent) := do
  -- TODO qualification
  let (parser, ident) ← parseIdent parser
  pure (parser, SmtQualifiedIdent.Ident ident)

-- TODO prove termination
mutual
partial def parseTermApplication (parser: Parser)
              (ident: SmtQualifiedIdent) (terms: Array SmtTerm): Except EParser (Parser × SmtTerm)  := do
  match parser.tokens with
    | Token.ParenClose :: tokens =>
      if terms.isEmpty then
        Except.error (parser.error ParserError.EmptyApplication)
      else
        pure ((parser.with tokens), SmtTerm.Application ident terms)
    | _ =>
      let (parser, term) ← parseTerm parser
      parseTermApplication parser ident (terms.push term)

partial def parseLetBindings (parser: Parser) (bindings: Array (String8 × SmtTerm))
  : Except EParser (Parser × Array (String8 × SmtTerm)) :=
  match parser.tokens with
    | Token.ParenOpen :: Token.Symbol name :: tokens => do
      let (tokens, term) ← parseTerm (parser.with tokens)
      let tokens ← consumeParenClose tokens
      parseLetBindings tokens (bindings.push (name, term))
    | _ => pure (parser, bindings)

partial def parseTerm (parser: Parser) : Except EParser (Parser × SmtTerm) := do
  match parser.tokens with
    | Token.Numeral value length :: tokens =>
      pure ((parser.with tokens), SmtTerm.SpecialConstant (SmtSpecialConstant.Numeral value length))
    | Token.Decimal value numeratorLength denominatorLength :: tokens =>
        pure ((parser.with tokens),
          SmtTerm.SpecialConstant (SmtSpecialConstant.Decimal value numeratorLength denominatorLength))
    | Token.Hexadecimal value length :: tokens =>
      pure ((parser.with tokens), SmtTerm.SpecialConstant (SmtSpecialConstant.Hexadecimal value length))
    | Token.Binary value length :: tokens =>
      pure ((parser.with tokens), SmtTerm.SpecialConstant (SmtSpecialConstant.Binary value length))
    | Token.String value :: tokens =>
      pure ((parser.with tokens), SmtTerm.SpecialConstant (SmtSpecialConstant.String value))

    | Token.Symbol _ :: _ =>
      -- normal identifier
      let (tokens, ident) ← parseIdent parser
      pure (tokens, SmtTerm.QualifiedIdent (SmtQualifiedIdent.Ident ident))

    | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: _ =>
      -- qualified identifier
      let (tokens, ident) ← parseIdent parser
      pure (tokens, SmtTerm.QualifiedIdent (SmtQualifiedIdent.Ident ident))

    | Token.ParenOpen :: Token.Reserved Reserved.Let :: Token.ParenOpen :: tokens =>
      -- let
      let (tokens, bindings) ← parseLetBindings (parser.with tokens) #[]
      if bindings.isEmpty then
        Except.error (parser.error ParserError.EmptyLetBindings)
      else
        let tokens ← consumeParenClose tokens
        let (tokens, term) ← parseTerm tokens
        let tokens ← consumeParenClose tokens
        pure (tokens, SmtTerm.Let bindings term)

    | Token.ParenOpen :: tokens =>
      -- application
      let (tokens, ident) ← parseQualifiedIdent (parser.with tokens)
      parseTermApplication tokens ident #[]

    -- unsupported: lambda, forall, exists, match, !

    | token :: tokens =>
      if let some constant := specialConstant? token then
        pure (parser.with tokens, SmtTerm.SpecialConstant constant)
      else
        Except.error (parser.error ParserError.ExpectedTerm)
    | _ => Except.error (parser.error ParserError.ExpectedTerm)
end

-- TODO prove termination
partial def parseCommands (parser: Parser) (commands: Array SmtCommand) : Except EParser (Array SmtCommand) := do
  if parser.tokens.isEmpty then
    return commands

  let parser ← consumeParenOpen parser
  let (parser, commandName) ← consumeSymbol parser

  let (parser, command) ← match commandName.toString? with
    | some "set-logic" =>
      let (parser, logic) ← consumeSymbol parser
      pure (parser, SmtCommand.SetLogic logic)

    | some "set-info" =>
      let (parser, attr) ← parseAttribute parser
      pure (parser, SmtCommand.SetInfo attr)

    | some "declare-fun" =>
      let (parser, name) ← consumeSymbol parser

      let parser ← consumeParenOpen parser
      -- TODO: support non-constant functions
      let parser ← consumeParenClose parser
      let (parser, sort) ← parseSort parser

      pure (parser, SmtCommand.DeclareConst name sort)

    | some "declare-const" =>
      let (parser, name) ← consumeSymbol parser
      let (parser, sort) ← parseSort parser
      pure (parser, SmtCommand.DeclareConst name sort)

    | some "assert" =>
      let (parser, term) ← parseTerm (parser.with parser.tokens)
      pure (parser, SmtCommand.Assert term)

    | some "check-sat" =>
      pure (parser, SmtCommand.CheckSat)

    | some "exit" =>
      pure (parser, SmtCommand.Exit)

    | _ => Except.error (parser.error ParserError.UnsupportedCommand)

    let parser ← consumeParenClose parser

    parseCommands (parser) (commands.push (command))


public def parse (filename: String): EIO EParser (Array SmtCommand) := do
  let tokens ← (lex filename).adapt (λ e => EParser.Lexer e)
  let tokens := tokens.toList
  let parser : Parser := { tokens, initial := tokens }
  let parsed ← EIO.ofExcept (parseCommands parser #[])
  pure parsed
