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
  | ExpectedUnderscore
  | ExpectedSymbol
  | ExpectedKeyword
  | EmptyIdentIndices
  | InvalidIdent
  | InvalidAttributeValue
  | EmptyApplication
  | EmptyLetBindings
  | ExpectedTerm
  | ExpectedCommand
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

def Parser.next (parser: Parser) : Except EParser (Parser × Token) :=
  match parser.tokens with
  | token :: tokens =>
    pure (parser.with tokens, token)
  | [] => pure (parser, Token.End)

def Parser.skip (parser: Parser) : Except EParser Parser := do
  let (parser, _token) ← parser.next
  pure parser

def Parser.peek (parser: Parser) : Except EParser Token :=
  match parser.tokens with
  | token :: _ =>
    pure (token)
  | [] => pure Token.End

def consumeParenOpen(parser: Parser): Except EParser (Parser) := do
  let (parser, token) ← parser.next
  match token with
  | Token.ParenOpen => pure parser
  | _ => Except.error (parser.error ParserError.ExpectedParenOpen)

def consumeParenClose(parser: Parser): Except EParser (Parser) := do
  let (parser, token) ← parser.next
  match token with
  | Token.ParenClose => pure parser
  | _ => Except.error (parser.error ParserError.ExpectedParenClose)

def consumeUnderscore(parser: Parser): Except EParser (Parser) := do
  let (parser, token) ← parser.next
  match token with
  | Token.Reserved Reserved.Underscore => pure parser
  | _ => Except.error (parser.error ParserError.ExpectedUnderscore)

def consumeSymbol(parser: Parser): Except EParser (Parser × String8) := do
  let (parser, token) ← parser.next
  match token with
  | Token.Symbol name => pure (parser, name)
  | _ => Except.error (parser.error ParserError.ExpectedSymbol)

def consumeKeyword(parser: Parser): Except EParser (Parser × String8) := do
  let (parser, token) ← parser.next
  match token with
  | Token.Keyword name => pure (parser, name)
  | _ => Except.error (parser.error ParserError.ExpectedKeyword)

partial def parseIndices (parser: Parser) (indices: Array SmtIndex) : Except EParser (Parser × Array SmtIndex) := do
  let peeked ← parser.peek
  match peeked with
    | Token.Numeral value length =>
      let parser ← parser.skip
      parseIndices parser (indices.push (SmtIndex.Numeral value length))
    | Token.Symbol name =>
      let parser ← parser.skip
      parseIndices parser (indices.push (SmtIndex.Symbol name))
    | _ => pure (parser, indices)

def parseIndexedIdent (parser: Parser) : Except EParser (Parser × SmtIdent) := do
  -- indexed identifier has an underscore followed by name and one or more indices
  let parser ← consumeUnderscore parser

  let (parser, token) ← parser.next
  match token with
  | Token.Symbol name =>
    let (parser, indices) ← parseIndices parser #[]
    if indices.isEmpty then
      Except.error (parser.error ParserError.EmptyIdentIndices)
    let parser ← consumeParenClose parser
    pure (parser, SmtIdent.mk name indices)
  | _ => Except.error (parser.error ParserError.InvalidIdent)


def parseIdent (parser: Parser) : Except EParser (Parser × SmtIdent) := do
  let (parser, token) ← parser.next

  match token with
  | Token.Symbol name => pure (parser, (SmtIdent.simple name))
  | Token.ParenOpen => parseIndexedIdent parser
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

partial def parseSExprs (parser: Parser) (exprs: Array SmtSExpr) : Except EParser (Parser × (Array SmtSExpr)) := do
  let peeked ← parser.peek
  match peeked with
    | Token.Symbol name =>
      let parser ← parser.skip
      parseSExprs parser (exprs.push (SmtSExpr.Symbol name))
    | Token.Reserved value =>
      let parser ← parser.skip
      parseSExprs parser (exprs.push (SmtSExpr.Reserved value))
    | Token.Keyword keyword =>
      let parser ← parser.skip
      parseSExprs parser (exprs.push (SmtSExpr.Keyword keyword))
    | Token.ParenOpen =>
      let parser ← parser.skip
      let (parser, innerExprs) ← parseSExprs parser #[]
      let parser ← consumeParenClose parser
      parseSExprs parser (exprs.push (SmtSExpr.Exprs innerExprs))
    | token =>
      if let some constant := specialConstant? token then
        let parser ← parser.skip
        parseSExprs parser (exprs.push (SmtSExpr.SpecialConstant constant))
      else
        pure (parser, exprs)

def parseAttribute (parser: Parser) : Except EParser (Parser × SmtAttribute) := do
  let (parser, keyword) ← consumeKeyword parser
  let peeked ← parser.peek

  let (parser, value) ← match peeked with
    | Token.Symbol name =>
      -- attribute value is a symbol
      let parser ← parser.skip
      let value := SmtAttributeValue.Symbol name
      pure (parser, some value)
    | Token.ParenOpen =>
      -- attribute value is an S-expression
      let parser ← parser.skip
      let (parser, exprs) ← parseSExprs parser #[]
      let parser ← consumeParenClose parser
      let value := SmtAttributeValue.Exprs exprs
      pure (parser, some value)
    | token =>
      if let some constant := specialConstant? token then
        let parser ← parser.skip
        let value := SmtAttributeValue.SpecialConstant constant
        pure (parser, some value)
      else
        pure (parser, none) -- attribute has no value

  if let some value := value then
    pure (parser, SmtAttribute.NameValue keyword value)
  else
    pure (parser, SmtAttribute.Name keyword)

mutual
partial def parseSortApplication (parser: Parser) (ident: SmtIdent) (sorts: Array SmtSort)
  : Except EParser (Parser × SmtSort)  := do
  -- only simple sorts implemented
    let (parser, sort) ← parseSort parser
    parseSortApplication parser ident (sorts.push sort)

partial def parseSort (parser: Parser) : Except EParser (Parser × SmtSort) := do
  let peeked ← parser.peek
  match peeked with
  | Token.ParenOpen =>
    let parser ← parser.skip
    let peeked ← parser.peek
    match peeked with
    | Token.Reserved Reserved.Underscore =>
      -- sort consists of an indexed ident
      let (parser, ident) ← parseIndexedIdent parser
      pure (parser, SmtSort.Ident ident)
    | _ =>
      -- sort consists of an application
      let (parser, ident) ← parseIdent parser
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
  let peeked ← parser.peek
  match peeked with
    | Token.ParenClose =>
      let parser ← parser.skip
      if terms.isEmpty then
        Except.error (parser.error ParserError.EmptyApplication)
      pure (parser, SmtTerm.Application ident terms)
    | _ =>
      let (parser, term) ← parseTerm parser
      parseTermApplication parser ident (terms.push term)

partial def parseLetBindings (parser: Parser) (bindings: Array (String8 × SmtTerm))
  : Except EParser (Parser × Array (String8 × SmtTerm)) := do
  let peeked ← parser.peek
  match peeked with
    | Token.ParenOpen =>
      let parser ← parser.skip
      let (parser, token) ← parser.next
      match token with
      | Token.Symbol name =>
        let (parser, term) ← parseTerm parser
        let parser ← consumeParenClose parser
        parseLetBindings parser (bindings.push (name, term))
      | _ => Except.error (parser.error ParserError.ExpectedSymbol)
    | _ => pure (parser, bindings)

partial def parseTerm (parser: Parser) : Except EParser (Parser × SmtTerm) := do
  let peeked ← parser.peek
  match peeked with
    | Token.Numeral value length =>
      let parser ← parser.skip
      pure (parser, SmtTerm.SpecialConstant (SmtSpecialConstant.Numeral value length))
    | Token.Decimal value numeratorLength denominatorLength =>
      let parser ← parser.skip
      pure (parser,
        SmtTerm.SpecialConstant (SmtSpecialConstant.Decimal value numeratorLength denominatorLength))
    | Token.Hexadecimal value length =>
      let parser ← parser.skip
      pure (parser, SmtTerm.SpecialConstant (SmtSpecialConstant.Hexadecimal value length))
    | Token.Binary value length =>
      let parser ← parser.skip
      pure (parser, SmtTerm.SpecialConstant (SmtSpecialConstant.Binary value length))
    | Token.String value =>
      let parser ← parser.skip
      pure (parser, SmtTerm.SpecialConstant (SmtSpecialConstant.String value))

    | Token.Symbol _ =>
      -- normal identifier
      let (tokens, ident) ← parseIdent parser
      pure (tokens, SmtTerm.QualifiedIdent (SmtQualifiedIdent.Ident ident))

    | Token.ParenOpen =>
      let parser ← parser.skip
      let peeked ← parser.peek

      match peeked with
      | Token.Reserved Reserved.Underscore =>
        -- qualified identifier
        let parser ← parser.skip
        let (tokens, ident) ← parseIdent parser
        pure (tokens, SmtTerm.QualifiedIdent (SmtQualifiedIdent.Ident ident))
      | Token.Reserved Reserved.Let =>
        -- let
        let parser ← parser.skip
        let parser ← consumeParenOpen parser
        let (tokens, bindings) ← parseLetBindings parser #[]
        if bindings.isEmpty then
          Except.error (parser.error ParserError.EmptyLetBindings)
        let tokens ← consumeParenClose tokens
        let (tokens, term) ← parseTerm tokens
        let tokens ← consumeParenClose tokens
        pure (tokens, SmtTerm.Let bindings term)
      | _ =>
      -- application
      let (parser, ident) ← parseQualifiedIdent parser
      parseTermApplication parser ident #[]
      -- unsupported: lambda, forall, exists, match, !

    | peeked =>
      if let some constant := specialConstant? peeked then
        let parser ← parser.skip
        pure (parser, SmtTerm.SpecialConstant constant)
      else
        Except.error (parser.error ParserError.ExpectedTerm)
end

-- TODO prove termination
partial def parseCommands (parser: Parser) (commands: Array SmtCommand) : Except EParser (Array SmtCommand) := do
  let (parser, token) ← parser.next
  match token with
  | Token.ParenOpen =>
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
  | Token.End =>
    return commands
  | _ => Except.error (parser.error ParserError.ExpectedCommand)


public def parse (filename: String): EIO EParser (Array SmtCommand) := do
  let tokens ← (lex filename).adapt (λ e => EParser.Lexer e)
  let tokens := tokens.toList
  let parser : Parser := { tokens, initial := tokens }
  let parsed ← EIO.ofExcept (parseCommands parser #[])
  pure parsed
