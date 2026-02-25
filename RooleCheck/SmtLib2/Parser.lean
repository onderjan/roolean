module

public import RooleCheck.SmtLib2.String8
public import RooleCheck.SmtLib2.Reserved
public import RooleCheck.SmtLib2.Error

import RooleCheck.SmtLib2.Lexer
public import RooleCheck.SmtLib2.Lexer

public inductive SmtIndex
  | Numeral (value: Nat) (length: Nat)
  | Symbol (name: String8)
deriving Repr

public inductive SmtIdent
  | Symbol (name: String8)
  -- there must be at least one index
  | Indexed (name: String8) (indices: Array SmtIndex)
deriving Repr

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
  | Unspecified

deriving Repr, Nonempty, Inhabited
deriving instance Nonempty for ParserError

public structure Parser where
  tokens: List Token
deriving Repr, Nonempty, Inhabited

public inductive EParser where
  | Lexer (err: ELexer)
  | Parser (err: ParserError) (parser: Parser)
deriving Repr, Nonempty, Inhabited

def Parser.error (parser: Parser) (err: ParserError) : EParser :=
  EParser.Parser err parser

def Parser.with (_parser: Parser) (tokens: List Token) : Parser :=
  { tokens := tokens }

def consumeParenClose(parser: Parser): Except EParser (Parser) :=
  match parser.tokens with
  | Token.ParenClose :: tokens => pure (parser.with tokens)
  | _ => Except.error (parser.error ParserError.Unspecified)


def parseIndices (parser: Parser) (indices: Array SmtIndex) : (Parser × Array SmtIndex) :=
  match parser.tokens with
    | Token.Numeral value length :: tokens => ((parser.with tokens), indices.push (SmtIndex.Numeral value length))
    | Token.Symbol name :: tokens => ((parser.with tokens), indices.push (SmtIndex.Symbol name))
    | _ => (parser, indices)

def parseIdent (parser: Parser) : Except EParser (Parser × SmtIdent) :=
  match parser.tokens with
  | Token.Symbol name :: tokens => pure ((parser.with tokens), (SmtIdent.Symbol name))
  | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: Token.Symbol name :: tokens => do
    -- indexed identifier, one or more indices
    let (tokens, indices) := parseIndices (parser.with tokens) #[]
    if indices.isEmpty then
      Except.error (parser.error ParserError.Unspecified)
    else
      let tokens ← consumeParenClose tokens
      pure (tokens, SmtIdent.Indexed name indices)
  | _ => Except.error (parser.error ParserError.Unspecified)

def parseSpecialConstantOpt (parser: Parser) : (Parser × Option SmtSpecialConstant) :=
  match parser.tokens with
    | Token.Numeral value numDigits :: tokens => ((parser.with tokens), some (SmtSpecialConstant.Numeral value numDigits))
    | Token.Decimal value numNumeratorDigits numDenominatorDigits :: tokens =>
      ((parser.with tokens), some (SmtSpecialConstant.Decimal value numNumeratorDigits numDenominatorDigits))
    | Token.Hexadecimal value numDigits :: tokens => ((parser.with tokens), some (SmtSpecialConstant.Hexadecimal value numDigits))
    | Token.Binary value numDigits :: tokens => ((parser.with tokens), some (SmtSpecialConstant.Binary value numDigits))
    | Token.String value :: tokens => ((parser.with tokens), some (SmtSpecialConstant.String value))
    | _ => (parser, none)

-- TODO prove termination
partial def parseSExprs (parser: Parser) (exprs: Array SmtSExpr) : Except EParser (Parser × (Array SmtSExpr)) :=
  let (parser, constant) := parseSpecialConstantOpt parser
  if let some constant := constant then
    parseSExprs parser (exprs.push (SmtSExpr.SpecialConstant constant))
  else match parser.tokens with
    | Token.Symbol name :: tokens => parseSExprs (parser.with tokens) (exprs.push (SmtSExpr.Symbol name))
    | Token.Reserved value :: tokens => parseSExprs (parser.with tokens) (exprs.push (SmtSExpr.Reserved value))
    | Token.Keyword keyword :: tokens => parseSExprs (parser.with tokens) (exprs.push (SmtSExpr.Keyword keyword))
    | Token.ParenOpen :: tokens => do
      let (parser, innerExprs) ← parseSExprs (parser.with tokens) #[]
      match parser.tokens with
        | Token.ParenClose :: tokens => parseSExprs (parser.with tokens) (exprs.push (SmtSExpr.Exprs innerExprs))
        | _ => Except.error (parser.error ParserError.Unspecified)
    | _ => pure (parser, exprs)


def parseAttributeValueOpt (parser: Parser) : Except EParser (Parser × Option SmtAttributeValue) :=
  let (parser, constant) := parseSpecialConstantOpt parser
  if let some constant := constant then
    pure (parser, some (SmtAttributeValue.SpecialConstant constant))
  else match parser.tokens with
    | Token.Symbol name :: tokens => pure ((parser.with tokens), some (SmtAttributeValue.Symbol name))
    | Token.ParenOpen :: tokens => do
      let (parser, exprs) ← parseSExprs (parser.with tokens) #[]
      match parser.tokens with
        | Token.ParenClose :: tokens => pure ((parser.with tokens), SmtAttributeValue.Exprs exprs.reverse)
        | _ => Except.error (parser.error ParserError.Unspecified)
    | _ => Except.error (parser.error ParserError.Unspecified)


def parseAttribute (parser: Parser) : Except EParser (Parser × SmtAttribute) :=
  match parser.tokens with
  | Token.Keyword keyword :: tokens => do
    let (parser, value) ← parseAttributeValueOpt (parser.with tokens)
    if let some value := value then
      pure (parser, SmtAttribute.NameValue keyword value)
    else
      pure (parser, SmtAttribute.Name keyword)
  | _ => Except.error (parser.error ParserError.Unspecified)


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
        Except.error (parser.error ParserError.Unspecified)
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
  let (parser, constant) := parseSpecialConstantOpt parser
  if let some constant := constant then
    pure (parser, SmtTerm.SpecialConstant constant)
  else match parser.tokens with
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
        Except.error (parser.error ParserError.Unspecified)
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

    | _ => Except.error (parser.error ParserError.Unspecified)
end

-- TODO prove termination
partial def parseCommands (parser: Parser) (commands: Array SmtCommand) : Except EParser (Array SmtCommand) := do
  match parser.tokens with
    | [] => pure commands
    | Token.ParenOpen :: Token.Symbol commandName :: tokens =>
      match commandName.toString? with

        | some "set-logic" =>
          if let Token.Symbol logic :: Token.ParenClose :: tokens := tokens then
            parseCommands (parser.with tokens) (commands.push (SmtCommand.SetLogic logic))
          else Except.error (parser.error ParserError.Unspecified)

        | some "set-info" =>
          let (parser, attr) ← parseAttribute (parser.with tokens)
          match parser.tokens with
            | Token.ParenClose :: tokens =>
              parseCommands (parser.with tokens) (commands.push (SmtCommand.SetInfo attr))
            | _ => Except.error (parser.error ParserError.Unspecified)

        | some "declare-fun" =>
          if let Token.Symbol name :: Token.ParenOpen :: Token.ParenClose :: tokens := tokens then
          let (parser, sort) ← parseSort (parser.with tokens)
            match parser.tokens with
              | Token.ParenClose :: tokens =>
                parseCommands (parser.with tokens) (commands.push (SmtCommand.DeclareConst name sort))
              | _ => Except.error (parser.error ParserError.Unspecified)
          else Except.error (parser.error ParserError.Unspecified)

        | some "declare-const" =>
          if let Token.Symbol name :: tokens := tokens then
            let (parser, sort) ← parseSort (parser.with tokens)
            match parser.tokens with
              | Token.ParenClose :: tokens =>
                parseCommands (parser.with tokens) (commands.push (SmtCommand.DeclareConst name sort))
              | _ => Except.error (parser.error ParserError.Unspecified)
          else Except.error (parser.error ParserError.Unspecified)

        | some "assert" =>
          let (parser, term) ← parseTerm (parser.with tokens)
          match parser.tokens with
            | Token.ParenClose :: tokens =>
              parseCommands (parser.with tokens)  (commands.push (SmtCommand.Assert term))
            | _ => Except.error (parser.error ParserError.Unspecified)

        | some "check-sat" =>
          if let Token.ParenClose :: tokens := tokens then
            parseCommands (parser.with tokens) (commands.push (SmtCommand.CheckSat))
          else Except.error (parser.error ParserError.Unspecified)

        | some "exit" =>
          if let Token.ParenClose :: tokens := tokens then
            parseCommands (parser.with tokens) (commands.push (SmtCommand.Exit))
          else Except.error (parser.error ParserError.Unspecified)

        | _ => Except.error (parser.error ParserError.Unspecified)

    | _ => Except.error (parser.error ParserError.Unspecified)


public def parse (chars: List Char8): Except EParser (Array SmtCommand) :=
  match lex chars with
    | Except.ok tokens => do
      let tokens := tokens.toList
      let parser : Parser := { tokens }
      let parsed ← parseCommands parser #[]
      pure parsed
    | Except.error err => Except.error (EParser.Lexer err)
