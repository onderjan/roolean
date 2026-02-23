module

public import RooleCheck.SmtLib2.String8
public import RooleCheck.SmtLib2.Reserved

import RooleCheck.SmtLib2.Lexer

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
  | Numeral (value: Nat) (length: Nat)
  | Decimal (value: Nat) (length: Nat) (denominatorLength: Nat)
  | Hexadecimal (value: Nat) (length: Nat)
  | Binary (value: Nat) (length: Nat)
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

public inductive EParser where
  | Lexer
  | Parser
deriving Repr

def consumeParenClose(tokens: List Token): Except Unit (List Token) :=
  match tokens with
  | Token.ParenClose :: tokens => pure tokens
  | _ => Except.error ()


def parseIndices (tokens: List Token) (indices: Array SmtIndex) : (List Token × Array SmtIndex) :=
  match tokens with
    | Token.Numeral value length :: tokens => (tokens, indices.push (SmtIndex.Numeral value length))
    | Token.Symbol name :: tokens => (tokens, indices.push (SmtIndex.Symbol name))
    | _ => (tokens, indices)

def parseIdent (tokens: List Token) : Except Unit ((List Token) × SmtIdent) :=
  match tokens with
  | Token.Symbol name :: tokens => pure (tokens, (SmtIdent.Symbol name))
  | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: Token.Symbol name :: tokens => do
    -- indexed identifier, one or more indices
    let (tokens, indices) := parseIndices tokens #[]
    if indices.isEmpty then
      Except.error ()
    else
      let tokens ← consumeParenClose tokens
      pure (tokens, SmtIdent.Indexed name indices)
  | _ => Except.error ()

def parseSpecialConstantOpt (tokens: List Token) : ((List Token) × Option SmtSpecialConstant) :=
  match tokens with
    | Token.Numeral value length :: tokens => (tokens, some (SmtSpecialConstant.Numeral value length))
    | Token.Decimal value numeratorLength denominatorLength :: tokens =>
      (tokens, some (SmtSpecialConstant.Decimal value numeratorLength denominatorLength))
    | Token.Hexadecimal value length :: tokens => (tokens, some (SmtSpecialConstant.Hexadecimal value length))
    | Token.Binary value length :: tokens => (tokens, some (SmtSpecialConstant.Binary value length))
    | Token.String value :: tokens => (tokens, some (SmtSpecialConstant.String value))
    | _ => (tokens, none)

-- TODO prove termination
partial def parseSExprs (tokens: List Token) (exprs: Array SmtSExpr) : Except Unit ((List Token) × (Array SmtSExpr)) :=
  let (tokens, constant) := parseSpecialConstantOpt tokens
  if let some constant := constant then
    parseSExprs tokens (exprs.push (SmtSExpr.SpecialConstant constant))
  else match tokens with
    | Token.Symbol name :: tokens => parseSExprs tokens (exprs.push (SmtSExpr.Symbol name))
    | Token.Reserved value :: tokens => parseSExprs tokens (exprs.push (SmtSExpr.Reserved value))
    | Token.Keyword keyword :: tokens => parseSExprs tokens (exprs.push (SmtSExpr.Keyword keyword))
    | Token.ParenOpen :: tokens => do
      let (tokens, innerExprs) ← parseSExprs tokens #[]
      match tokens with
        | Token.ParenClose :: tokens => parseSExprs tokens (exprs.push (SmtSExpr.Exprs innerExprs))
        | _ => Except.error ()
    | _ => pure (tokens, exprs)


def parseAttributeValueOpt (tokens: List Token) : Except Unit ((List Token) × Option SmtAttributeValue) :=
  let (tokens, constant) := parseSpecialConstantOpt tokens
  if let some constant := constant then
    pure (tokens, some (SmtAttributeValue.SpecialConstant constant))
  else match tokens with
    | Token.Symbol name :: tokens => pure (tokens, some (SmtAttributeValue.Symbol name))
    | Token.ParenOpen :: tokens => do
      let (tokens, exprs) ← parseSExprs tokens #[]
      match tokens with
        | Token.ParenClose :: tokens => pure (tokens, SmtAttributeValue.Exprs exprs.reverse)
        | _ => Except.error ()
    | _ => Except.error ()


def parseAttribute (tokens: List Token) : Except Unit ((List Token) × SmtAttribute) :=
  match tokens with
  | Token.Keyword keyword :: tokens => do
    let (tokens, value) ← parseAttributeValueOpt tokens
    if let some value := value then
      pure (tokens, SmtAttribute.NameValue keyword value)
    else
      pure (tokens, SmtAttribute.Name keyword)
  | _ => Except.error ()


-- TODO prove termination
mutual
partial def parseSortApplication (tokens: List Token) (ident: SmtIdent) (sorts: Array SmtSort)
  : Except Unit ((List Token) × SmtSort)  := do
  -- only simple sorts implemented
    let (tokens, sort) ← parseSort tokens
    parseSortApplication tokens ident (sorts.push sort)

partial def parseSort (tokens: List Token) : Except Unit ((List Token) × SmtSort) := do
  match tokens with
    | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: _ =>
      -- sort consists of an indexed ident
      let (tokens, ident) ← parseIdent tokens
      pure (tokens, SmtSort.Ident ident)

    | Token.ParenOpen :: tokens =>
      -- sort consists of an application
      let (tokens, ident) ← parseIdent tokens
      parseSortApplication tokens ident #[]
    | _ => -- sort consists of an ident
      let (tokens, ident) ← parseIdent tokens
      pure (tokens, SmtSort.Ident ident)
end

def parseQualifiedIdent (tokens: List Token) : Except Unit ((List Token) × SmtQualifiedIdent) := do
  -- TODO qualification
  let (tokens, ident) ← parseIdent tokens
  pure (tokens, SmtQualifiedIdent.Ident ident)

-- TODO prove termination
mutual
partial def parseTermApplication (tokens: List Token)
              (ident: SmtQualifiedIdent) (terms: Array SmtTerm): Except Unit ((List Token) × SmtTerm)  := do
  match tokens with
    | Token.ParenClose :: tokens =>
      if terms.isEmpty then
        Except.error ()
      else
        pure (tokens, SmtTerm.Application ident terms)
    | _ =>
      let (tokens, term) ← parseTerm tokens
      parseTermApplication tokens ident (terms.push term)

partial def parseLetBindings (tokens: List Token) (bindings: Array (String8 × SmtTerm))
  : Except Unit ((List Token) × Array (String8 × SmtTerm)) :=
  match tokens with
    | Token.ParenOpen :: Token.Symbol name :: tokens => do
      let (tokens, term) ← parseTerm tokens
      let tokens ← consumeParenClose tokens
      parseLetBindings tokens (bindings.push (name, term))
    | _ => pure (tokens, bindings)

partial def parseTerm (tokens: List Token) : Except Unit ((List Token) × SmtTerm) := do
  let (tokens, constant) := parseSpecialConstantOpt tokens
  if let some constant := constant then
    pure (tokens, SmtTerm.SpecialConstant constant)
  else match tokens with
    | Token.Numeral value length :: tokens => pure (tokens, SmtTerm.SpecialConstant (SmtSpecialConstant.Numeral value length))
    | Token.Decimal value numeratorLength denominatorLength :: tokens =>
        pure (tokens, SmtTerm.SpecialConstant (SmtSpecialConstant.Decimal value numeratorLength denominatorLength))
    | Token.Hexadecimal value length :: tokens => pure (tokens, SmtTerm.SpecialConstant (SmtSpecialConstant.Hexadecimal value length))
    | Token.Binary value length :: tokens => pure (tokens, SmtTerm.SpecialConstant (SmtSpecialConstant.Binary value length))
    | Token.String value :: tokens => pure (tokens, SmtTerm.SpecialConstant (SmtSpecialConstant.String value))

    | Token.Symbol _ :: _ =>
      -- normal identifier
      let (tokens, ident) ← parseIdent tokens
      pure (tokens, SmtTerm.QualifiedIdent (SmtQualifiedIdent.Ident ident))

    | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: _ =>
      -- qualified identifier
      let (tokens, ident) ← parseIdent tokens
      pure (tokens, SmtTerm.QualifiedIdent (SmtQualifiedIdent.Ident ident))

    | Token.ParenOpen :: Token.Reserved Reserved.Let :: Token.ParenOpen :: tokens =>
      -- let
      let (tokens, bindings) ← parseLetBindings tokens #[]
      if bindings.isEmpty then
        Except.error ()
      else
        let tokens ← consumeParenClose tokens
        let (tokens, term) ← parseTerm tokens
        let tokens ← consumeParenClose tokens
        pure (tokens, SmtTerm.Let bindings term)

    | Token.ParenOpen :: tokens =>
      -- application
      let (tokens, ident) ← parseQualifiedIdent tokens
      parseTermApplication tokens ident #[]

    -- unsupported: lambda, forall, exists, match, !

    | _ => Except.error ()
end

-- TODO prove termination
partial def parseCommands (tokens: List Token) (commands: Array SmtCommand) : Except EParser (Array SmtCommand) := do
  match tokens with
    | [] => pure commands
    | Token.ParenOpen :: Token.Symbol commandName :: tokens =>
      match commandName.toString? with

        | some "set-logic" =>
          if let Token.Symbol logic :: Token.ParenClose :: tokens := tokens then
            parseCommands tokens (commands.push (SmtCommand.SetLogic logic))
          else Except.error EParser.Parser

        | some "set-info" =>
          match parseAttribute tokens with
            | Except.ok (Token.ParenClose :: tokens, attr) =>
              parseCommands tokens (commands.push (SmtCommand.SetInfo attr))
            | _ => Except.error EParser.Parser

        | some "declare-fun" =>
          if let Token.Symbol name :: Token.ParenOpen :: Token.ParenClose :: tokens := tokens then
            match parseSort tokens with
              | Except.ok (Token.ParenClose :: tokens, sort) =>
                parseCommands tokens (commands.push (SmtCommand.DeclareConst name sort))
              | _ => Except.error EParser.Parser
          else Except.error EParser.Parser

        | some "declare-const" =>
          if let Token.Symbol name :: tokens := tokens then
            match parseSort tokens with
              | Except.ok (Token.ParenClose :: tokens, sort) =>
                parseCommands tokens (commands.push (SmtCommand.DeclareConst name sort))
              | _ => Except.error EParser.Parser
          else Except.error EParser.Parser

        | some "assert" =>
          match parseTerm tokens with
            | Except.ok (Token.ParenClose :: tokens, term) =>
              parseCommands tokens (commands.push (SmtCommand.Assert term))
            | _ => Except.error EParser.Parser

        | some "check-sat" =>
          if let Token.ParenClose :: tokens := tokens then
            parseCommands tokens (commands.push (SmtCommand.CheckSat))
          else Except.error EParser.Parser

        | some "exit" =>
          if let Token.ParenClose :: tokens := tokens then
            parseCommands tokens (commands.push (SmtCommand.Exit))
          else Except.error EParser.Parser

        | _ => Except.error EParser.Parser

    | _ => Except.error EParser.Parser

public def parse (chars: List Char8): Except EParser (Array SmtCommand) :=
  match lex chars with
    | Except.ok tokens => do
      let tokens := tokens.toList
      let parsed ← parseCommands tokens #[]
      pure parsed
    | Except.error {} => Except.error EParser.Lexer
