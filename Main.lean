import RooleCheck.Parser.Lexer

inductive SmtIndex
  | Numeral (value: Nat)
  | Symbol (name: String)
deriving Repr

inductive SmtIdent
  | Symbol (name: String)
  -- there must be at least one index
  | Indexed (name: String) (indices: Array SmtIndex)
deriving Repr

inductive SmtSpecialConstant
  | Numeral (value: Nat)
  | Decimal (numer: Nat) (minus_log_10: Nat)
  | Hexadecimal (value: Nat)
  | Binary (value: Nat)
  | String (value: String)
deriving Repr

inductive SmtSExpr
  | SpecialConstant(value: SmtSpecialConstant)
  | Symbol (name: String)
  | Reserved (value: Reserved)
  | Keyword (name: String)
  | Exprs (exprs: Array SmtSExpr)
deriving Repr

inductive SmtAttributeValue
  | SpecialConstant (value: SmtSpecialConstant)
  | Symbol (name: String)
  | Exprs (exprs: Array SmtSExpr)
deriving Repr

inductive SmtAttribute
  | Name (name: String)
  | NameValue (name: String) (value: SmtAttributeValue)
deriving Repr

inductive SmtSort
  | Ident (ident: SmtIdent)
  -- sort applications not implemented
deriving Repr

inductive SmtQualifiedIdent
  -- 'as' qualified idents not implemented
  | Ident (ident: SmtIdent)
deriving Repr

structure SmtVariableBinding where
  symbol: String
  term: SmtTerm

inductive SmtTerm
  | SpecialConstant (constant: SmtSpecialConstant)
  | QualifiedIdent (qualified: SmtQualifiedIdent)
  -- there must be at least one term
  | Application (qualified: SmtQualifiedIdent) (terms: Array SmtTerm)
  -- there must be at least one binding
  | Let (bindings: Array (String × SmtTerm)) (term: SmtTerm)
  -- TODO let, lambda, forall, exists, match, !
deriving Repr

inductive SmtCommand
  | SetLogic (logic: String)
  | SetInfo (attr: SmtAttribute)
  | DeclareConst (name: String) (sort: SmtSort)
  | Assert (term: SmtTerm)
  | CheckSat
  | Exit
deriving Repr

inductive EParser where
  | Lexer (err: ELexer)
  | Parser (commands: Array SmtCommand) (tokens: List Token)
deriving Repr

def consumeParenClose(tokens: List Token): Except Unit (List Token) :=
  match tokens with
  | Token.ParenClose :: tail => pure tail
  | _ => Except.error ()


def parseIndices (tokens: List Token) (indices: Array SmtIndex) : (List Token × Array SmtIndex) :=
  match tokens with
    | Token.Numeral value :: tail => (tail, indices.push (SmtIndex.Numeral value))
    | Token.Symbol name :: tail => (tail, indices.push (SmtIndex.Symbol name))
    | _ => (tokens, indices)

def parseIdent (tokens: List Token) : Except Unit ((List Token) × SmtIdent) :=
  match tokens with
  | Token.Symbol name :: tail => pure (tail, (SmtIdent.Symbol name))
  | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: Token.Symbol name :: tail => do
    -- indexed identifier, one or more indices
    let (tail, indices) := parseIndices tail #[]
    if indices.isEmpty then
      Except.error ()
    else
      let tail ← consumeParenClose tail
      pure (tail, SmtIdent.Indexed name indices)
  | _ => Except.error ()

def parseSpecialConstantOpt (tokens: List Token) : ((List Token) × Option SmtSpecialConstant) :=
  match tokens with
    | Token.Numeral value :: tail => (tail, some (SmtSpecialConstant.Numeral value))
    | Token.Decimal numer minus_log_10 :: tail => (tail, some (SmtSpecialConstant.Decimal numer minus_log_10))
    | Token.Hexadecimal value :: tail => (tail, some (SmtSpecialConstant.Hexadecimal value))
    | Token.Binary value :: tail => (tail, some (SmtSpecialConstant.Binary value))
    | Token.String value :: tail => (tail, some (SmtSpecialConstant.String value))
    | _ => (tokens, none)

-- TODO prove termination
partial def parseSExprs (tokens: List Token) (exprs: Array SmtSExpr) : Except Unit ((List Token) × (Array SmtSExpr)) :=
  let (tail, constant) := parseSpecialConstantOpt tokens
  if let some constant := constant then
    parseSExprs tail (exprs.push (SmtSExpr.SpecialConstant constant))
  else match tail with
    | Token.Symbol name :: tail => parseSExprs tail (exprs.push (SmtSExpr.Symbol name))
    | Token.Reserved value :: tail => parseSExprs tail (exprs.push (SmtSExpr.Reserved value))
    | Token.Keyword keyword :: tail => parseSExprs tail (exprs.push (SmtSExpr.Keyword keyword))
    | Token.ParenOpen :: tail => do
      let (tail, innerExprs) ← parseSExprs tail #[]
      match tail with
        | Token.ParenClose :: tail => parseSExprs tail (exprs.push (SmtSExpr.Exprs innerExprs))
        | _ => Except.error ()
    | _ => pure (tail, exprs)


def parseAttributeValueOpt (tokens: List Token) : Except Unit ((List Token) × Option SmtAttributeValue) :=
  let (tail, constant) := parseSpecialConstantOpt tokens
  if let some constant := constant then
    pure (tail, some (SmtAttributeValue.SpecialConstant constant))
  else match tail with
    | Token.Symbol name :: tail => pure (tail, some (SmtAttributeValue.Symbol name))
    | Token.ParenOpen :: tail => do
      let (tail, exprs) ← parseSExprs tail #[]
      match tail with
        | Token.ParenClose :: tail => pure (tail, SmtAttributeValue.Exprs exprs.reverse)
        | _ => Except.error ()
    | _ => Except.error ()


def parseAttribute (tokens: List Token) : Except Unit ((List Token) × SmtAttribute) :=
  match tokens with
  | Token.Keyword keyword :: tail => do
    let (tail, value) ← parseAttributeValueOpt tail
    if let some value := value then
      pure (tail, SmtAttribute.NameValue keyword value)
    else
      pure (tail, SmtAttribute.Name keyword)
  | _ => Except.error ()


-- TODO prove termination
mutual
partial def parseSortApplication (tokens: List Token) (ident: SmtIdent) (sorts: Array SmtSort)
  : Except Unit ((List Token) × SmtSort)  := do
  -- only simple sorts implemented
    let (tail, sort) ← parseSort tokens
    parseSortApplication tail ident (sorts.push sort)

partial def parseSort (tokens: List Token) : Except Unit ((List Token) × SmtSort) := do
  match tokens with
    | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: _ =>
      -- sort consists of an indexed ident
      let (tail, ident) ← parseIdent tokens
      pure (tail, SmtSort.Ident ident)

    | Token.ParenOpen :: tail =>
      -- sort consists of an application
      let (tail, ident) ← parseIdent tail
      parseSortApplication tail ident #[]
    | _ => -- sort consists of an ident
      let (tail, ident) ← parseIdent tokens
      pure (tail, SmtSort.Ident ident)
end

def parseQualifiedIdent (tokens: List Token) : Except Unit ((List Token) × SmtQualifiedIdent) := do
  -- TODO qualification
  let (tail, ident) ← parseIdent tokens
  pure (tail, SmtQualifiedIdent.Ident ident)

-- TODO prove termination
mutual
partial def parseTermApplication (tokens: List Token)
              (ident: SmtQualifiedIdent) (terms: Array SmtTerm): Except Unit ((List Token) × SmtTerm)  := do
  match tokens with
    | Token.ParenClose :: tail =>
      if terms.isEmpty then
        Except.error ()
      else
        pure (tail, SmtTerm.Application ident terms)
    | _ =>
      let (tail, term) ← parseTerm tokens
      parseTermApplication tail ident (terms.push term)

partial def parseLetBindings (tokens: List Token) (bindings: Array (String × SmtTerm))
  : Except Unit ((List Token) × Array (String × SmtTerm)) :=
  match tokens with
    | Token.ParenOpen :: Token.Symbol name :: tail => do
      let (tail, term) ← parseTerm tail
      let tail ← consumeParenClose tail
      parseLetBindings tail (bindings.push (name, term))
    | _ => pure (tokens, bindings)

partial def parseTerm (tokens: List Token) : Except Unit ((List Token) × SmtTerm) := do
  let (tail, constant) := parseSpecialConstantOpt tokens
  if let some constant := constant then
    pure (tail, SmtTerm.SpecialConstant constant)
  else match tokens with
    | Token.Numeral value :: tail => pure (tail, SmtTerm.SpecialConstant (SmtSpecialConstant.Numeral value))
    | Token.Decimal numer minus_log_10 :: tail => pure (tail, SmtTerm.SpecialConstant (SmtSpecialConstant.Decimal numer minus_log_10))
    | Token.Hexadecimal value :: tail => pure (tail, SmtTerm.SpecialConstant (SmtSpecialConstant.Hexadecimal value))
    | Token.Binary value :: tail => pure (tail, SmtTerm.SpecialConstant (SmtSpecialConstant.Binary value))
    | Token.String value :: tail => pure (tail, SmtTerm.SpecialConstant (SmtSpecialConstant.String value))

    | Token.Symbol _ :: _ =>
      -- normal identifier
      let (tail, ident) ← parseIdent tokens
      pure (tail, SmtTerm.QualifiedIdent (SmtQualifiedIdent.Ident ident))

    | Token.ParenOpen :: Token.Reserved Reserved.Underscore :: _ =>
      -- qualified identifier
      let (tail, ident) ← parseIdent tokens
      pure (tail, SmtTerm.QualifiedIdent (SmtQualifiedIdent.Ident ident))

    | Token.ParenOpen :: Token.Reserved Reserved.Let :: Token.ParenOpen :: tail =>
      -- let
      let (tail, bindings) ← parseLetBindings tail #[]
      if bindings.isEmpty then
        Except.error ()
      else
        let tail ← consumeParenClose tail
        let (tail, term) ← parseTerm tail
        let tail ← consumeParenClose tail
        pure (tail, SmtTerm.Let bindings term)

    | Token.ParenOpen :: tail =>
      -- application
      let (tail, ident) ← parseQualifiedIdent tail
      parseTermApplication tail ident #[]

    -- unsupported: lambda, forall, exists, match, !

    | _ => Except.error ()
end

-- TODO prove termination
partial def parseCommands (tokens: List Token) (commands: Array SmtCommand) : Except EParser (Array SmtCommand) :=
  match tokens with
    | [] => pure commands

    | Token.ParenOpen :: Token.Symbol "set-logic" :: Token.Symbol logic :: Token.ParenClose :: tail =>
      parseCommands tail (commands.push (SmtCommand.SetLogic logic))


    | Token.ParenOpen :: Token.Symbol "set-info":: tail =>
      match parseAttribute tail with
        | Except.ok (Token.ParenClose :: tail, attr) =>
          parseCommands tail (commands.push (SmtCommand.SetInfo attr))
        | _ => Except.error (EParser.Parser commands tokens)

    | Token.ParenOpen :: Token.Symbol "declare-fun" :: Token.Symbol name :: Token.ParenOpen :: Token.ParenClose :: tail => do
      match parseSort tail with
        | Except.ok (Token.ParenClose :: tail, sort) =>
          parseCommands tail (commands.push (SmtCommand.DeclareConst name sort))
        | _ => Except.error (EParser.Parser commands tokens)

    | Token.ParenOpen :: Token.Symbol "declare-const" :: Token.Symbol name :: tail => do
      match parseSort tail with
        | Except.ok (Token.ParenClose :: tail, sort) =>
          parseCommands tail (commands.push (SmtCommand.DeclareConst name sort))
        | _ => Except.error (EParser.Parser commands tokens)


    | Token.ParenOpen :: Token.Symbol "assert":: tail =>
      match parseTerm tail with
        | Except.ok (Token.ParenClose :: tail, term) =>
          parseCommands tail (commands.push (SmtCommand.Assert term))
        | _ => Except.error (EParser.Parser commands tokens)

    | Token.ParenOpen :: Token.Symbol "check-sat" :: Token.ParenClose :: tail =>
      parseCommands tail (commands.push (SmtCommand.CheckSat))

    | Token.ParenOpen :: Token.Symbol "exit" :: Token.ParenClose :: tail =>
      parseCommands tail (commands.push (SmtCommand.Exit))

    | _ => Except.error (EParser.Parser commands tokens)

def parse (chars: List Char): Except EParser (Array SmtCommand) :=
  match lex chars with
    | Except.ok tokens => do
      let tokens := tokens.toList
      let parsed ← parseCommands tokens #[]
      pure parsed
    | Except.error err => Except.error (EParser.Lexer err)


def process: IO (Except EParser (Array SmtCommand)) := do
  let string ← IO.FS.readFile "benchmarks/lean.smt2"
  IO.println s!"Read:\n---\n{string}\n---\n"
  let chars := Std.Iter.toList (String.chars string)
  let parsed := parse chars
  pure parsed

def main : IO Unit := do
  let _discard ← process

#eval process
