module

public import Roolean.SmtLib2.String8
public import Roolean.SmtLib2.Reserved
public import Roolean.SmtLib2.Error

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
  | DefineFun (name: String8) (vars: Array (String8 × SmtSort)) (resultSort: SmtSort) (term: SmtTerm)
  | Assert (term: SmtTerm)
  | CheckSat
  | Exit
deriving Repr

public structure Parser where
  tokens: List Token
  initial: List Token
deriving Repr, Nonempty, Inhabited

def Parser.with (parser: Parser) (tokens: List Token) : Parser :=
  { tokens := tokens, initial := parser.initial }

public def Parser.next (parser: Parser) : Except EParser (Parser × Token) :=
  match parser.tokens with
  | token :: tokens =>
    pure (parser.with tokens, token)
  | [] => pure (parser, Token.End)

public def Parser.skip (parser: Parser) : Except EParser Parser := do
  let (parser, _token) ← parser.next
  pure parser

public def Parser.peek (parser: Parser) : Except EParser Token :=
  match parser.tokens with
  | token :: _ =>
    pure (token)
  | [] => pure Token.End
