module

public import Roolean.SmtLib2.Parser
public import Roolean.SmtLib2.Executor
public import Roolean.QfBv.Formula
public import Roolean.QfBv.Checker

import Std.Data.HashMap.Basic
import Roolean.QfBv.Checker


public structure Interpretation where
  variables: Array (String8 × BitvectorType)
  assertions: Array SmtTerm

public inductive EInterpretation
  | SortNotBitVec
  | BitvectorWidthNotNumeral
  | InvalidSpecialConstant
  | InvalidDecimalBitvec (name: String8)
  | InvalidIndexedQualifiedIdent
  | VariableNotFound (name: String8)
  | TooFewUniOpArgs
  | TooManyUniOpArgs
  | TooFewBiOpArgs
  | TooManyBiOpArgs
  | UnsupportedApplication
  | UnsupportedLogic (logic: String8)

  | Checker (err: EChecker)

  | LetNotImplemented -- TODO implement
deriving Repr

abbrev VariableMap := Std.HashMap String8 USize


def interpretVariableSort (sort: SmtSort): Except EInterpretation BitvectorType :=
  match sort with
    | SmtSort.Ident (SmtIdent.Indexed typename #[width]) =>
      if let some "BitVec" := typename.toString? then
        match width with
          | SmtIndex.Numeral width _width_num_length =>
            pure {width := width}
          | _ =>
            -- bitvector width must be a numeral
            Except.error EInterpretation.BitvectorWidthNotNumeral
      else
        Except.error EInterpretation.SortNotBitVec -- expected a bitvector
    | _ =>
      -- expected a bitvector, which is a sort indexed by width
      Except.error EInterpretation.SortNotBitVec

def interpretSpecialConstant (constant: SmtSpecialConstant)
  : (Except EInterpretation) Formula := do
  let (value, width) ← match constant with

    | SmtSpecialConstant.Hexadecimal value numDigits =>
      pure (value, numDigits * 4) -- in hexadecimal, each digit represents 4 bits

    | SmtSpecialConstant.Binary value numDigits =>
      pure (value, numDigits) -- in binary, each digit represents 1 bit

    | _ =>
      -- not a QF_BV constant, decimals can be "constants" only through bvX
      Except.error EInterpretation.InvalidSpecialConstant

  pure (Formula.Constant { value, width })


def interpretQualifiedIdent (variables: VariableMap) (qualified: SmtQualifiedIdent)
  : (Except EInterpretation) Formula := do

  let name ← match qualified with
  | SmtQualifiedIdent.Ident (SmtIdent.Symbol name) => pure name
  | SmtQualifiedIdent.Ident (SmtIdent.Indexed name indexed) =>
    -- try to process the form (_ bvX n)
    if let some value := (name.dropPrefix? (String8.fromUTF8 "bv")) >>= (λ (a) => a.toString?) then
      -- the number should be decimal
      if let some value := String.toNat? value then
        match indexed with
          | #[SmtIndex.Numeral width _] =>
            return (Formula.Constant { value, width })
          | _ =>
            -- bvX should have a single index, width
            Except.error (EInterpretation.InvalidDecimalBitvec name)
      else
        -- we do not support indexed idents other than bvX where X is a decimal
        Except.error EInterpretation.InvalidIndexedQualifiedIdent
    else
      -- we do not support indexed idents other than bvX
      Except.error EInterpretation.InvalidIndexedQualifiedIdent

  match variables.get? name with
  | some varIndex => pure (Formula.Variable varIndex)
  | none =>
    -- variable with the given name not found
    Except.error (EInterpretation.VariableNotFound name)


-- TODO prove termination
mutual
partial def interpretUniOp (variables: VariableMap) (op: UniOperator) (terms: Array SmtTerm)
  : (Except EInterpretation) Formula := do
   -- expecting exactly one term
  match terms with
    | #[inner] =>
      let inner ← interpretTerm variables inner
      pure (Formula.Operation (Operation.Unary op inner))
    | #[] => Except.error EInterpretation.TooFewUniOpArgs
    | _ => Except.error EInterpretation.TooManyUniOpArgs

partial def interpretBiOp (variables: VariableMap) (op: BiOperator) (terms: Array SmtTerm)
  : (Except EInterpretation) Formula := do

  let construct (op) (left) (right) :=
    pure (Formula.Operation (Operation.Binary op left right))

  if h: terms.size < 2 then
    Except.error EInterpretation.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- exactly two args, evaluate normally
      let left ← interpretTerm variables terms[0]
      let right ← interpretTerm variables terms[1]
      construct op left right
  else
    -- more than two args
    -- handle left-associative and right-associative as syntactic sugar
    -- left-assoc: 'and', 'or', 'xor' (from Core),
    --             'bvand', 'bvor', 'bvadd', 'bvmul' (from FixedSizeBitvectors),
    --             'bvxor' (from QF_BV)
    -- right-assoc: '=>' (from Core)
    -- TODO: pairwise, chainable
    match op with
      | BiOperator.BitAnd | BiOperator.BitOr | BiOperator.BitXor | BiOperator.Add | BiOperator.Mul =>
        -- left-associative, transform (f s_1 s_2 .. s_n) as (f (f s_1 s_2 ...) s_n)
        -- still process left-to-right
        let rightTerm := terms.back
        let left ← interpretBiOp variables op (terms.pop)
        let right ← interpretTerm variables rightTerm
        construct op left right
      | BiOperator.Implies =>
        -- right-associative, transform (f s_1 s_2 .. s_n) as (f s_1 (f s_2 ... s_n))
        -- still process left-to-right
        let left ← interpretTerm variables (terms[0])
        let right ← interpretBiOp variables op (terms.eraseIdx 0)
        construct op left right
      | _ =>
        -- cannot process this operation with more than two terms
        Except.error EInterpretation.TooManyBiOpArgs

partial def intepretApplication (variables: VariableMap) (qualified: SmtQualifiedIdent) (terms: Array SmtTerm)
  : (Except EInterpretation) Formula := do

  -- all supported applications are just symbols
  let name ← match qualified with
    | SmtQualifiedIdent.Ident (SmtIdent.Symbol symbol) => pure symbol
    | _ => Except.error EInterpretation.UnsupportedApplication

  -- all supported application symbols are ASCII
  let name ← match name.toString? with
    | some name => pure name
    | none => Except.error EInterpretation.UnsupportedApplication

  let result ← match name with
    | "not" | "bvnot" => interpretUniOp variables UniOperator.Not terms
    | "bvneg" => interpretUniOp variables UniOperator.Neg terms

    | "=" | "bvcomp" => interpretBiOp variables BiOperator.Eq terms
    | "distinct" => interpretBiOp variables BiOperator.Ne terms
    | "=>" => interpretBiOp variables BiOperator.Implies terms

    | "bvult" => interpretBiOp variables BiOperator.Ult terms
    | "bvule" => interpretBiOp variables BiOperator.Ule terms
    | "bvugt" => interpretBiOp variables BiOperator.Ugt terms
    | "bvuge" => interpretBiOp variables BiOperator.Uge terms

    | "bvslt" => interpretBiOp variables BiOperator.Slt terms
    | "bvsle" => interpretBiOp variables BiOperator.Sle terms
    | "bvsgt" => interpretBiOp variables BiOperator.Sgt terms
    | "bvsge" => interpretBiOp variables BiOperator.Sge terms

    | "bvadd" => interpretBiOp variables BiOperator.Add terms
    | "bvsub" => interpretBiOp variables BiOperator.Sub terms
    | "bvmul" => interpretBiOp variables BiOperator.Mul terms
    | "bvudiv" => interpretBiOp variables BiOperator.Udiv terms
    | "bvurem" => interpretBiOp variables BiOperator.Urem terms
    | "bvsdiv" => interpretBiOp variables BiOperator.Sdiv terms
    | "bvsrem" => interpretBiOp variables BiOperator.Srem terms

    | "and" | "bvand" => interpretBiOp variables BiOperator.BitAnd terms
    | "or" | "bvor" => interpretBiOp variables BiOperator.BitOr terms
    | "xor" | "bvxor" => interpretBiOp variables BiOperator.BitXor terms

    | "bvshl" => interpretBiOp variables BiOperator.Shl terms
    | "bvlshr" => interpretBiOp variables BiOperator.Lshr terms
    | "bvashr" => interpretBiOp variables BiOperator.Ashr terms

     -- TODO
     -- | "ite"
     -- | "concat"
     -- | "rotate_left"
     -- | "rotate_right"
     -- | "zero_extend"
     -- | "sign_extend"
     -- | "extract"

    | _ => Except.error EInterpretation.UnsupportedApplication

  pure result

partial def interpretLet (variables: VariableMap) (bindings: Array (String8 × SmtTerm)) (term: SmtTerm)
  : Except EInterpretation Formula := do
  Except.error EInterpretation.LetNotImplemented -- TODO implement

partial def interpretTerm (variables: VariableMap) (term: SmtTerm): (Except EInterpretation) Formula :=
  match term with
  | SmtTerm.SpecialConstant constant => interpretSpecialConstant constant
  | SmtTerm.QualifiedIdent qualified => interpretQualifiedIdent variables qualified
  | SmtTerm.Application qualified terms => intepretApplication variables qualified terms
  | SmtTerm.Let bindings term => interpretLet variables bindings term

end

public def Interpretation.new : Interpretation :=
  { variables := #[], assertions := #[] }

public def Interpretation.declareConst (interpretation: Interpretation)
  (name: String8) (sort: SmtSort) : Except EInterpretation Interpretation :=
    match interpretVariableSort sort with
      | Except.ok type =>
        let variables := interpretation.variables.push (name, type)
        pure {interpretation with variables}
      | Except.error err => Except.error err

public def Interpretation.assert (interpretation: Interpretation)
  (term: SmtTerm) : Interpretation :=
  { interpretation with assertions := interpretation.assertions.push term}

public def Interpretation.checkSat (interpretation: Interpretation): IO (Except EInterpretation Unit) := do
  -- combine assertions
  let assertion :=
    match h: interpretation.assertions.size with
      | 0 =>
        -- conjunction of 0 terms is trivially true
        SmtTerm.SpecialConstant (SmtSpecialConstant.String (String8.fromUTF8 "true"))
      | 1 =>
        -- just the single assertion
        interpretation.assertions[0]
      | _ =>
        -- combine the assertions in a conjunction, which is left-associative
        SmtTerm.Application (SmtQualifiedIdent.Ident (SmtIdent.Symbol (String8.fromUTF8 "and"))) interpretation.assertions

  let mut variableMap: VariableMap := {}
  let mut index: USize := 0
  for (name, _type) in interpretation.variables do
    variableMap := variableMap.insert name index
    index := index + 1

  let formula ← match interpretTerm variableMap assertion with
    | Except.ok formula => pure formula
    | Except.error err => return (Except.error err)

  let variables := interpretation.variables.map (λ (var) => var.snd)

  let problem := { variables, formula }

  let checked ← solve problem
  match checked with
    | Except.ok () => pure (Except.ok ())
    | Except.error err => pure (Except.error (EInterpretation.Checker err))

instance : Interpret Interpretation EInterpretation where
  new := Interpretation.new
  declareConst := Interpretation.declareConst
  assert := Interpretation.assert
  checkSat := Interpretation.checkSat
