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
  | BinaryWidthMismatch

  | UnsupportedApplication
  | UnsupportedLogic (logic: String8)
  | RootWidthNotOne

  | Checker (err: EChecker)

  | LetNotImplemented -- TODO implement
deriving Repr

structure VariableData where
  index: USize
  width: Nat

abbrev VariableMap := Std.HashMap String8 VariableData

structure FormulaW where
  width: Nat
  value: Formula width
deriving Repr, Nonempty

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
  : (Except EInterpretation) FormulaW := do
  let (value, width) ← match constant with

    | SmtSpecialConstant.Hexadecimal value numDigits =>
      pure (value, numDigits * 4) -- in hexadecimal, each digit represents 4 bits

    | SmtSpecialConstant.Binary value numDigits =>
      pure (value, numDigits) -- in binary, each digit represents 1 bit

    | _ =>
      -- not a QF_BV constant, decimals can be "constants" only through bvX
      Except.error EInterpretation.InvalidSpecialConstant

  let bv: Bitvector width := { value := (BitVec.ofNat width value) }
  pure { width, value := Formula.Leaf (Primary.Constant bv)}

def interpretQualifiedIdent (variables: VariableMap) (qualified: SmtQualifiedIdent)
  : (Except EInterpretation) FormulaW := do

  let name ← match qualified with
  | SmtQualifiedIdent.Ident (SmtIdent.Symbol name) => pure name
  | SmtQualifiedIdent.Ident (SmtIdent.Indexed name indexed) =>
    -- try to process the form (_ bvX n)
    if let some value := (name.dropPrefix? (String8.fromUTF8 "bv")) >>= (λ (a) => a.toString?) then
      -- the number should be decimal
      if let some value := String.toNat? value then
        match indexed with
          | #[SmtIndex.Numeral width _] =>
            -- construct bitvector
            let bv := { value := BitVec.ofNat width value }
            return { width, value := Formula.Leaf (Primary.Constant bv)}
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
  | some varData =>
    -- construct a reference to the variable

    pure { width := varData.width, value := Formula.Leaf (Primary.Variable varData.index) }
  | none =>
    -- variable with the given name not found
    Except.error (EInterpretation.VariableNotFound name)

-- TODO prove termination
mutual
partial def interpretUniOp (variables: VariableMap) (op: UniOp) (terms: Array SmtTerm)
  : (Except EInterpretation) FormulaW := do
   -- expecting exactly one term
  match terms with
    | #[inner] =>
      let inner ← interpretTerm variables inner
      pure { width := inner.width, value := Formula.Unary inner.value op }
    | #[] => Except.error EInterpretation.TooFewUniOpArgs
    | _ => Except.error EInterpretation.TooManyUniOpArgs


partial def interpretBiNormalPair (left: FormulaW) (right: FormulaW) (op: BiNormalOp)
  : (Except EInterpretation) FormulaW :=
  let width := left.width
  if h: left.width = right.width then
    have h : Formula right.width = Formula left.width := by simp[h]
    let rightValue := cast h right.value
    pure { width, value := Formula.BinaryNormal left.value rightValue op }
  else
    Except.error EInterpretation.BinaryWidthMismatch

partial def interpretBiNormalOp (variables: VariableMap) (op: BiNormalOp) (terms: Array SmtTerm)
  : (Except EInterpretation) FormulaW := do

  let ((left, right) : FormulaW × FormulaW) ← if h: terms.size < 2 then
    Except.error EInterpretation.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- exactly two args, evaluate normally
      let left ← interpretTerm variables terms[0]
      let right ← interpretTerm variables terms[1]
      pure (left, right)
  else
    -- more than two args
    -- handle left-associative and right-associative as syntactic sugar
    -- left-assoc: 'and', 'or', 'xor' (from Core),
    --             'bvand', 'bvor', 'bvadd', 'bvmul' (from FixedSizeBitvectors),
    --             'bvxor' (from QF_BV)
    -- right-assoc: '=>' (from Core)
    -- TODO: pairwise, chainable
    match op with
      | .BitAnd | .BitOr | .BitXor | .Add | .Mul =>
        -- left-associative, transform (f s_1 s_2 .. s_n) as (f (f s_1 s_2 ...) s_n)
        -- still process left-to-right
        let rightTerm := terms.back
        let left ← interpretBiNormalOp variables op (terms.pop)
        let right ← interpretTerm variables rightTerm
        pure (left, right)
      | _ =>
        -- cannot process this operation with more than two terms
        Except.error EInterpretation.TooManyBiOpArgs

  interpretBiNormalPair left right op

partial def interpretBiReductionPair (left: FormulaW) (right: FormulaW) (op: BiReductionOp)
  : (Except EInterpretation) (Formula 1) :=
  let width := left.width
  if h: left.width = right.width then
    have h : Formula right.width = Formula left.width := by simp[h]
    let rightValue := cast h right.value
    pure (Formula.BinaryReduction left.value rightValue op)
  else
    Except.error EInterpretation.BinaryWidthMismatch

partial def interpretBiReductionOp (variables: VariableMap) (op: BiReductionOp) (terms: Array SmtTerm)
  : (Except EInterpretation) FormulaW := do
  if h: terms.size < 2 then
    Except.error EInterpretation.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- exactly two args, evaluate normally
      let left ← interpretTerm variables terms[0]
      let right ← interpretTerm variables terms[1]
      let value ← interpretBiReductionPair left right op
      pure { width := 1, value }
  else
    -- cannot process these operations with more than two terms
    Except.error EInterpretation.TooManyBiOpArgs


partial def interpretNeOp (variables: VariableMap) (terms: Array SmtTerm)
  : (Except EInterpretation) FormulaW := do
  if h: terms.size < 2 then
    Except.error EInterpretation.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- evaluate as bit-not of the result of an equality
      let left ← interpretTerm variables terms[0]
      let right ← interpretTerm variables terms[1]
      let eqResult ← interpretBiReductionPair left right BiReductionOp.Eq
      let value := Formula.Unary eqResult UniOp.Not
      pure { width := 1, value }
  else
    -- cannot process this operation with more than two terms
    Except.error EInterpretation.TooManyBiOpArgs

partial def interpretImpliesOp (variables: VariableMap) (terms: Array SmtTerm)
  : (Except EInterpretation) FormulaW := do
  let ((left, right) : FormulaW × FormulaW) ← if h: terms.size < 2 then
    Except.error EInterpretation.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- consider a => b to work bit-wise:
      -- if some bit in a is set, that bit must also be set in b
      -- the result is whether this holds for all bits
      -- we can rewrite to (a or b) == b, which is true exactly
      -- when there is no bit that is set in a but not set in b
      let left ← interpretTerm variables terms[0]
      let right ← interpretTerm variables terms[1]
      pure (left, right)
  else
    -- Implies right-associative, transform (f s_1 s_2 .. s_n) as (f s_1 (f s_2 ... s_n))
    -- still process left-to-right
    let left ← interpretTerm variables (terms[0])
    let right ← interpretImpliesOp variables (terms.eraseIdx 0)
    pure (left, right)

  let orResult ← interpretBiNormalPair left right BiNormalOp.BitOr
  let eqResult ← interpretBiReductionPair orResult right BiReductionOp.Eq

  pure { width := 1, value := eqResult }


partial def intepretApplication (variables: VariableMap) (qualified: SmtQualifiedIdent) (terms: Array SmtTerm)
  : (Except EInterpretation) FormulaW := do

  -- all supported applications are just symbols
  let name ← match qualified with
    | SmtQualifiedIdent.Ident (SmtIdent.Symbol symbol) => pure symbol
    | _ => Except.error EInterpretation.UnsupportedApplication

  -- all supported application symbols are ASCII
  let name ← match name.toString? with
    | some name => pure name
    | none => Except.error EInterpretation.UnsupportedApplication

  match name with
    | "not" | "bvnot" => interpretUniOp variables UniOp.Not terms
    | "bvneg" => interpretUniOp variables UniOp.Neg terms

    | "bvadd" => interpretBiNormalOp variables BiNormalOp.Add terms
    | "bvsub" => interpretBiNormalOp variables BiNormalOp.Sub terms
    | "bvmul" => interpretBiNormalOp variables BiNormalOp.Mul terms
    | "bvudiv" => interpretBiNormalOp variables BiNormalOp.Udiv terms
    | "bvurem" => interpretBiNormalOp variables BiNormalOp.Urem terms
    | "bvsdiv" => interpretBiNormalOp variables BiNormalOp.Sdiv terms
    | "bvsrem" => interpretBiNormalOp variables BiNormalOp.Srem terms

    | "and" | "bvand" => interpretBiNormalOp variables BiNormalOp.BitAnd terms
    | "or" | "bvor" => interpretBiNormalOp variables BiNormalOp.BitOr terms
    | "xor" | "bvxor" => interpretBiNormalOp variables BiNormalOp.BitXor terms

    | "=" | "bvcomp" => interpretBiReductionOp variables BiReductionOp.Eq terms
    | "distinct" => interpretNeOp variables terms
    | "=>" => interpretImpliesOp variables terms

    | "bvult" => interpretBiReductionOp variables BiReductionOp.Ult terms
    | "bvule" => interpretBiReductionOp variables BiReductionOp.Ule terms
    | "bvslt" => interpretBiReductionOp variables BiReductionOp.Slt terms
    | "bvsle" => interpretBiReductionOp variables BiReductionOp.Sle terms

    -- for greater-than/greater-or-equal, reverse terms of corresponding
    -- lesser-than/lesser-or-equal
    | "bvugt" => interpretBiReductionOp variables BiReductionOp.Ult terms.reverse
    | "bvuge" => interpretBiReductionOp variables BiReductionOp.Ule terms.reverse
    | "bvsgt" => interpretBiReductionOp variables BiReductionOp.Slt terms.reverse
    | "bvsge" => interpretBiReductionOp variables BiReductionOp.Sle terms.reverse

    | "bvshl" => interpretBiNormalOp variables BiNormalOp.Shl terms
    | "bvlshr" => interpretBiNormalOp variables BiNormalOp.Lshr terms
    | "bvashr" => interpretBiNormalOp variables BiNormalOp.Ashr terms

     -- TODO
     -- | "ite"
     -- | "concat"
     -- | "rotate_left"
     -- | "rotate_right"
     -- | "zero_extend"
     -- | "sign_extend"
     -- | "extract"

    | _ => Except.error EInterpretation.UnsupportedApplication

partial def interpretLet (variables: VariableMap) (bindings: Array (String8 × SmtTerm)) (term: SmtTerm)
  : Except EInterpretation FormulaW := do
  Except.error EInterpretation.LetNotImplemented -- TODO implement

partial def interpretTerm (variables: VariableMap) (term: SmtTerm): (Except EInterpretation) FormulaW :=
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
  for (name, type) in interpretation.variables do
    variableMap := variableMap.insert name { index, width := type.width }
    index := index + 1

  let formula ← match interpretTerm variableMap assertion with
    | Except.ok formula => pure formula
    | Except.error err => return (Except.error err)

  if h: formula.width = 1 then
    have h : Formula formula.width = Formula 1 := by simp[h]
    let formula: Formula 1 := cast h formula.value

    let variables := interpretation.variables.map (λ (var) => var.snd)

    IO.println s!"Check satisfiability\nVariables: {reprStr variables}\nFormula: {reprStr formula}"

    let checked := solve variables formula
    match checked with
      | Except.ok satisfiable =>
        IO.println s!"Satisfiable: {reprStr satisfiable}"
        pure (Except.ok ())
      | Except.error err => pure (Except.error (EInterpretation.Checker err))
  else
    pure (Except.error EInterpretation.RootWidthNotOne)

instance : Interpret Interpretation EInterpretation where
  new := Interpretation.new
  declareConst := Interpretation.declareConst
  assert := Interpretation.assert
  checkSat := Interpretation.checkSat
