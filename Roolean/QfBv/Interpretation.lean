module

public import Roolean.SmtLib2.Parser
public import Roolean.SmtLib2.Executor

import Roolean.QfBv.BvTerm
import Roolean.QfBv.Checker
import Roolean.QfBv.Domain.ThreeValued
import Std.Data.HashMap.Basic


public structure Interpretation where
  variables: Array (String8 × Nat)
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

  | CollidingLetBinders
deriving Repr

structure BvTermW (v: VarWidths) where
  width: Nat
  value: BvTerm v width
deriving Repr, Nonempty

structure Scope (v: VarWidths) where
  binders: Std.HashMap String8 (BvTermW v)

structure Context (v: VarWidths) where
  varNames: Std.HashMap String8 (Fin v.size)
  scopes: List (Scope v)


def interpretVariableSort (sort: SmtSort): Except EInterpretation Nat :=
  match sort with
    | SmtSort.Ident (SmtIdent.Indexed typename #[width]) =>
      if let some "BitVec" := typename.toString? then
        match width with
          | SmtIndex.Numeral width _width_num_length =>
            pure width
          | _ =>
            -- bitvector width must be a numeral
            Except.error EInterpretation.BitvectorWidthNotNumeral
      else
        Except.error EInterpretation.SortNotBitVec -- expected a bitvector
    | _ =>
      -- expected a bitvector, which is a sort indexed by width
      Except.error EInterpretation.SortNotBitVec

def interpretSpecialConstant {v} (constant: SmtSpecialConstant)
  : (Except EInterpretation) (BvTermW v) := do
  let (value, width) ← match constant with

    | SmtSpecialConstant.Hexadecimal value numDigits =>
      pure (value, numDigits * 4) -- in hexadecimal, each digit represents 4 bits

    | SmtSpecialConstant.Binary value numDigits =>
      pure (value, numDigits) -- in binary, each digit represents 1 bit

    | _ =>
      -- not a QF_BV constant, decimals can be "constants" only through bvX
      Except.error EInterpretation.InvalidSpecialConstant

  let bv: Bitvector width := { value := (BitVec.ofNat width value) }
  pure { width, value := BvTerm.Constant bv}

def interpretQualifiedIdent {v} (context: Context v) (qualified: SmtQualifiedIdent)
  : (Except EInterpretation) (BvTermW v) := do

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
            return { width, value := BvTerm.Constant bv}
          | _ =>
            -- bvX should have a single index, width
            Except.error (EInterpretation.InvalidDecimalBitvec name)
      else
        -- we do not support indexed idents other than bvX where X is a decimal
        Except.error EInterpretation.InvalidIndexedQualifiedIdent
    else
      -- we do not support indexed idents other than bvX
      Except.error EInterpretation.InvalidIndexedQualifiedIdent

  -- look at variable bindings
  for scope in context.scopes do
    if let some result := scope.binders.get? name then
      return result

  -- look at variable definitions
  if let some index := context.varNames.get? name then
    -- construct a reference to the variable
    let width := v.varWidth index
    let value := BvTerm.Variable index
    return { width, value }

  -- try out special names
  if let some name := name.toString? then
    if name == "false" then
      return ({ width := 1, value := BvTerm.Constant (Bitvector.fromBool false) })
    if name == "true" then
      return ({ width := 1, value := BvTerm.Constant (Bitvector.fromBool true) })

  -- variable with the given name not found
  Except.error (EInterpretation.VariableNotFound name)

mutual
partial def interpretUniOp {v} (context: Context v) (op: UniOp) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
   -- expecting exactly one term
  match terms with
    | #[inner] =>
      let inner ← interpretTerm context inner
      pure { width := inner.width, value := BvTerm.Unary inner.value op }
    | #[] => Except.error EInterpretation.TooFewUniOpArgs
    | _ => Except.error EInterpretation.TooManyUniOpArgs


partial def interpretBiNormalPair {v} (left: BvTermW v) (right: BvTermW v) (op: BiNormalOp)
  : (Except EInterpretation) (BvTermW v) :=
  let width := left.width
  if h: left.width = right.width then
    have h : BvTerm v right.width = BvTerm v left.width := by simp[h]
    let rightValue := cast h right.value
    pure { width, value := BvTerm.BinaryNormal left.value rightValue op }
  else
    Except.error EInterpretation.BinaryWidthMismatch

partial def interpretBiNormalOp {v} (context: Context v) (op: BiNormalOp) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do

  let (left, right) ← if h: terms.size < 2 then
    Except.error EInterpretation.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- exactly two args, evaluate normally
      let left ← interpretTerm context terms[0]
      let right ← interpretTerm context terms[1]
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
        let left ← interpretBiNormalOp context op (terms.pop)
        let right ← interpretTerm context rightTerm
        pure (left, right)
      | _ =>
        -- cannot process this operation with more than two terms
        Except.error EInterpretation.TooManyBiOpArgs

  interpretBiNormalPair left right op

partial def interpretBiReductionPair {v} (left: BvTermW v) (right: BvTermW v) (op: BiReductionOp)
  : (Except EInterpretation) (BvTerm v 1) :=
  let width := left.width
  if h: left.width = right.width then
    have h : BvTerm v right.width = BvTerm v left.width := by simp[h]
    let rightValue := cast h right.value
    pure (BvTerm.BinaryReduction left.value rightValue op)
  else
    Except.error EInterpretation.BinaryWidthMismatch

partial def interpretBiReductionOp {v} (context: Context v) (op: BiReductionOp) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
  if h: terms.size < 2 then
    Except.error EInterpretation.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- exactly two args, evaluate normally
      let left ← interpretTerm context terms[0]
      let right ← interpretTerm context terms[1]
      let value ← interpretBiReductionPair left right op
      pure { width := 1, value }
  else
    -- cannot process these operations with more than two terms
    Except.error EInterpretation.TooManyBiOpArgs


partial def interpretNeOp {v} (context: Context v) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
  if h: terms.size < 2 then
    Except.error EInterpretation.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- evaluate as bit-not of the result of an equality
      let left ← interpretTerm context terms[0]
      let right ← interpretTerm context terms[1]
      let eqResult ← interpretBiReductionPair left right BiReductionOp.Eq
      let value := BvTerm.Unary eqResult UniOp.Not
      pure { width := 1, value }
  else
    -- cannot process this operation with more than two terms
    Except.error EInterpretation.TooManyBiOpArgs

partial def interpretImpliesOp {v} (context: Context v) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
  let ((left, right) : BvTermW v × BvTermW v) ← if h: terms.size < 2 then
    Except.error EInterpretation.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- consider a => b to work bit-wise:
      -- if some bit in a is set, that bit must also be set in b
      -- the result is whether this holds for all bits
      -- we can rewrite to (a or b) == b, which is true exactly
      -- when there is no bit that is set in a but not set in b
      let left ← interpretTerm context terms[0]
      let right ← interpretTerm context terms[1]
      pure (left, right)
  else
    -- Implies right-associative, transform (f s_1 s_2 .. s_n) as (f s_1 (f s_2 ... s_n))
    -- still process left-to-right
    let left ← interpretTerm context (terms[0])
    let right ← interpretImpliesOp context (terms.eraseIdx 0)
    pure (left, right)

  let orResult ← interpretBiNormalPair left right BiNormalOp.BitOr
  let eqResult ← interpretBiReductionPair orResult right BiReductionOp.Eq

  pure { width := 1, value := eqResult }


partial def intepretApplication {v} (context: Context v) (qualified: SmtQualifiedIdent) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do

  -- all supported applications are just symbols
  let name ← match qualified with
    | SmtQualifiedIdent.Ident (SmtIdent.Symbol symbol) => pure symbol
    | _ => Except.error EInterpretation.UnsupportedApplication

  -- all supported application symbols are ASCII
  let name ← match name.toString? with
    | some name => pure name
    | none => Except.error EInterpretation.UnsupportedApplication

  match name with
    | "not" | "bvnot" => interpretUniOp context UniOp.Not terms
    | "bvneg" => interpretUniOp context UniOp.Neg terms

    | "bvadd" => interpretBiNormalOp context BiNormalOp.Add terms
    | "bvsub" => interpretBiNormalOp context BiNormalOp.Sub terms
    | "bvmul" => interpretBiNormalOp context BiNormalOp.Mul terms
    | "bvudiv" => interpretBiNormalOp context BiNormalOp.Udiv terms
    | "bvurem" => interpretBiNormalOp context BiNormalOp.Urem terms
    | "bvsdiv" => interpretBiNormalOp context BiNormalOp.Sdiv terms
    | "bvsrem" => interpretBiNormalOp context BiNormalOp.Srem terms

    | "and" | "bvand" => interpretBiNormalOp context BiNormalOp.BitAnd terms
    | "or" | "bvor" => interpretBiNormalOp context BiNormalOp.BitOr terms
    | "xor" | "bvxor" => interpretBiNormalOp context BiNormalOp.BitXor terms

    | "=" | "bvcomp" => interpretBiReductionOp context BiReductionOp.Eq terms
    | "distinct" => interpretNeOp context terms
    | "=>" => interpretImpliesOp context terms

    | "bvult" => interpretBiReductionOp context BiReductionOp.Ult terms
    | "bvule" => interpretBiReductionOp context BiReductionOp.Ule terms
    | "bvslt" => interpretBiReductionOp context BiReductionOp.Slt terms
    | "bvsle" => interpretBiReductionOp context BiReductionOp.Sle terms

    -- for greater-than/greater-or-equal, reverse terms of corresponding
    -- lesser-than/lesser-or-equal
    | "bvugt" => interpretBiReductionOp context BiReductionOp.Ult terms.reverse
    | "bvuge" => interpretBiReductionOp context BiReductionOp.Ule terms.reverse
    | "bvsgt" => interpretBiReductionOp context BiReductionOp.Slt terms.reverse
    | "bvsge" => interpretBiReductionOp context BiReductionOp.Sle terms.reverse

    | "bvshl" => interpretBiNormalOp context BiNormalOp.Shl terms
    | "bvlshr" => interpretBiNormalOp context BiNormalOp.Lshr terms
    | "bvashr" => interpretBiNormalOp context BiNormalOp.Ashr terms

     -- TODO
     -- | "ite"
     -- | "concat"
     -- | "rotate_left"
     -- | "rotate_right"
     -- | "zero_extend"
     -- | "sign_extend"
     -- | "extract"

    | _ => Except.error EInterpretation.UnsupportedApplication

partial def interpretLet {v} (context: Context v) (bindings: Array (String8 × SmtTerm)) (term: SmtTerm)
  : Except EInterpretation (BvTermW v) := do
  let mut binders := {}
  for (name, term) in bindings do
    let result ← interpretTerm context term
    if binders.contains name then
      Except.error EInterpretation.CollidingLetBinders
    binders := binders.insert name result

  let scope: Scope v :=  { binders }
  let innerContext := { context with scopes := scope :: context.scopes }
  interpretTerm innerContext term

partial def interpretTerm {v} (context: Context v) (term: SmtTerm): Except EInterpretation (BvTermW v) :=
  match term with
  | SmtTerm.SpecialConstant constant => interpretSpecialConstant constant
  | SmtTerm.QualifiedIdent qualified => interpretQualifiedIdent context qualified
  | SmtTerm.Application qualified terms => intepretApplication context qualified terms
  | SmtTerm.Let bindings term => interpretLet context bindings term

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

  let varWidths: VarWidths := { inner := interpretation.variables.map (λ e => e.snd) }

  let numVariables := interpretation.variables.size

  let variableArray := interpretation.variables.mapFinIdx λ index var h =>
    let h: index < varWidths.size := by simp[varWidths, VarWidths.size, h]
    (var.fst, Fin.mk index h)

  let context := { varNames := Std.HashMap.ofArray variableArray, scopes := {} }

  match interpretTerm (v := varWidths) context assertion with
    | Except.ok term =>
      if h: term.width = 1 then
        have h : BvTerm varWidths term.width = BvTerm varWidths 1 := by simp[h]
        let term: BvTerm varWidths 1 := cast h term.value

        let variables := interpretation.variables.map (λ (var) => var.snd)

        IO.println s!"Check satisfiability\nVar widths: {reprStr varWidths}\nTerm: {reprStr term}"

        let satisfiable := solve Bitvector3 term
        IO.println s!"Satisfiable: {reprStr satisfiable}"
        pure (Except.ok ())
      else
        pure (Except.error EInterpretation.RootWidthNotOne)
    | Except.error err => return (Except.error err)


instance : Interpret Interpretation EInterpretation where
  new := Interpretation.new
  declareConst := Interpretation.declareConst
  assert := Interpretation.assert
  checkSat := Interpretation.checkSat
