module

public import Roolean.SmtLib2.Parser
public import Roolean.SmtLib2.Executor
public import Roolean.QfBv.Checker

import Roolean.QfBv.BvTerm
import Roolean.QfBv.Solver
import Roolean.QfBv.Domain.Bitvector3
public import Std.Data.HashMap.Basic
import Roolean.QfBv.BvTerm

public structure Function where
  varWidths: Array (String8 × Nat)
  resultWidth: Nat
  term: SmtTerm

public structure Interpretation where
  variables: Array (String8 × Nat)
  functions: Std.HashMap String8 Function
  assertions: Array SmtTerm

public inductive EInterpretation
  | SortNotBitVec
  | BitvectorWidthNotNumeral
  | InvalidSpecialConstant
  | InvalidDecimalBitvec (name: String8)

  | InvalidIndexedQualifiedIdent
  | VariableNotFound (name: String8) (scopes: List (Std.HashMap String8 Nat))

  | TooFewOpArgs
  | TooManyOpArgs

  | BinaryWidthMismatch
  | ImpliesWidthNotOne
  | IteConditionWidthNotOne
  | IteBranchWidthMismatch
  | BadExtraction

  | BadApplication (name: String8)
  | UnsupportedLogic (logic: String8)
  | RootWidthNotOne

  | CollidingLetBinders
  | BadVariable

  | DuplicateFunction (name: String8)
  | BadFunctionArgumentWidth
  | BadFunctionResultWidth
  | CollidingFunctionParameters

  | InvalidProof (err: Proof.EOfSmt)
  | WrongProofCheck (err: ECheckResult)
deriving Repr

structure BvTermW (v: VarWidths) where
  width: Nat
  value: BvTerm v width
deriving Repr, Nonempty

structure Context where
  interpretation: Interpretation
  scopes: List (Std.HashMap String8 Nat)

def interpretVariableSort (sort: SmtSort): Except EInterpretation Nat :=
  match sort with
    | SmtSort.Ident { name := typename, indices := #[width] } =>
      if let some "BitVec" := typename.toString? then
        match width with
          | SmtIndex.Numeral width _width_num_length =>
            pure width
          | _ =>
            -- bitvector width must be a numeral
            Except.error EInterpretation.BitvectorWidthNotNumeral
      else
        Except.error EInterpretation.SortNotBitVec -- expected a bitvector
    | SmtSort.Ident { name := typename, indices := #[] } =>
      if let some "Bool" := typename.toString? then
        pure 1
      else
        Except.error EInterpretation.SortNotBitVec -- expected a bool
    | _ =>
      -- expected a bitvector, which is a sort indexed by width, or a Bool
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

mutual

partial def interpretQualifiedIdent {v} (context: Context) (qualified: SmtQualifiedIdent)
  : (Except EInterpretation) (BvTermW v) := do

  let ident := match qualified with
    | SmtQualifiedIdent.Ident ident => ident

  let name ← if ident.indices.isEmpty then
    pure ident.name
  else
    -- try to process the form (_ bvX n)
    let withoutPrefix := ident.name.dropPrefix? (String8.fromUTF8 "bv")
    if let some value := withoutPrefix >>= (λ (a) => a.toString?) then
      -- the number should be decimal
      if let some value := String.toNat? value then
        match ident.indices with
          | #[SmtIndex.Numeral width _] =>
            -- construct bitvector
            let bv := { value := BitVec.ofNat width value }
            return { width, value := BvTerm.Constant bv}
          | _ =>
            -- bvX should have a single index, width
            Except.error (EInterpretation.InvalidDecimalBitvec ident.name)
      else
        -- we do not support indexed idents other than bvX where X is a decimal
        Except.error EInterpretation.InvalidIndexedQualifiedIdent
    else
      -- we do not support indexed idents other than bvX
      Except.error EInterpretation.InvalidIndexedQualifiedIdent

  -- look at variable bindings
  for scope in context.scopes do
    if let some index := scope.get? name then
      -- construct a reference to the variable
      let width := v.varWidth index
      if h: index < v.size then
        let value := BvTerm.Variable (Fin.mk index h)
        return { width, value }
      else
        Except.error (EInterpretation.BadVariable)

  -- look at functions
  if let some function := context.interpretation.functions.get? name then
    -- no arguments
    if function.varWidths.size > 0 then
      let () ← (Except.error EInterpretation.TooManyOpArgs)
    let term ← interpretTerm (v:=v) context function.term
    return term

  -- try out special names
  if let some name := name.toString? then
    if name == "false" then
      return ({ width := 1, value := BvTerm.Constant (Bitvector.fromBool false) })
    if name == "true" then
      return ({ width := 1, value := BvTerm.Constant (Bitvector.fromBool true) })

  -- variable with the given name not found
  Except.error (EInterpretation.VariableNotFound name context.scopes)

partial def interpretUniOp {v} (context: Context) (op: UniOp) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
   -- expecting exactly one term
  match terms with
    | #[inner] =>
      let inner ← interpretTerm context inner
      pure { width := inner.width, value := BvTerm.Unary inner.value op }
    | #[] => Except.error EInterpretation.TooFewOpArgs
    | _ => Except.error EInterpretation.TooManyOpArgs


partial def interpretBiNormalPair {v} (left: BvTermW v) (right: BvTermW v) (op: BiNormalOp)
  : (Except EInterpretation) (BvTermW v) :=
  let width := left.width
  if h: left.width = right.width then
    have h : BvTerm v right.width = BvTerm v left.width := by simp[h]
    let rightValue := cast h right.value
    pure { width, value := BvTerm.BinaryNormal left.value rightValue op }
  else
    Except.error EInterpretation.BinaryWidthMismatch

partial def interpretBiNormalOp {v} (context: Context) (op: BiNormalOp) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do

  let (left, right) ← if h: terms.size < 2 then
    Except.error EInterpretation.TooFewOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- exactly two args, evaluate normally
      let left ← interpretTerm context terms[0]
      let right ← interpretTerm context terms[1]
      pure (left, right)
  else
    -- more than two args
    -- handle as syntactic sugar
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
        Except.error EInterpretation.TooManyOpArgs

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

partial def andCombine {v} (context: Context) (ops: Array (BvTermW v))
  : (Except EInterpretation) (BvTermW v) := do
  if h: ops.size < 2 then
    Except.error EInterpretation.TooFewOpArgs -- must have at least two args
  else if ops.size == 2 then
    -- exactly two args, evaluate normally
    interpretBiNormalPair ops[0] ops[1] BiNormalOp.BitAnd
  else
    -- more than two args, left-associative
    let right := ops.back
    let left ← andCombine context ops.pop
    interpretBiNormalPair left right BiNormalOp.BitAnd


partial def interpretBiReductionOp {v} (context: Context) (op: BiReductionOp) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
  if h: terms.size < 2 then
    Except.error EInterpretation.TooFewOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- exactly two args, evaluate normally
      let left ← interpretTerm context terms[0]
      let right ← interpretTerm context terms[1]
      let value ← interpretBiReductionPair left right op
      pure { width := 1, value }
  else
    -- more than two args
    -- handle as syntactic sugar
    match op with
      | .Eq =>
        -- chainable, transform (f t_1 ... t_n) to (and (f t_1 t_2) (f t_2 t_3) ... (f t_n-1 t_n))
        let mut ops := #[]
        for h: i in 1...terms.size do
          let left := terms[i-1]
          let right := terms[i]
          let op ← interpretBiReductionOp context op #[left, right]
          ops := ops.push op

        andCombine context ops
      | _ =>
        -- cannot process these operations with more than two terms
        Except.error EInterpretation.TooManyOpArgs


partial def interpretNeOp {v} (context: Context) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
  if h: terms.size < 2 then
    Except.error EInterpretation.TooFewOpArgs -- must have at least two args
  else if terms.size == 2 then
    -- evaluate as bit-not of the result of an equality
    let left ← interpretTerm context terms[0]
    let right ← interpretTerm context terms[1]
    let eqResult ← interpretBiReductionPair left right BiReductionOp.Eq
    let value := BvTerm.Unary eqResult UniOp.Not
    pure { width := 1, value }
  else
    -- pairwise, transform  (f t_1 ... t_n) to (and (f t_1 t_2) (f t_1 t_3) ... (f t_1 t_n) (f t_2 ... t_n))
    -- take the first operation and combine it with others
    let first := terms[0]
    let terms := terms.eraseIdx 0
    let mut ops := #[]
    for term in terms do
      let op ← interpretNeOp context #[first, term]
      ops := ops.push op

    -- process the other terms and then combine everything using and
    let lastOp ← interpretNeOp context terms
    ops := ops.push lastOp

    andCombine context ops

partial def interpretImpliesOp {v} (context: Context) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
  let ((ante, conse) : BvTermW v × BvTermW v) ← if h: terms.size < 2 then
    Except.error EInterpretation.TooFewOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- consider a => b to work bit-wise:
      -- if some bit in a is set, that bit must also be set in b
      -- the result is whether this holds for all bits
      -- we can rewrite to (a or b) == b, which is true exactly
      -- when there is no bit that is set in a but not set in b
      let ante ← interpretTerm context terms[0]
      let conse ← interpretTerm context terms[1]
      pure (ante, conse)
  else
    -- Implies right-associative, transform (f s_1 s_2 .. s_n) as (f s_1 (f s_2 ... s_n))
    -- still process left-to-right
    let ante ← interpretTerm context (terms[0])
    let conse ← interpretImpliesOp context (terms.eraseIdx 0)
    pure (ante, conse)

  if h1: ante.width = 1 then
    if h2: conse.width = 1 then
      let hAnte := by simp[h1]
      let hConse := by simp[h2]

      let ante: BvTerm v 1 := cast hAnte ante.value
      let conse: BvTerm v 1 := cast hConse conse.value

      let value := BvTerm.Implies ante conse
      pure { width := 1, value }
    else
      Except.error EInterpretation.ImpliesWidthNotOne
  else
    Except.error EInterpretation.ImpliesWidthNotOne


partial def interpretExtOp {v} (context: Context) (op: ExtOp) (addWidth: Nat) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
   -- expecting exactly one term
  match terms with
    | #[inner] =>
      let inner ← interpretTerm context inner
      let combinedWidth := inner.width + addWidth
      pure { width := combinedWidth, value := BvTerm.Extension inner.value combinedWidth op }
    | #[] => Except.error EInterpretation.TooFewOpArgs
    | _ => Except.error EInterpretation.TooManyOpArgs

partial def interpretRepeatOp {v} (context: Context) (times: Nat) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
   -- expecting exactly one term
  match terms with
    | #[inner] =>
      let inner ← interpretTerm context inner
      let totalWidth := inner.width * times
      pure { width := totalWidth, value := BvTerm.Repeat inner.value times }
    | #[] => Except.error EInterpretation.TooFewOpArgs
    | _ => Except.error EInterpretation.TooManyOpArgs


partial def interpretIte {v} (context: Context) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
  -- expecting exactly three terms: condition, then branch, else branch
  match terms with
    | #[condition, thenBranch, elseBranch] =>
      let condition ← interpretTerm context condition
      let thenBranch ← interpretTerm context thenBranch
      let elseBranch ← interpretTerm context elseBranch

      if hCond: 1 = condition.width then
        have hCond : BvTerm v condition.width = BvTerm v 1 := by simp[hCond]
        let condition: BvTerm v 1 := cast hCond condition.value
        if hBranches: thenBranch.width = elseBranch.width then
          have hBranches : BvTerm v elseBranch.width = BvTerm v thenBranch.width := by simp[hBranches]
          let elseBranch: BvTerm v thenBranch.width := cast hBranches elseBranch.value
          pure { width := thenBranch.width, value := BvTerm.Ite condition thenBranch.value elseBranch }
        else
          Except.error EInterpretation.IteBranchWidthMismatch

      else
        Except.error EInterpretation.IteConditionWidthNotOne

    | #[] => Except.error EInterpretation.TooFewOpArgs
    | _ => Except.error EInterpretation.TooManyOpArgs

partial def interpretConcat {v} (context: Context) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do
  match terms with
  | #[left, right] =>
      let left ← interpretTerm context left
      let right ← interpretTerm context right
      let value := BvTerm.Concat left.width right.width left.value right.value
      pure { width := left.width + right.width, value }
  | #[] => Except.error EInterpretation.TooFewOpArgs
  | _ => Except.error EInterpretation.TooManyOpArgs

partial def interpretExtract {v} (context: Context) (hi lo: Nat) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do

  match terms with
  | #[inner] =>
    let inner ← interpretTerm context inner

    if h: hi < inner.width ∧ lo < inner.width ∧ lo ≤ hi then
      let lsb := Fin.mk lo h.right.left
      let newWidth := hi - lo + 1
      let value := BvTerm.Extract inner.value lsb newWidth
      pure { width := newWidth, value }
    else
      Except.error EInterpretation.BadExtraction

  | #[] => Except.error EInterpretation.TooFewOpArgs
  | _ => Except.error EInterpretation.TooManyOpArgs

partial def interpretLetRec {v} (context: Context) (scope: Std.HashMap String8 Nat)
  (bindings: List (String8 × SmtTerm × Option Nat)) (term: SmtTerm)
  : Except EInterpretation (BvTermW v) := do

  match bindings with
  | binding :: bindings =>
    if scope.contains binding.fst then
      Except.error EInterpretation.CollidingLetBinders
    -- compute the bind term
    let bind: BvTermW v ← interpretTerm context binding.snd.fst
    -- test against the expected width if it was provided
    if let some expectedWidth := binding.snd.snd then
      if bind.width != expectedWidth then
        Except.error EInterpretation.BadFunctionArgumentWidth

    -- insert bind to scope and push to variables
    let scope := scope.insert binding.fst v.size
    let vPush := v.push bind.width
    -- recurse
    let innerTerm ← interpretLetRec (v := vPush) context scope bindings term
    -- construct let term
    pure { width := innerTerm.width, value := BvTerm.Let bind.value innerTerm.value }
  | [] =>
    -- push the scope and interpret the term
    interpretTerm { context with scopes := scope :: context.scopes } term

partial def interpretLet {v} (context: Context) (bindings: Array (String8 × SmtTerm)) (term: SmtTerm)
  : Except EInterpretation (BvTermW v) := do
  interpretLetRec context {} (bindings.toList.map λ (name, term) => (name, term, none)) term

partial def intepretApplication {v} (context: Context) (qualified: SmtQualifiedIdent) (terms: Array SmtTerm)
  : (Except EInterpretation) (BvTermW v) := do

  let ident := match qualified with
    | SmtQualifiedIdent.Ident ident => ident

  -- look at functions
  if let some function := context.interpretation.functions.get? ident.name then
    -- unravel the function
    if function.varWidths.size > terms.size then
      Except.error EInterpretation.TooManyOpArgs
    else if function.varWidths.size < terms.size then
      Except.error EInterpretation.TooFewOpArgs

    let bindings := (function.varWidths.zip terms).map λ ((name, width), term) => (name, term, width)

    let innerTerm ← interpretLetRec context {} bindings.toList function.term
    if function.resultWidth != innerTerm.width then
        Except.error EInterpretation.BadFunctionResultWidth
    return innerTerm


  -- all supported application symbols are ASCII
  let nameString ← match ident.name.toString? with
    | some name => pure name
    | none => Except.error (EInterpretation.BadApplication ident.name)

  match ident.indices with
    | #[] => -- no indices
      match nameString with
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
        | "ite" => interpretIte context terms
        | "concat" => interpretConcat context terms
        | _ => Except.error (EInterpretation.BadApplication ident.name)

      | #[index] => -- one index, should be a numeral
          let index ← match index with
            | SmtIndex.Numeral value _ => pure value
            | _ => Except.error (EInterpretation.BadApplication ident.name)

          match nameString with
          | "zero_extend" => interpretExtOp context ExtOp.Uext index terms
          | "sign_extend" => interpretExtOp context ExtOp.Sext index terms
          -- | "rotate_left"
          -- | "rotate_right"
          | "repeat" => interpretRepeatOp context index terms
          | _ => Except.error (EInterpretation.BadApplication ident.name)

      | #[index1, index2] => -- two indices, should be numerals
        let index1 ← match index1 with
          | SmtIndex.Numeral value _ => pure value
          | _ => Except.error (EInterpretation.BadApplication ident.name)
        let index2 ← match index2 with
          | SmtIndex.Numeral value _ => pure value
          | _ => Except.error (EInterpretation.BadApplication ident.name)

        match nameString with
        | "extract" => interpretExtract context index1 index2 terms
        | _ => Except.error (EInterpretation.BadApplication ident.name)


      | _ => Except.error (EInterpretation.BadApplication ident.name)

partial def interpretTerm {v} (context: Context) (term: SmtTerm): Except EInterpretation (BvTermW v) :=
  match term with
  | SmtTerm.SpecialConstant constant => interpretSpecialConstant constant
  | SmtTerm.QualifiedIdent qualified => interpretQualifiedIdent context qualified
  | SmtTerm.Application qualified terms => intepretApplication context qualified terms
  | SmtTerm.Let bindings term => interpretLet context bindings term

end

public def Interpretation.new : Interpretation :=
  { variables := #[], functions := Std.HashMap.emptyWithCapacity, assertions := #[] }

public def Interpretation.declareConst (interpretation: Interpretation)
  (name: String8) (sort: SmtSort) : Except EInterpretation Interpretation := do
    let type ← interpretVariableSort sort
    let variables := interpretation.variables.push (name, type)
    pure {interpretation with variables}

def Interpretation.varWidths (interpretation: Interpretation) : VarWidths :=
  { inner := interpretation.variables.map (λ e => e.snd) }


def Interpretation.globalContext (interpretation: Interpretation) : Context :=
  let varWidths := interpretation.varWidths
    let variableArray := interpretation.variables.mapFinIdx λ index var h =>
      let h: index < varWidths.size := by simp[varWidths, Interpretation.varWidths, VarWidths.size, h]
      (var.fst, index)
    let globalScope := Std.HashMap.ofArray variableArray
    { scopes := [globalScope], interpretation }


public def Interpretation.defineFun  (interpretation: Interpretation)
  (name: String8) (vars: Array (String8 × SmtSort)) (resultSort: SmtSort) (term: SmtTerm)
  : Except EInterpretation Interpretation := do
  let mut varWidths := #[]
  for var in vars do
    let width ← interpretVariableSort var.snd
    varWidths := varWidths.push (var.fst, width)
  let resultWidth ← interpretVariableSort resultSort
  let (duplicate, functions) := interpretation.functions.containsThenInsert name (Function.mk varWidths resultWidth term)
  let interpretation := { interpretation with functions}
  if duplicate then
    Except.error (EInterpretation.DuplicateFunction name)
  else
    pure interpretation


public def Interpretation.assert (interpretation: Interpretation)
  (term: SmtTerm) : Interpretation :=
  { interpretation with assertions := interpretation.assertions.push term}

public def Interpretation.checkSat (interpretation: Interpretation) (proof: SmtProof)
  : IO (Except EInterpretation Unit) := do

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
        SmtTerm.Application (SmtQualifiedIdent.Ident (SmtIdent.simple (String8.fromUTF8 "and"))) interpretation.assertions

  let varWidths: VarWidths := { inner := interpretation.variables.map (λ e => e.snd) }

  let context := interpretation.globalContext

  let term ← match interpretTerm (v := varWidths) context assertion with
    | Except.ok term => pure term
    | Except.error err => return (Except.error err)

  let proof ← match Proof.ofSmt proof varWidths with
    | Except.ok proof => pure proof
    | Except.error err => return (Except.error (EInterpretation.InvalidProof err))

  if h: term.width = 1 then
    have h : BvTerm varWidths term.width = BvTerm varWidths 1 := by simp[h]
    let term: BvTerm varWidths 1 := cast h term.value

    let variables := interpretation.variables.map (λ (var) => var.snd)

    IO.eprintln s!"Checking satisfiability"

    let () ← match checkProof Bitvector3 term proof with
      | Except.ok () => pure ()
      | Except.error err => return (Except.error (EInterpretation.WrongProofCheck err))

    -- print result to standard output as per SMT-LIB2
    if proof.result then
      IO.println "sat"
    else
      IO.println "unsat"

    pure (Except.ok ())
  else
    pure (Except.error EInterpretation.RootWidthNotOne)



instance : Interpret Interpretation EInterpretation where
  new := Interpretation.new
  declareConst := Interpretation.declareConst
  defineFun := Interpretation.defineFun
  assert := Interpretation.assert
  checkSat := Interpretation.checkSat
