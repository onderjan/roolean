module
import Roolean.QfBv.Formula
import Std.Data.HashMap.Basic
import Roolean.QfBv.Checker
public import Roolean.SmtLib2.Parser


inductive EExecutor
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

def processVariableSort (sort: SmtSort): Except EExecutor BitvectorType :=
  match sort with
    | SmtSort.Ident (SmtIdent.Indexed typename #[width]) =>
      if let some "BitVec" := typename.toString? then
        match width with
          | SmtIndex.Numeral width _width_num_length =>
            pure {width := width}
          | _ =>
            -- bitvector width must be a numeral
            Except.error EExecutor.BitvectorWidthNotNumeral
      else
        Except.error EExecutor.SortNotBitVec -- expected a bitvector
    | _ =>
      -- expected a bitvector, which is a sort indexed by width
      Except.error EExecutor.SortNotBitVec


abbrev VariableMap := Std.HashMap String8 USize

def execSpecialConstant (constant: SmtSpecialConstant)
  : (Except EExecutor) Formula := do
  let (value, width) ← match constant with

    | SmtSpecialConstant.Hexadecimal value numDigits =>
      pure (value, numDigits * 4) -- in hexadecimal, each digit represents 4 bits

    | SmtSpecialConstant.Binary value numDigits =>
      pure (value, numDigits) -- in binary, each digit represents 1 bit

    | _ =>
      -- not a QF_BV constant, decimals can be "constants" only through bvX
      Except.error EExecutor.InvalidSpecialConstant

  pure (Formula.Constant { value, width })


def execQualifiedIdent (variables: VariableMap) (qualified: SmtQualifiedIdent)
  : (Except EExecutor) Formula := do

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
            Except.error (EExecutor.InvalidDecimalBitvec name)
      else
        -- we do not support indexed idents other than bvX where X is a decimal
        Except.error EExecutor.InvalidIndexedQualifiedIdent
    else
      -- we do not support indexed idents other than bvX
      Except.error EExecutor.InvalidIndexedQualifiedIdent

  match variables.get? name with
  | some varIndex => pure (Formula.Variable varIndex)
  | none =>
    -- variable with the given name not found
    Except.error (EExecutor.VariableNotFound name)


-- TODO prove termination
mutual
partial def execUniOp (variables: VariableMap) (op: UniOperator) (terms: Array SmtTerm)
  : (Except EExecutor) Formula := do
   -- expecting exactly one term
  match terms with
    | #[inner] =>
      let inner ← execTerm variables inner
      pure (Formula.Operation (Operation.Unary op inner))
    | #[] => Except.error EExecutor.TooFewUniOpArgs
    | _ => Except.error EExecutor.TooManyUniOpArgs

partial def execBiOp (variables: VariableMap) (op: BiOperator) (terms: Array SmtTerm)
  : (Except EExecutor) Formula := do

  let construct (op) (left) (right) :=
    pure (Formula.Operation (Operation.Binary op left right))

  if h: terms.size < 2 then
    Except.error EExecutor.TooFewBiOpArgs -- must have at least two args
  else if terms.size == 2 then
      -- exactly two args, evaluate normally
      let left ← execTerm variables terms[0]
      let right ← execTerm variables terms[1]
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
        let left ← execBiOp variables op (terms.pop)
        let right ← execTerm variables rightTerm
        construct op left right
      | BiOperator.Implies =>
        -- right-associative, transform (f s_1 s_2 .. s_n) as (f s_1 (f s_2 ... s_n))
        -- still process left-to-right
        let left ← execTerm variables (terms[0])
        let right ← execBiOp variables op (terms.eraseIdx 0)
        construct op left right
      | _ =>
        -- cannot process this operation with more than two terms
        Except.error EExecutor.TooManyBiOpArgs



partial def execApplication (variables: VariableMap) (qualified: SmtQualifiedIdent) (terms: Array SmtTerm)
  : (Except EExecutor) Formula := do

  -- all supported applications are just symbols
  let name ← match qualified with
    | SmtQualifiedIdent.Ident (SmtIdent.Symbol symbol) => pure symbol
    | _ => Except.error EExecutor.UnsupportedApplication

  -- all supported application symbols are ASCII
  let name ← match name.toString? with
    | some name => pure name
    | none => Except.error EExecutor.UnsupportedApplication

  let result ← match name with
    | "not" | "bvnot" => execUniOp variables UniOperator.Not terms
    | "bvneg" => execUniOp variables UniOperator.Neg terms

    | "=" | "bvcomp" => execBiOp variables BiOperator.Eq terms
    | "distinct" => execBiOp variables BiOperator.Ne terms
    | "=>" => execBiOp variables BiOperator.Implies terms

    | "bvult" => execBiOp variables BiOperator.Ult terms
    | "bvule" => execBiOp variables BiOperator.Ule terms
    | "bvugt" => execBiOp variables BiOperator.Ugt terms
    | "bvuge" => execBiOp variables BiOperator.Uge terms

    | "bvslt" => execBiOp variables BiOperator.Slt terms
    | "bvsle" => execBiOp variables BiOperator.Sle terms
    | "bvsgt" => execBiOp variables BiOperator.Sgt terms
    | "bvsge" => execBiOp variables BiOperator.Sge terms

    | "bvadd" => execBiOp variables BiOperator.Add terms
    | "bvsub" => execBiOp variables BiOperator.Sub terms
    | "bvmul" => execBiOp variables BiOperator.Mul terms
    | "bvudiv" => execBiOp variables BiOperator.Udiv terms
    | "bvurem" => execBiOp variables BiOperator.Urem terms
    | "bvsdiv" => execBiOp variables BiOperator.Sdiv terms
    | "bvsrem" => execBiOp variables BiOperator.Srem terms

    | "and" | "bvand" => execBiOp variables BiOperator.BitAnd terms
    | "or" | "bvor" => execBiOp variables BiOperator.BitOr terms
    | "xor" | "bvxor" => execBiOp variables BiOperator.BitXor terms

    | "bvshl" => execBiOp variables BiOperator.Shl terms
    | "bvlshr" => execBiOp variables BiOperator.Lshr terms
    | "bvashr" => execBiOp variables BiOperator.Ashr terms

     -- TODO
     -- | "ite"
     -- | "concat"
     -- | "rotate_left"
     -- | "rotate_right"
     -- | "zero_extend"
     -- | "sign_extend"
     -- | "extract"

    | _ => Except.error EExecutor.UnsupportedApplication

  pure result

partial def execLet (variables: VariableMap) (bindings: Array (String8 × SmtTerm)) (term: SmtTerm)
  : Except EExecutor Formula := do
  Except.error EExecutor.LetNotImplemented -- TODO implement

partial def execTerm (variables: VariableMap) (term: SmtTerm): (Except EExecutor) Formula :=
  match term with
  | SmtTerm.SpecialConstant constant => execSpecialConstant constant
  | SmtTerm.QualifiedIdent qualified => execQualifiedIdent variables qualified
  | SmtTerm.Application qualified terms => execApplication variables qualified terms
  | SmtTerm.Let bindings term => execLet variables bindings term

end

def execCheckSat (variables: Array (String8 × BitvectorType)) (assertions: Array SmtTerm): IO (Except EExecutor Unit) := do
  -- combine assertions
  let assertion := if assertions.isEmpty then
    SmtTerm.SpecialConstant (SmtSpecialConstant.String (String8.fromUTF8 "true"))
  else
    SmtTerm.Application (SmtQualifiedIdent.Ident (SmtIdent.Symbol (String8.fromUTF8 "and"))) assertions
  -- IO.println s!"Check satisfiability\nVariables: {reprStr variables}\nCombined assertion: {reprStr assertion}"

  let mut variableMap: VariableMap := {}
  let mut index: USize := 0
  for (name, _type) in variables do
    variableMap := variableMap.insert name index
    index := index + 1

  let formula ← match execTerm variableMap assertion with
    | Except.ok formula => pure formula
    | Except.error err => return (Except.error err)

  let variables := variables.map (λ (var) => var.snd)

  let checked ← check variables formula
  match checked with
    | Except.ok () => pure (Except.ok ())
    | Except.error err => pure (Except.error (EExecutor.Checker err))


def execCommands (commands: Array SmtCommand): IO ((Except EExecutor) Unit) := do
  let mut qf_bv := false
  let mut variables: Array (String8 × BitvectorType) := {}
  let mut assertions: Array SmtTerm := {}

  for command in commands do
    match command with
      | .SetLogic logic =>
        if logic == String8.fromUTF8 "QF_BV" || logic == String8.fromUTF8 "ALL" then
          qf_bv := true
        else
          return Except.error (EExecutor.UnsupportedLogic logic)
      | .SetInfo _ => continue -- ignore info
      | .DeclareConst name sort =>
        match processVariableSort sort with
          | Except.ok type => variables := variables.push (name, type)
          | Except.error err => return Except.error err
      | .Assert term => assertions := assertions.push term
      | .CheckSat =>
        let result ← execCheckSat variables assertions
        match result with
          | Except.ok () => pure ()
          | Except.error err => return Except.error err

      | .Exit => break
  pure (Except.ok ())

public def execute (commands: Array SmtCommand): IO Unit := do
  let executed ← execCommands commands
  match executed with
    | Except.ok () =>
      pure ()
    | Except.error err =>
      IO.println s!"Execution error: {reprStr err}"
