import RooleCheck.SmtLib2.Parser
import Std.Data.HashMap.Basic

def load (filename: String): IO (Except EParser (Array SmtCommand)) := do
  let byteArray ← IO.FS.readBinFile filename
  let chars := byteArray.toList
  pure (parse chars)

structure BitvectorType where
  width: UInt32
deriving Repr

structure EExecutor
deriving Repr

def processVariableSort (sort: SmtSort): Except EExecutor BitvectorType :=
  match sort with
    | SmtSort.Ident (SmtIdent.Indexed typename #[width]) =>
      if let some "BitVec" := typename.toString? then
        match width with
          | SmtIndex.Numeral width _width_num_length =>
            if width < UInt32.size then
              pure {width := UInt32.ofNat width}
            else
              Except.error {} -- we support only 32-bit widths
          | _ => Except.error {} -- bitvector width must be a numeral
      else
        Except.error {} -- expected bitvector
    | _ => Except.error {} -- expected bitvector

inductive UniOperator
  | Not
  | Neg
deriving Repr

inductive BiOperator
  | Add
  | Sub
  | Mul
  | Udiv
  | Urem
  | Sdiv
  | Srem
  | BitAnd
  | BitOr
  | BitXor
  | Eq
  | Ne
  | Implies
  | Ult
  | Ule
  | Ugt
  | Uge
  | Slt
  | Sle
  | Sgt
  | Sge
  | Shl
  | Lshr
  | Ashr
deriving Repr

structure Constant where
  value: Nat
  width: UInt32
deriving Repr

mutual

structure UniOp where
  op: UniOperator
  inner: Formula
deriving Repr

structure BiOp where
  op: BiOperator
  left: Formula
  right: Formula
deriving Repr

inductive Operation where
  | Unary (unary: UniOp)
  | Binary (binary: BiOp)
  -- TODO others
/-  | Ext (ext: ExtOp)
  | Ite (ite: IteOp)
  | Concat (concat: ConcatOp)
  | Extract (extract: ExtractOp)
  | Rotate (rotate: RotateOp) -/
deriving Repr

inductive Formula where
  | Constant (constant: Constant)
  | Variable (index: USize)
  | Operation (operation: Operation)
deriving Repr

end

abbrev VariableMap := Std.HashMap String8 USize

-- TODO prove termination
mutual
partial def execSpecialConstant (constant: SmtSpecialConstant)
  : (Except EExecutor) Formula := do
  let (value, width) ← match constant with

    | SmtSpecialConstant.Hexadecimal value numDigits =>
      pure (value, numDigits * 4) -- in hexadecimal, each digit represents 4 bits

    | SmtSpecialConstant.Binary value numDigits =>
      pure (value, numDigits) -- in binary, each digit represents 1 bit

    | _ => Except.error {} -- not a QF_BV constant, decimals can be "constants" only through bvX

  if width < UInt32.size then
    pure (Formula.Constant { value, width := UInt32.ofNat width })
  else
    Except.error {} -- we support only 32-bit widths

partial def execQualifiedIdent (variables: VariableMap) (qualified: SmtQualifiedIdent)
  : IO ((Except EExecutor) Formula) := do

  let name ← match qualified with
  | SmtQualifiedIdent.Ident (SmtIdent.Symbol name) => pure name
  | SmtQualifiedIdent.Ident (SmtIdent.Indexed ..) =>
    return (Except.error {})-- we do not support indexed ident here

  match variables.get? name with
  | some varIndex => pure (Except.ok (Formula.Variable varIndex))
  | none =>
  IO.println "Variable {name} not found"
  pure (Except.error {}) -- variable not found

partial def execUniOp (variables: VariableMap) (op: UniOperator) (terms: Array SmtTerm)
  : IO ((Except EExecutor) Formula) := do
  match terms with
    | #[inner] =>
      let inner ← execTerm variables inner
      match inner with
        | Except.ok inner => pure (Except.ok (Formula.Operation (Operation.Unary { op, inner })))
        | Except.error err => pure (Except.error err) -- error evaluating inner term
    | _ => pure (Except.error {}) -- expected one term

partial def execBiOp (variables: VariableMap) (op: BiOperator) (terms: Array SmtTerm)
  : IO ((Except EExecutor) Formula) := do

  if h: terms.size > 2 then
      -- more than two terms
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
        match left, right with
          | Except.ok left, Except.ok right => pure (Except.ok (Formula.Operation (Operation.Binary { op, left, right })))
          | _,_ => pure (Except.error {}) -- error evaluating inner terms
      | BiOperator.Implies =>
        -- right-associative, transform (f s_1 s_2 .. s_n) as (f s_1 (f s_2 ... s_n))
        -- still process left-to-right
        let left ← execTerm variables (terms[0])
        let right ← execBiOp variables op (terms.eraseIdx 0)
        match left, right with
          | Except.ok left, Except.ok right => pure (Except.ok (Formula.Operation (Operation.Binary { op, left, right })))
          | _,_ => pure (Except.error {}) -- error evaluating inner terms
      | _ => pure (Except.error {}) -- cannot process this operation with more than two terms

  else match terms with
    | #[left, right] =>
      let left ← execTerm variables left
      let right ← execTerm variables right
      match left, right with
        | Except.ok left, Except.ok right => pure (Except.ok (Formula.Operation (Operation.Binary { op, left, right })))
        | _,_ => pure (Except.error {}) -- error evaluating inner terms
    | #[] | #[_] => pure (Except.error {}) -- must have at least two terms
    | _ => pure (Except.error {}) -- expected two terms

partial def execApplication (variables: VariableMap) (qualified: SmtQualifiedIdent) (terms: Array SmtTerm)
  : IO ((Except EExecutor) Formula) := do
  let name ← match qualified with
    | SmtQualifiedIdent.Ident (SmtIdent.Symbol symbol) => pure symbol
    | _ => return Except.error {} -- we only support application symbols

  let name ← match name.toString? with
    | some name => pure name
    | none => return Except.error {} -- must be ASCII

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

    | _ => pure (Except.error {}) -- unknown application

  pure result

partial def execLet (variables: VariableMap) (bindings: Array (String8 × SmtTerm)) (term: SmtTerm)
  : IO (Except EExecutor Formula) := do
  IO.println s!"Let"
  pure (Except.error {}) -- TODO implement

partial def execTerm (variables: VariableMap) (term: SmtTerm): IO ((Except EExecutor) Formula) :=
  match term with
  | SmtTerm.SpecialConstant constant => pure (execSpecialConstant constant)
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
  IO.println s!"Check satisfiability\nVariables: {reprStr variables}\nCombined assertion: {reprStr assertion}"

  let mut variableMap: VariableMap := {}
  let mut index: USize := 0
  for (name, _type) in variables do
    variableMap := variableMap.insert name index
    index := index + 1

  let result ← execTerm variableMap assertion
  match result with
    | Except.ok formula =>
      IO.println s!"CheckSat formula: {reprStr formula}"
      pure (Except.ok ())
    | Except.error err =>
      IO.println s!"CheckSat error: {reprStr err}"
      pure (Except.error err)



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
          return Except.error {}
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

def execute (commands: Array SmtCommand): IO Unit := do
  let executed ← execCommands commands
  match executed with
    | Except.ok () =>
      pure ()
    | Except.error err =>
      IO.println s!"Execution error: {reprStr err}"

def main : IO Unit := do
  let commands ← load "benchmarks/lean.smt2"
  match commands with
    | Except.ok commands =>
      let _executed ← execute commands
    | Except.error err =>
      IO.println s!"Parser error: {reprStr err}"

#eval main
