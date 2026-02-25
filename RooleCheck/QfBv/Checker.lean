module
public import RooleCheck.SmtLib2.String8
public import RooleCheck.QfBv.Formula

public structure BitvectorType where
  width: UInt32
deriving Repr, Inhabited

public structure EChecker
deriving Repr

public structure VarAssignment where
  type: BitvectorType
  value: Nat
deriving Repr, Inhabited

public def checkAssignment (variables: Array BitvectorType) (formula: Formula) (assignment: Nat) : IO (Except EChecker Unit) := do
  IO.println s!"Assignment: {assignment}"

  let mut assignments: Array VarAssignment := #[]
  let mut workingAssignment := assignment

  let _ ← for var in variables do
    let mask := (2 ^ var.width.toNat) - 1
    let value := workingAssignment &&& mask
    workingAssignment := workingAssignment >>> var.width.toNat
    assignments := assignments.push { type := var, value }

  IO.println s!"Assignments: {reprStr assignments}"

  -- let _ ← evaluate formula assignments

  pure (Except.ok ())


public def check (variables: Array BitvectorType) (formula: Formula) : IO (Except EChecker Unit) := do
  IO.println s!"Check satisfiability\nVariables: {reprStr variables}\nFormula: {reprStr formula}"

  let totalWidth: Nat := variables.foldl (λ acc e => acc + e.width.toNat) 0
  let numValues: Nat := 2 ^ totalWidth

  IO.println s!"Num values: {numValues}"

  for assignment in (0...numValues) do
    let checked ← checkAssignment variables formula assignment
    match checked with
      | Except.ok () => pure ()
      | Except.error {} => return Except.error {}


  let mut assignment := Array.replicate variables.size 0
  IO.println s!"Assignment: {assignment}"


  pure (Except.ok ())

#eval (3...7).toList
