module
public import RooleCheck.SmtLib2.String8
public import RooleCheck.QfBv.Formula

public structure BitvectorType where
  width: UInt32
deriving Repr

public structure EChecker
deriving Repr

public def check (variables: Array BitvectorType) (formula: Formula) : IO (Except EChecker Unit) := do
  IO.println s!"Check satisfiability\nVariables: {reprStr variables}\nFormula: {reprStr formula}"
  pure (Except.ok ())
