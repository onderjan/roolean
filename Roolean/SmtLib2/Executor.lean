module
public import Roolean.SmtLib2.Parser
public import Roolean.QfBv.Interpretation

public inductive EExecutor
  | UnsupportedLogic (logic: String8)
  | Interpretation (err: EInterpretation)
deriving Repr

public def execute (commands: Array SmtCommand): IO ((Except EExecutor) Unit) := do
  let mut interpretation: Interpretation := Interpretation.new

  for command in commands do
    match command with

      | .SetLogic logic =>
        if logic != String8.fromUTF8 "QF_BV" && logic != String8.fromUTF8 "ALL" then
          return Except.error (EExecutor.UnsupportedLogic logic)

      | .SetInfo _ => pure () -- ignore info

      | .DeclareConst name sort =>
        match interpretation.declareConst name sort with
          | Except.ok new => interpretation := new
          | Except.error err => return Except.error (EExecutor.Interpretation err)

      | .Assert term =>
        interpretation := interpretation.assert term

      | .CheckSat =>
        let result ← interpretation.checkSat
        match result with
          | Except.ok () => pure ()
          | Except.error err => return Except.error (EExecutor.Interpretation err)

      | .Exit => break

  pure (Except.ok ())
