import Roolean.SmtLib2.Executor
import Roolean.QfBv.Interpretation

def main : IO Unit := do
  let problem ← IO.FS.readBinFile "benchmarks/lean.smt2"
  let proof ← IO.FS.readBinFile "benchmarks/lean.proof"

  let proof ← match Proof.parse proof.toList with
  | Except.ok proof => pure proof
  | Except.error err =>
    IO.println s!"Proof parsing error: {reprStr err}"
    return

  let commands := parse problem.toList
  match commands with
    | Except.ok commands =>
      -- IO.println s!"Parsed commands: {reprStr commands}"
      let executed ← execute Interpretation commands proof
      match executed with
        | Except.ok () =>
          IO.println s!"Execution successful"
          pure ()
        | Except.error err =>
          IO.println s!"Execution error: {reprStr err}"

    | Except.error err =>
      IO.println s!"Problem parsing error: {reprStr err}"

#eval main
