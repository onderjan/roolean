import Roolean.SmtLib2.Executor
import Roolean.QfBv.Interpretation

def work (problem proof: String): IO Unit := do
  let problem ← IO.FS.readBinFile problem
  let proof ← IO.FS.readBinFile proof

  let proof ← match Proof.parse proof.toList with
  | Except.ok proof => pure proof
  | Except.error err =>
    throw (IO.userError s!"Proof parsing error: {reprStr err}")

  let commands := parse problem.toList
  match commands with
    | Except.ok commands =>
      -- IO.println s!"Parsed commands: {reprStr commands}"
      let executed ← execute Interpretation commands proof
      match executed with
        | Except.ok () =>
          IO.eprintln s!"Execution successful"
          pure ()
        | Except.error err =>
          throw (IO.userError s!"Execution error: {reprStr err}")

    | Except.error err =>
      throw (IO.userError s!"Problem parsing error: {reprStr err}")

def main (args: List String) : IO UInt32 := do
  let (problem, proof) ← match args with
    | [problem, proof] => pure (problem, proof)
    | _ =>
      IO.eprintln "Usage: roolean [problem] [proof]"
      return 101

  try
    work problem proof; pure 0
  catch
    | .userError string => IO.eprintln string; pure 101
    | other => throw other
