import Roolean.SmtLib2.Executor
import Roolean.QfBv.Interpretation

def work (problem proof: String): IO Unit := do
  let proof ← (Proof.parse proof).toIO (λ e => IO.userError s!"Proof parsing error: {reprStr e}")
  let commands ← (Problem.parse problem).toIO (λ e => IO.userError s!"Problem parsing error: {reprStr e}")

  let executed ← execute Interpretation commands proof
  match executed with
    | Except.ok () =>
      IO.eprintln s!"Execution successful"
      pure ()
    | Except.error err =>
      throw (IO.userError s!"Execution error: {reprStr err}")


def main (args: List String) : IO UInt32 := do
  let startTime ← IO.monoMsNow
  let (problem, proof) ← match args with
    | [problem, proof] => pure (problem, proof)
    | _ =>
      IO.eprintln "Usage: roolean [problem] [proof]"
      return 101

  try
    work problem proof
    let endTime ← IO.monoMsNow
    IO.eprintln s!"Roolean finished in {endTime-startTime} ms"
    pure 0
  catch
    | .userError string =>
      let endTime ← IO.monoMsNow
      IO.eprintln s!"Roolean error in {endTime-startTime} ms"
      IO.eprintln string; pure 101
    | other => throw other
