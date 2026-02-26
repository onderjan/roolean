import Roolean.SmtLib2.Executor
import Roolean.QfBv.Interpretation


def load (filename: String): IO (Except EParser (Array SmtCommand)) := do
  let byteArray ← IO.FS.readBinFile filename
  let chars := byteArray.toList

  pure (parse chars)

def main : IO Unit := do
  let commands ← load "benchmarks/lean.smt2"
  match commands with
    | Except.ok commands =>
      -- IO.println s!"Parsed commands: {reprStr commands}"
      let executed ← execute Interpretation commands
      match executed with
        | Except.ok () =>
          IO.println s!"Execution successful"
          pure ()
        | Except.error err =>
          IO.println s!"Execution error: {reprStr err}"

    | Except.error err =>
      IO.println s!"Parser error: {reprStr err}"

#eval main
