import Roolean.QfBv.Executor


def load (filename: String): IO (Except EParser (Array SmtCommand)) := do
  let byteArray ← IO.FS.readBinFile filename
  let chars := byteArray.toList

  pure (parse chars)


def main : IO Unit := do
  let commands ← load "benchmarks/lean.smt2"
  match commands with
    | Except.ok commands =>
      -- IO.println s!"Parsed commands: {reprStr commands}"
      let _executed ← execute commands
    | Except.error err =>
      IO.println s!"Parser error: {reprStr err}"

#eval main
