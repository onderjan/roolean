import RooleCheck.Parser.Parser

def process: IO (Except EParser (Array SmtCommand)) := do
  let string ← IO.FS.readFile "benchmarks/lean.smt2"
  IO.println s!"Read:\n---\n{string}\n---\n"
  let chars := Std.Iter.toList (String.chars string)
  let parsed := parse chars
  pure parsed

def main : IO Unit := do
  let _discard ← process

#eval process
