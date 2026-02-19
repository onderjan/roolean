import RooleCheck.Parser.Lexer


def process: IO (Except ELexer (List Token)) := do
  let string ← IO.FS.readFile "benchmarks/lean.smt2"
  IO.println s!"Read:\n---\n{string}\n---\n"
  let chars := Std.Iter.toList (String.chars string)
  let lexed := lex chars
  pure lexed

def main : IO Unit := do
  let _discard ← process

 #eval process
