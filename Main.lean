import RooleCheck.SmtLib2.Parser
import Std.Data.HashMap.Basic

def load (filename: String): IO (Except EParser (Array SmtCommand)) := do
  let string ← IO.FS.readFile filename
  IO.println s!"Read:\n---\n{string}\n---\n"
  let chars := Std.Iter.toList (String.chars string)
  pure (parse chars)

structure BitvectorType where
  width: UInt32
deriving Repr

structure EExecutor
deriving Repr

def processVariableType (sort: SmtSort): Except EExecutor BitvectorType :=
  match sort with
    | SmtSort.Ident (SmtIdent.Indexed "BitVec" #[width]) =>
      match width with
        | SmtIndex.Numeral width =>
          if width < UInt32.size then
            pure {width := UInt32.ofNat width}
          else
            Except.error {} -- we support only 32-bit widths
        | _ => Except.error {} -- bitvector width must be a numeral
    | _ => Except.error {} -- expected bitvector

def execCheckSat (variables: Std.HashMap String BitvectorType) (assertions: Array SmtTerm) := do
  IO.println s!"Check satisfiability\nVariables: {reprStr variables}\nAssertions: {reprStr assertions}"


def execCommands (commands: Array SmtCommand): IO ((Except EExecutor) Unit) := do
  let mut qf_bv := false
  let mut variables: Std.HashMap String BitvectorType := {}
  let mut assertions: Array SmtTerm := {}

  for command in commands do
    match command with
      | .SetLogic logic =>
        if logic == "QF_BV" || logic == "ALL" then
          qf_bv := true
        else
          return Except.error {}
      | .SetInfo _ => continue -- ignore info
      | .DeclareConst name sort =>
        match processVariableType sort with
          | Except.ok type => variables := variables.insert name type
          | Except.error err => return Except.error err
      | .Assert term => assertions := assertions.push term
      | .CheckSat => execCheckSat variables assertions
      | .Exit => break
  pure (Except.ok ())

def execute (commands: Array SmtCommand): IO Unit := do
  let executed ← execCommands commands
  match executed with
    | Except.ok () =>
      pure ()
    | Except.error err =>
      IO.println s!"Execution error: {reprStr err}"

def main : IO Unit := do
  let commands ← load "benchmarks/lean.smt2"
  match commands with
    | Except.ok commands =>
      let _executed ← execute commands
    | Except.error err =>
      IO.println s!"Parser error: {reprStr err}"

#eval main
