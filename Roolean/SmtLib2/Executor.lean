module
public import Roolean.SmtLib2.Problem
public import Roolean.SmtLib2.Proof

public class Interpret (α : Type) (ε: outParam Type) where
  new: α
  declareConst: α → String8 → SmtSort → (Except ε α)
  assert : α → SmtTerm → α
  checkSat : α → SmtProof → IO (Except ε Unit)

public inductive EExecutor (ε : Type)
  | UnsupportedLogic (logic: String8)
  | Interpretation (err: ε)
deriving Repr


public def execute (α: Type) {ε: Type} [Interpret α ε] (commands: Array SmtCommand) (proof: SmtProof): IO ((Except (EExecutor ε)) Unit) := do
  let mut interpretation: α := Interpret.new

  for command in commands do
    match command with

      | .SetLogic logic =>
        if logic != String8.fromUTF8 "QF_BV" && logic != String8.fromUTF8 "ALL" then
          return Except.error (EExecutor.UnsupportedLogic logic)

      | .SetInfo _ => pure () -- ignore info

      | .DeclareConst name sort =>
        match Interpret.declareConst interpretation name sort with
          | Except.ok new => interpretation := new
          | Except.error err => return Except.error (EExecutor.Interpretation err)

      | .Assert term =>
        interpretation := Interpret.assert interpretation term

      | .CheckSat =>
        let result ← Interpret.checkSat interpretation proof
        match result with
          | Except.ok () => pure ()
          | Except.error err => return Except.error (EExecutor.Interpretation err)

      | .Exit => break

  pure (Except.ok ())
