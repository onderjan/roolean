module

public import Roolean.QfBv.BvTerm
public import Roolean.SmtLib2.Lexer
public import Roolean.SmtLib2.Proof

public inductive Proof.Node (v: VarWidths)
  | Relevant
  | Irrelevant
  | Split (varIndex: Fin v.size) (bitIndex: Fin (v.varWidth varIndex))
    (left: Proof.Node v) (right: Proof.Node v)
deriving Repr

public structure Proof (v: VarWidths) where
  result: Bool
  root: Proof.Node v

namespace Proof

public inductive EOfSmt
  | BadVarIndex
  | BadBitIndex
deriving Repr

public def Node.ofSmt (n: SmtNode) (v: VarWidths) : Except EOfSmt (Node v) := do
  match n with
  | .Relevant => pure Node.Relevant
  | .Irrelevant => pure Node.Irrelevant
  | .Split varIndex bitIndex left right =>
    if hVarIndex: varIndex < v.size then
      let varIndex := Fin.mk varIndex hVarIndex
      if hBitIndex: bitIndex < v.varWidth varIndex then
        let bitIndex := (Fin.mk bitIndex hBitIndex)
        let left ← Node.ofSmt left v
        let right ← Node.ofSmt right v
        pure (Node.Split varIndex bitIndex left right)

      else
        Except.error EOfSmt.BadBitIndex
    else
      Except.error EOfSmt.BadVarIndex

public def ofSmt (proof: SmtProof) (v: VarWidths) : Except EOfSmt (Proof v) := do
  let root ← Node.ofSmt proof.root v
  pure { result := proof.result, root }
