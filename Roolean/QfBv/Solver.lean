module

public import Roolean.QfBv.Checker

public def solve {v: VarWidths} (α) [Domain α] [AbstractDomain α]
  (term: BvTerm v 1) : Option Bool := do
  -- brute-force by splitting everything
  let splitTree: Proof.Node v := Fin.foldl v.size (λ (splitTree: Proof.Node v) varIndex =>
    Fin.foldl (v.varWidth varIndex) (λ splitTree bitIndex =>
        Proof.Node.Split varIndex bitIndex splitTree splitTree) splitTree
    ) Proof.Node.Relevant

  computeSat α term splitTree
