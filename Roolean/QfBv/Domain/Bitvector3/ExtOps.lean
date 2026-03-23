module

public import Roolean.QfBv.Domain.Bitvector3.Basic
import Roolean.QfBv.Domain.Bitvector3.BiNormalOps

namespace Bitvector3

 --- DEFINITIONS ---

public def extOp {w} (domain: Bitvector3 w) (newWidth: Nat) (op: ExtOp) : Bitvector3 newWidth :=
  match op with
  | .Uext =>
    sorry
  | .Sext =>
    sorry

 --- THEOREMS ---

public theorem extOp_sound {w} (a: Bitvector3 w) (c: Bitvector w) (m: Nat) (op: ExtOp)
  : γ a c → γ (a.extOp m op) (c.extOp m op):= by
  sorry
