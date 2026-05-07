module

public import Roolean.QfBv.Domain.Bitvector3.Basic
import Roolean.QfBv.Domain.Bitvector3.BiNormalOp
import Roolean.QfBv.Domain.Bitvector3.BiNormalOp.Arith

namespace Bitvector3

 --- DEFINITIONS ---

public def uniOp {w} (domain: Bitvector3 w) (op: UniOp)
  : Bitvector3 w :=
  match op with
  | UniOp.Not =>
    -- swap zeros and ones
    let zeros := domain.ones
    let ones := domain.zeros
    let zeros_or_ones_set := by simp[zeros, ones, zeros_or_ones_set, BitVec.or_comm]
    { zeros, ones, zeros_or_ones_set }
  | UniOp.Neg =>
    -- negation is taken from arith
    domain.neg

 --- THEOREMS ---

public theorem uniOp_sound {w} (a: Bitvector3 w) (c: Bitvector w) (op: UniOp)
  : γ a c → γ (a.uniOp op) (c.uniOp op):= by
  simp[uniOp]
  intro h
  split
  { simp[γ] at h; simp[Bitvector.uniOp, γ, h] } -- not
  {
    -- neg
    exact neg_sound a c h
  }
