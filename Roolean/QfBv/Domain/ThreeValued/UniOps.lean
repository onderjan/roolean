module

public import Roolean.QfBv.Domain.ThreeValued.Basic
import Roolean.QfBv.Domain.Bitvector
import Roolean.QfBv.Domain.ThreeValued.BiNormalOps
import Roolean.QfBv.Domain.ThreeValued.Basic

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
    -- compute as 0 - domain
    biNormal (Bitvector3.allZeros (w:=w)) domain BiNormalOp.Sub

 --- THEOREMS ---

public theorem uniOp_sound {w} (a: Bitvector3 w) (c: Bitvector w) (op: UniOp)
  : γ a c → γ (a.uniOp op) (c.uniOp op):= by
  simp[uniOp]
  intro h
  split
  { simp[γ] at h; simp[Bitvector.uniOp, γ, h] } -- not
  {
    -- neg
    let z := Bitvector3.allZeros w
    let cz := Bitvector.allZeros w

    let hSound := biNormal_sound z a BiNormalOp.Sub cz c
    let hSound := hSound (allZeros_contains w) h

    simp[z, cz, Bitvector.biNormal, Bitvector.standardBi, Bitvector.allZeros] at hSound
    simp[Bitvector.uniOp, hSound]
  }
