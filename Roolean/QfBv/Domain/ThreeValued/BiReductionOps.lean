module

public import Roolean.QfBv.Domain.ThreeValued.Basic
import Roolean.QfBv.Domain.Bitvector

namespace Bitvector3

 --- DEFINITIONS ---

public def biReduction {w} (left: Bitvector3 w) (right: Bitvector3 w) (op: BiReductionOp)
  : Bitvector3 1 :=
  match left.toBitvector?, right.toBitvector? with
  | some left, some right =>
    let result := Bitvector.biReduction left right op
    ofBitvector result
  | _, _ =>
      allUnknown 1

 --- THEOREMS ---

public theorem biReduction_sound {w} (a b: Bitvector3 w) (op: BiReductionOp) (ca cb: Bitvector w)
    : γ a ca → γ b cb
      → γ (biReduction a b op) (Domain.biReduction ca cb op) := by
  intro ha hb
  simp[biReduction]
  split
  {
    rename_i hA hB hAto hBto
    rw[Eq.comm] at hAto;rw[Eq.comm] at hBto
    let h5 := Iff.mp (toBitvector?_sound (w:=w) a hA ca hAto) ha
    let h6 := Iff.mp (toBitvector?_sound (w:=w) b hB cb hBto) hb
    simp[γ_ofBitvector, h5,h6]
    trivial
  }
  { apply γ_allUnknown }
