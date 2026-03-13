module
public import Roolean.QfBv.Domain.ThreeValued.Basic
public import Roolean.QfBv.Domain.ThreeValued.Split
public import Roolean.QfBv.Domain.ThreeValued.Ops

public instance : Domain Bitvector3 where
  ofBitvector := Bitvector3.ofBitvector
  toBitvector? := Bitvector3.toBitvector?

  uniOp := Bitvector3.uniOp
  biNormal := Bitvector3.biNormal
  biReduction := Bitvector3.biReduction

  fmt := Bitvector3.fmt

public instance : AbstractDomain Bitvector3 where
  top := Bitvector3.allUnknown
  split := Bitvector3.split
  γ := Bitvector3.γ
  choice := Bitvector3.choice

  top_γ_all := Bitvector3.top_γ_all
  split_comprises := Bitvector3.split_comprises
  split_within := Bitvector3.split_within

  uniOp_sound := Bitvector3.uniOp_sound
  biNormal_sound := Bitvector3.biNormal_sound
  biReduction_sound := Bitvector3.biReduction_sound

  ofBitvector_sound := Bitvector3.ofBitvector_sound
  toBitvector?_sound := Bitvector3.toBitvector?_sound
