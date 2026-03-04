module

public import Roolean.QfBv.Bitvector

public inductive DomainUniOp
  | Not
  | Neg
deriving Repr, Inhabited

public inductive DomainBiNormalOp
  | Add
  | Sub
  | Mul
  | Udiv
  | Urem
  | Sdiv
  | Srem

  | BitAnd
  | BitOr
  | BitXor

  | Shl
  | Lshr
  | Ashr
deriving Repr, Inhabited

public inductive DomainBiReductionOp
  | Eq
  | Ult
  | Ule
  | Slt
  | Sle
deriving Repr, Inhabited


public class Domain (α: Nat → Type) where
  cast {w m} (h: w = m): α w → α m

  ofBitvector {w}: Bitvector w → α w
  toBitvector? {w}: α w → Option (Bitvector w)

  uniOp {w}: α w → DomainUniOp → α w
  biNormal{w}: α w → α w → DomainBiNormalOp → α w
  biReduction {w}: α w → α w → DomainBiReductionOp → α 1
