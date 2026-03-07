module

public import Roolean.QfBv.Bitvector

public inductive UniOp
  | Not
  | Neg
deriving Repr, Inhabited

public inductive BiNormalOp
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

public inductive BiReductionOp
  | Eq
  | Ult
  | Ule
  | Slt
  | Sle
deriving Repr, Inhabited


public class Domain (α: Nat → Type) where
  ofBitvector {w}: Bitvector w → α w
  toBitvector? {w}: α w → Option (Bitvector w)

  uniOp {w}: α w → UniOp → α w
  biNormal{w}: α w → α w → BiNormalOp → α w
  biReduction {w}: α w → α w → BiReductionOp → α 1

  fmt {w}: α w → String
