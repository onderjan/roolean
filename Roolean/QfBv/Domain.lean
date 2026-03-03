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


public class Domain (α: Type) where
  ε: Type

  ofBitvector: Bitvector → α
  toBitvector?: α → Option Bitvector
  width: α → Nat

  uniOp: α → DomainUniOp → Except ε α
  biNormal: α → α → DomainBiNormalOp → Except ε α
  biReduction: α → α → DomainBiReductionOp → Except ε α
