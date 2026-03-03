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


public class AbstractDomain (α : Type) [Domain α] where
  top: Nat → α
  containsConcrete: α → Bitvector → Bool
  split: α → Nat → (α × Option α)

  top_containsConcrete_all{w: Nat} {c: Bitvector} : c.width = w → containsConcrete (top w) c
  containsConcrete_nonempty {a: α} : ∃x, containsConcrete a x
  split_noop_id : split a n = (b, none) → a = b
  split_preserves : split a n = (left, some right) →
    containsConcrete a c → containsConcrete left c ∨ containsConcrete right c
