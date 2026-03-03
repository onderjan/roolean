module

public import Roolean.QfBv.Bitvector

public class Domain (α: Type) where
  ε: Type

  ofBitvector: Bitvector → α
  toBitvector?: α → Option Bitvector
  width: α → Nat

  not: α → Except ε α
  neg: α → Except ε α

  add: α → α → Except ε α
  sub: α → α → Except ε α
  mul: α → α → Except ε α
  udiv: α → α → Except ε α
  urem: α → α → Except ε α
  sdiv: α → α → Except ε α
  srem: α → α → Except ε α

  bitAnd: α → α → Except ε α
  bitOr: α → α → Except ε α
  bitXor: α → α → Except ε α

  eq: α → α → Except ε α
  ult: α → α → Except ε α
  ule: α → α → Except ε α
  slt: α → α → Except ε α
  sle: α → α → Except ε α

  shl: α → α → Except ε α
  lshr: α → α → Except ε α
  ashr: α → α → Except ε α


public class AbstractDomain (α : Type) [Domain α] where
  top: Nat → α
  containsConcrete: α → Bitvector → Bool
  split: α → Nat → (α × Option α)

  containsConcrete_nonempty {a: α} : ∃x, containsConcrete a x
  split_noop_id : split a n = (b, none) → a = b
  split_preserves : split a n = (left, some right) →
    containsConcrete a c → containsConcrete left c ∨ containsConcrete right c
