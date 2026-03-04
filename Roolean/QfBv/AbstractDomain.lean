module

public import Roolean.QfBv.Domain.Bitvector

public class AbstractDomain (α : Nat → Type) [Domain α] where
  top (w: Nat) : α w
  containsConcrete {w}: α w → Bitvector w → Bool
  split {w}: α w → Nat → (α w × Option (α w))

  top_containsConcrete_all {w} (c: Bitvector w) : containsConcrete (top w) c
  containsConcrete_nonempty {w} (a: α w) : ∃c, containsConcrete a c
  split_noop_id {w} (a b : α w) (n: Nat) : split a n = (b, none) → a = b
  split_preserves {w} (a left right : α w) (n: Nat) (c: Bitvector w)
    : split a n = (left, some right) → containsConcrete a c →
      containsConcrete left c ∨ containsConcrete right c

  uniOp_sound {w} (a: α w) (op: DomainUniOp) (c: Bitvector w)
    : containsConcrete a c → containsConcrete (Domain.uniOp a op) (c.uniOp op)
