module

public import Roolean.QfBv.Domain.Bitvector

public class AbstractDomain (α : Type) [Domain α] where
  top: Nat → α
  containsConcrete: α → Bitvector → Bool
  split: α → Nat → (α × Option α)

  top_containsConcrete_all : c.width = w → containsConcrete (top w) c
  containsConcrete_nonempty : ∃x, containsConcrete a x
  split_noop_id : split a n = (b, none) → a = b
  split_preserves : split a n = (left, some right) →
    containsConcrete a c → containsConcrete left c ∨ containsConcrete right c

  uniOp_sound : Domain.uniOp a op = Except.ok ar → containsConcrete a c →
    Bitvector.uniOp c op = Except.ok cr ∧ containsConcrete ar cr
