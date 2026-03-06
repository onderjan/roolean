module

public structure Bitvector (width: Nat) where
  value: BitVec width
deriving Repr, Inhabited
