module

public structure BitvectorType where
  width: Nat
deriving Repr, Inhabited

public structure Bitvector (width: Nat) where
  value: BitVec width
deriving Repr, Inhabited
