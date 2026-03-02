module

public structure BitvectorType where
  width: Nat
deriving Repr, Inhabited

public structure Bitvector where
  width: Nat
  value: BitVec width
deriving Repr, Inhabited
