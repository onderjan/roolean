module

public import Roolean.QfBv.Bitvector
public import Roolean.QfBv.Domain

public inductive Primary (w: Nat) where
  | Constant (constant: Bitvector w)
  | Variable (index: USize)
deriving Repr, Inhabited

public inductive Formula: Nat → Type where
  | Leaf: {n: Nat} → Primary n → Formula n
  | Unary: {n: Nat} → Formula n → UniOp → Formula n
  | BinaryNormal: {n: Nat} → Formula n → Formula n → BiNormalOp → Formula n
  | BinaryReduction: {n: Nat} → Formula n → Formula n → BiReductionOp → Formula 1
deriving Repr, Nonempty


/-
  | Constant (w: Nat) (constant: Bitvector w)
  | Variable (index: USize)
  | Unary (op: UniOperator) (inner: Formula w)
  | Binary (op: BiOperator) (a: Nat) (left: Formula a) (right: Formula a)
-/
--deriving Repr, Inhabited
