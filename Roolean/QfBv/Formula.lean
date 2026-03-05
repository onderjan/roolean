module

public import Roolean.QfBv.Bitvector
public import Roolean.QfBv.Domain

public inductive Primary (w: Nat) where
  | Constant (constant: Bitvector w)
  | Variable (index: USize)
deriving Repr, Inhabited

public structure VarWidths where
  inner: Array Nat
deriving Repr

public def VarWidths.width (v: VarWidths) (index: USize) :=
  match v.inner[index]? with
  | some width => width
  | none => 0

public def VarWidths.size (v: VarWidths) :=
  v.inner.usize

public inductive Formula (v: VarWidths): Nat → Type where
  | Constant: {w: Nat} → Bitvector w → Formula v w
  | Variable: (a: USize) → Formula v (VarWidths.width v a)
  | Unary: {w: Nat} → Formula v w → UniOp → Formula v w
  | BinaryNormal: {w: Nat} → Formula v w → Formula v w → BiNormalOp → Formula v w
  | BinaryReduction: {w: Nat} → Formula v w → Formula v w → BiReductionOp → Formula v 1
deriving Repr, Nonempty


/-
  | Constant (w: Nat) (constant: Bitvector w)
  | Variable (index: USize)
  | Unary (op: UniOperator) (inner: Formula w)
  | Binary (op: BiOperator) (a: Nat) (left: Formula a) (right: Formula a)
-/
--deriving Repr, Inhabited
