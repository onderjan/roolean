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

public def VarWidths.varWidth (v: VarWidths) (index: USize) :=
  match v.inner[index]? with
  | some width => width
  | none => 0

public def VarWidths.usize (v: VarWidths) :=
  v.inner.usize

public inductive Formula (v: VarWidths): Nat → Type where
  | Constant: {w: Nat} → Bitvector w → Formula v w
  | Variable: (i : {a: USize // a < v.usize}) → Formula v (VarWidths.varWidth v i)
  | Unary: {w: Nat} → Formula v w → UniOp → Formula v w
  | BinaryNormal: {w: Nat} → Formula v w → Formula v w → BiNormalOp → Formula v w
  | BinaryReduction: {w: Nat} → Formula v w → Formula v w → BiReductionOp → Formula v 1
deriving Repr, Nonempty
