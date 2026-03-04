module

public import Roolean.QfBv.Bitvector

public inductive UniOperator
  | Not
  | Neg
deriving Repr, Inhabited

public inductive BiOperator
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
  | Eq
  | Ne
  | Implies
  | Ult
  | Ule
  | Ugt
  | Uge
  | Slt
  | Sle
  | Sgt
  | Sge
  | Shl
  | Lshr
  | Ashr
deriving Repr, Inhabited

mutual

public inductive Formula where
  | Constant (w: Nat) (constant: Bitvector w)
  | Variable (index: USize)
  | Operation (operation: Operation)
deriving Repr, Inhabited

public inductive BiOp where
  | Mk (op: BiOperator) (left: Formula) (right: Formula)
deriving Repr, Inhabited

public inductive Operation where
  | Unary (op: UniOperator) (inner: Formula)
  | Binary (op: BiOperator) (left: Formula) (right: Formula)
  -- TODO others
/-  | Ext (ext: ExtOp)
  | Ite (ite: IteOp)
  | Concat (concat: ConcatOp)
  | Extract (extract: ExtractOp)
  | Rotate (rotate: RotateOp) -/
deriving Repr, Inhabited

end

public structure Problem where
  public variables: Array BitvectorType
  public formula: Formula
deriving Repr, Inhabited
