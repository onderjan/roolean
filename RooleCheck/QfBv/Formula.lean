module

public inductive UniOperator
  | Not
  | Neg
deriving Repr

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
deriving Repr

public structure Constant where
  value: Nat
  width: UInt32
deriving Repr

mutual

public inductive Formula where
  | Constant (constant: Constant)
  | Variable (index: USize)
  | Operation (operation: Operation)
deriving Repr

public inductive BiOp where
  | Mk (op: BiOperator) (left: Formula) (right: Formula)
deriving Repr

public inductive Operation where
  | Unary (op: UniOperator) (inner: Formula)
  | Binary (op: BiOperator) (left: Formula) (right: Formula)
  -- TODO others
/-  | Ext (ext: ExtOp)
  | Ite (ite: IteOp)
  | Concat (concat: ConcatOp)
  | Extract (extract: ExtractOp)
  | Rotate (rotate: RotateOp) -/
deriving Repr

end
