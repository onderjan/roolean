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

public structure UniOp where
  public op: UniOperator
  public inner: Formula
deriving Repr

public structure BiOp where
  public op: BiOperator
  public left: Formula
  public right: Formula
deriving Repr

public inductive Operation where
  | Unary (unary: UniOp)
  | Binary (binary: BiOp)
  -- TODO others
/-  | Ext (ext: ExtOp)
  | Ite (ite: IteOp)
  | Concat (concat: ConcatOp)
  | Extract (extract: ExtractOp)
  | Rotate (rotate: RotateOp) -/
deriving Repr

public inductive Formula where
  | Constant (constant: Constant)
  | Variable (index: USize)
  | Operation (operation: Operation)
deriving Repr

end

public def UniOp.new (op: UniOperator) (inner: Formula): UniOp :=
  UniOp.mk op inner

public def BiOp.new (op: BiOperator) (left: Formula) (right: Formula): BiOp :=
  BiOp.mk op left right
