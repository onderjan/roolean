module

public import Roolean.QfBv.Formula
public import Roolean.QfBv.Domain
import Roolean.QfBv.Evaluator

public structure ConcreteDomain where
  bv: Bitvector
deriving Repr

public inductive EConcreteDomain
  | BinaryWidthMismatch (left: ConcreteDomain) (right: ConcreteDomain)
deriving Repr


public def ConcreteDomain.ofBitvector (bitvector: Bitvector) : ConcreteDomain :=
  { bv := bitvector }

public def ConcreteDomain.toBitvector? (inner: ConcreteDomain) : Option Bitvector :=
  some inner.bv

public def ConcreteDomain.not (inner: ConcreteDomain) : Except EConcreteDomain ConcreteDomain :=
  let value := ~~~inner.bv.value
  pure { bv := { value := value.toNat, width := inner.bv.width } }

public def ConcreteDomain.neg (inner: ConcreteDomain) : Except EConcreteDomain ConcreteDomain :=
  let value := -inner.bv.value
  pure { bv := { value := value.toNat, width := inner.bv.width } }


public def standardBi (left: ConcreteDomain) (right: ConcreteDomain) (fn: {w: Nat} → BitVec w → BitVec w → BitVec w)
  : Except EConcreteDomain ConcreteDomain := do
  let width := left.bv.width
  let h1: left.bv.width = width := by rw[eq_self width]; trivial

  let (left, right) ←
    if h2: right.bv.width = width then
      pure (BitVec.cast (n := left.bv.width) (m := width) h1 left.bv.value, BitVec.cast h2 right.bv.value)
    else
      Except.error (EConcreteDomain.BinaryWidthMismatch left right)

  let value := fn left right

  pure { bv := { value, width } }

public def boolBi (left: ConcreteDomain) (right: ConcreteDomain) (fn: {w: Nat} → BitVec w → BitVec w → Bool)
  : Except EConcreteDomain ConcreteDomain := do
  let width := left.bv.width
  let h1: left.bv.width = width := by rw[eq_self width]; trivial

  let (left, right) ←
    if h2: right.bv.width = width then
      pure (BitVec.cast (n := left.bv.width) (m := width) h1 left.bv.value, BitVec.cast h2 right.bv.value)
    else
      Except.error (EConcreteDomain.BinaryWidthMismatch left right)

  let value := BitVec.ofBool (fn left right)

  pure { bv := { value, width := 1 } }

public def ConcreteDomain.add (left) (right) := do
  standardBi left right λ a b => a + b

public def ConcreteDomain.sub (left) (right) := do
  standardBi left right λ a b => a - b

public def ConcreteDomain.mul (left) (right) := do
  standardBi left right λ a b => a * b

public def ConcreteDomain.udiv (left) (right) := do
  standardBi left right λ a b => (a.smtUDiv b) -- corresponds to 'bvudiv'

public def ConcreteDomain.urem (left) (right) := do
  standardBi left right λ a b => (a.umod b) -- corresponds to 'bvurem'

public def ConcreteDomain.sdiv (left) (right) := do
  standardBi left right λ a b => (a.smtSDiv b)  -- corresponds to 'bvsdiv'

public def ConcreteDomain.srem (left) (right) := do
  standardBi left right λ a b => (a.srem b) -- corresponds to 'bvsrem'

public def ConcreteDomain.bitAnd (left) (right) := do
  standardBi left right λ a b => (a &&& b)

public def ConcreteDomain.bitOr (left) (right) := do
  standardBi left right λ a b => (a ||| b)

public def ConcreteDomain.bitXor (left) (right) := do
  standardBi left right λ a b => (a ^^^ b)

public def ConcreteDomain.eq (left) (right) := do
  boolBi left right λ a b => (a == b)

public def ConcreteDomain.ult (left) (right) := do
  boolBi left right λ a b => (a.ult b)

public def ConcreteDomain.ule (left) (right) := do
  boolBi left right λ a b => (a.ule b)

public def ConcreteDomain.slt (left) (right) := do
  boolBi left right λ a b => (a.slt b)

public def ConcreteDomain.sle (left) (right) := do
  boolBi left right λ a b => (a.sle b)

public def ConcreteDomain.shl (left) (right) := do
  standardBi left right λ a b => (a.shiftLeft b.toNat)

public def ConcreteDomain.lshr (left) (right) := do
  standardBi left right λ a b => (a.ushiftRight b.toNat)

public def ConcreteDomain.ashr (left) (right) := do
  standardBi left right λ a b => (a.sshiftRight b.toNat)

public instance : Domain ConcreteDomain where
  ε := EConcreteDomain

  ofBitvector := ConcreteDomain.ofBitvector
  toBitvector? := ConcreteDomain.toBitvector?

  not := ConcreteDomain.not
  neg := ConcreteDomain.neg

  add := ConcreteDomain.add
  sub := ConcreteDomain.sub
  mul := ConcreteDomain.mul
  udiv := ConcreteDomain.udiv
  urem := ConcreteDomain.urem
  sdiv := ConcreteDomain.sdiv
  srem := ConcreteDomain.srem

  bitAnd := ConcreteDomain.bitAnd
  bitOr := ConcreteDomain.bitOr
  bitXor := ConcreteDomain.bitXor

  eq := ConcreteDomain.eq
  ult := ConcreteDomain.ult
  ule := ConcreteDomain.ule
  slt := ConcreteDomain.slt
  sle := ConcreteDomain.sle

  shl := ConcreteDomain.shl
  lshr := ConcreteDomain.lshr
  ashr := ConcreteDomain.ashr
