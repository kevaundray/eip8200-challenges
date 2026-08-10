import Challenge.Bls12381.ProofSupport.Fp2

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.Fp6

open EvmSemantics.Crypto.Bls12381

structure Repr where
  c0 : Fp2.Repr
  c1 : Fp2.Repr
  c2 : Fp2.Repr
deriving DecidableEq

def toField (a : Repr) : EvmSemantics.Crypto.Bls12381.Fp6 :=
  { c0 := Fp2.toField a.c0, c1 := Fp2.toField a.c1, c2 := Fp2.toField a.c2 }

def ofField (a : EvmSemantics.Crypto.Bls12381.Fp6) : Repr :=
  { c0 := Fp2.ofField a.c0, c1 := Fp2.ofField a.c1, c2 := Fp2.ofField a.c2 }

def Refines (a : Repr) (value : EvmSemantics.Crypto.Bls12381.Fp6) : Prop :=
  toField a = value

@[simp] theorem toField_ofField (a : EvmSemantics.Crypto.Bls12381.Fp6) :
    toField (ofField a) = a := by
  cases a
  simp [toField, ofField]

theorem refines_ofField (a : EvmSemantics.Crypto.Bls12381.Fp6) :
    Refines (ofField a) a := by
  simp [Refines]

/-- Multiplication by BLS12-381's sextic non-residue `1 + u`. -/
def mulByXi (a : Fp2.Repr) : Fp2.Repr :=
  { c0 := Fp.sub a.c0 a.c1, c1 := Fp.add a.c0 a.c1 }

@[simp] theorem semantic_mulByXi (a : EvmSemantics.Crypto.Bls12381.Fp2) :
    SexticNonResidue.mulByXi a =
      { c0 := a.c0 - a.c1, c1 := a.c0 + a.c1 } := rfl

def add (a b : Repr) : Repr :=
  { c0 := Fp2.add a.c0 b.c0
    c1 := Fp2.add a.c1 b.c1
    c2 := Fp2.add a.c2 b.c2 }

def sub (a b : Repr) : Repr :=
  { c0 := Fp2.sub a.c0 b.c0
    c1 := Fp2.sub a.c1 b.c1
    c2 := Fp2.sub a.c2 b.c2 }

/-- Six-multiplication Karatsuba formula for the cubic extension. -/
def mul (a b : Repr) : Repr :=
  let v0 := Fp2.mul a.c0 b.c0
  let v1 := Fp2.mul a.c1 b.c1
  let v2 := Fp2.mul a.c2 b.c2
  let t0 := Fp2.mul (Fp2.add a.c1 a.c2) (Fp2.add b.c1 b.c2)
  let t1 := Fp2.mul (Fp2.add a.c0 a.c1) (Fp2.add b.c0 b.c1)
  let t2 := Fp2.mul (Fp2.add a.c0 a.c2) (Fp2.add b.c0 b.c2)
  { c0 := Fp2.add v0 (mulByXi (Fp2.sub (Fp2.sub t0 v1) v2))
    c1 := Fp2.add (Fp2.sub (Fp2.sub t1 v0) v1) (mulByXi v2)
    c2 := Fp2.sub (Fp2.sub (Fp2.add t2 v1) v0) v2 }

def square (a : Repr) : Repr :=
  let s0 := Fp2.square a.c0
  let s1 := Fp2.mul a.c0 a.c1
  let s2 := Fp2.mul a.c1 a.c2
  let s3 := Fp2.square a.c1
  let s4 := Fp2.mul a.c0 a.c2
  let s5 := Fp2.square a.c2
  { c0 := Fp2.add s0 (mulByXi (Fp2.add s2 s2))
    c1 := Fp2.add (Fp2.add s1 s1) (mulByXi s5)
    c2 := Fp2.add (Fp2.add s4 s4) s3 }

/-- Multiplication by the cubic generator `v`. -/
def mulByV (a : Repr) : Repr :=
  { c0 := mulByXi a.c2, c1 := a.c0, c2 := a.c1 }
def inv (a : Repr) : Repr := ofField (_root_.Fp6.inv (toField a))

theorem mul_components (a b : Repr) :
    mul a b =
      let v0 := Fp2.mul a.c0 b.c0
      let v1 := Fp2.mul a.c1 b.c1
      let v2 := Fp2.mul a.c2 b.c2
      let t0 := Fp2.mul (Fp2.add a.c1 a.c2) (Fp2.add b.c1 b.c2)
      let t1 := Fp2.mul (Fp2.add a.c0 a.c1) (Fp2.add b.c0 b.c1)
      let t2 := Fp2.mul (Fp2.add a.c0 a.c2) (Fp2.add b.c0 b.c2)
      { c0 := Fp2.add v0 (mulByXi (Fp2.sub (Fp2.sub t0 v1) v2))
        c1 := Fp2.add (Fp2.sub (Fp2.sub t1 v0) v1) (mulByXi v2)
        c2 := Fp2.sub (Fp2.sub (Fp2.add t2 v1) v0) v2 } := rfl

@[simp] theorem toField_mulByXi (a : Fp2.Repr) :
    Fp2.toField (mulByXi a) =
      instBls12381SexticNonResidue.mulByXi
        (Fp2.toField a) := by
  change
    ({ c0 := Fp.toField (Fp.sub a.c0 a.c1)
       c1 := Fp.toField (Fp.add a.c0 a.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) = _
  simp [Fp2.toField]

theorem refines_add (a b : Repr) : Refines (add a b) (toField a + toField b) := by
  change toField (add a b) = _root_.Fp6.add (toField a) (toField b)
  simp [add, toField, _root_.Fp6.add]
theorem refines_sub (a b : Repr) : Refines (sub a b) (toField a - toField b) := by
  change toField (sub a b) = _root_.Fp6.sub (toField a) (toField b)
  simp [sub, toField, _root_.Fp6.sub]
theorem refines_mul (a b : Repr) : Refines (mul a b) (toField a * toField b) := by
  change toField (mul a b) = _root_.Fp6.mul (toField a) (toField b)
  simp [mul, toField, _root_.Fp6.mul]
theorem refines_square (a : Repr) :
    Refines (square a) (_root_.Fp6.square (toField a)) := by
  change toField (square a) = _root_.Fp6.square (toField a)
  simp [square, toField, _root_.Fp6.square]
theorem refines_inv (a : Repr) :
    Refines (inv a) (_root_.Fp6.inv (toField a)) :=
  refines_ofField _

@[simp] theorem toField_add (a b : Repr) :
    toField (add a b) = toField a + toField b := refines_add a b
@[simp] theorem toField_sub (a b : Repr) :
    toField (sub a b) = toField a - toField b := refines_sub a b
@[simp] theorem toField_mul (a b : Repr) :
    toField (mul a b) = toField a * toField b := refines_mul a b
@[simp] theorem toField_square (a : Repr) :
    toField (square a) = _root_.Fp6.square (toField a) := refines_square a
@[simp] theorem toField_mulByV (a : Repr) :
    toField (mulByV a) = _root_.Fp6.mulByV (toField a) := by
  change
    ({ c0 := Fp2.toField (mulByXi a.c2)
       c1 := Fp2.toField a.c0
       c2 := Fp2.toField a.c1 } : EvmSemantics.Crypto.Bls12381.Fp6) = _
  simp [_root_.Fp6.mulByV, toField]
@[simp] theorem toField_inv (a : Repr) :
    toField (inv a) = _root_.Fp6.inv (toField a) := refines_inv a

@[simp] theorem semantic_pow_two (a : EvmSemantics.Crypto.Bls12381.Fp6) :
    a ^ 2 = _root_.Fp6.square a := rfl

end Challenge.Bls12381.ProofSupport.Fp6
