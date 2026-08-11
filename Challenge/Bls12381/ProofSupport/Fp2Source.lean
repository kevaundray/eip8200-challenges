import Challenge.Bls12381.ProofSupport.Fp2Representation
import Challenge.Bls12381.ProofSupport.FpAddSub
import Challenge.Bls12381.ProofSupport.FpMul
import Challenge.Bls12381.ProofSupport.FpSquare
import Challenge.Bls12381.ProofSupport.FpInv

set_option warningAsError true

/-! # Source-faithful BLS12-381 Fp2 arithmetic -/

namespace Challenge.Bls12381.ProofSupport.Fp2

/-- Exact componentwise `Fp2.add` call graph. -/
def addSource (a b : Repr) : Repr :=
  { c0 := Fp.addSource a.c0 b.c0
    c1 := Fp.addSource a.c1 b.c1 }

/-- Exact componentwise `Fp2.sub` call graph. -/
def subSource (a b : Repr) : Repr :=
  { c0 := Fp.subSource a.c0 b.c0
    c1 := Fp.subSource a.c1 b.c1 }

/-- Exact componentwise `Fp2.neg` call graph. -/
def negSource (a : Repr) : Repr :=
  { c0 := Fp.negSource a.c0
    c1 := Fp.negSource a.c1 }

/-- Exact three-multiplication Karatsuba schedule from `Fp2.mul`. -/
def mulSource (a b : Repr) : Repr :=
  let v0 := Fp.mulCanonical a.c0 b.c0
  let v1 := Fp.mulCanonical a.c1 b.c1
  let c1 := Fp.subSource
    (Fp.mulCanonical
      (Fp.addSource a.c0 a.c1) (Fp.addSource b.c0 b.c1))
    (Fp.addSource v0 v1)
  { c0 := Fp.subSource v0 v1, c1 }

/-- Exact two-multiplication optimized schedule from `Fp2.sqr`. -/
def sqrSource (a : Repr) : Repr :=
  let c0 := Fp.mulCanonical
    (Fp.addSource a.c0 a.c1) (Fp.subSource a.c0 a.c1)
  let product := Fp.mulCanonical a.c0 a.c1
  let c1 := Fp.addSource product product
  { c0, c1 }

/-- Exact norm/invert/adjugate schedule from `Fp2.inv`. -/
def invSource (a : Repr) : Repr :=
  let norm := Fp.addSource
    (Fp.squareCanonical a.c0) (Fp.squareCanonical a.c1)
  let normInv := Fp.invCanonical norm
  { c0 := Fp.mulCanonical a.c0 normInv
    c1 := Fp.mulCanonical (Fp.negSource a.c1) normInv }

/-- Exact componentwise scalar multiplication from `Fp2.mulFp`. -/
def mulFpSource (a : Repr) (s : Fp.Limbs) : Repr :=
  { c0 := Fp.mulCanonical a.c0 s
    c1 := Fp.mulCanonical a.c1 s }

end Challenge.Bls12381.ProofSupport.Fp2
