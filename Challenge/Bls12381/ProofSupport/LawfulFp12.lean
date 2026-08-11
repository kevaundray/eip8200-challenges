import Challenge.Bls12381.ProofSupport.LawfulFp6

set_option warningAsError true

/-! Lawful component carrier for the BLS12-381 quadratic-over-cubic tower. -/

namespace Challenge.Bls12381.ProofSupport.LawfulFp12

@[ext] structure Carrier where
  c0 : LawfulFp6.Carrier
  c1 : LawfulFp6.Carrier
deriving DecidableEq

/-- Quadratic-over-cubic Karatsuba multiplication with `w² = v`. -/
def mul (a b : Carrier) : Carrier :=
  let v0 := LawfulFp6.mul a.c0 b.c0
  let v1 := LawfulFp6.mul a.c1 b.c1
  let t := LawfulFp6.mul (LawfulFp6.add a.c0 a.c1)
    (LawfulFp6.add b.c0 b.c1)
  { c0 := LawfulFp6.add v0 (LawfulFp6.mulByV v1)
    c1 := LawfulFp6.sub (LawfulFp6.sub t v0) v1 }

def ofWire (a : EvmSemantics.Crypto.Bls12381.Fp12) : Carrier :=
  { c0 := LawfulFp6.ofWire a.c0
    c1 := LawfulFp6.ofWire a.c1 }

def toWire (a : Carrier) : EvmSemantics.Crypto.Bls12381.Fp12 :=
  { c0 := LawfulFp6.toWire a.c0
    c1 := LawfulFp6.toWire a.c1 }

@[simp] theorem toWire_ofWire (a : EvmSemantics.Crypto.Bls12381.Fp12) :
    toWire (ofWire a) = a := by
  cases a
  simp [toWire, ofWire]

@[simp] theorem ofWire_toWire (a : Carrier) : ofWire (toWire a) = a := by
  cases a
  simp [toWire, ofWire]

end Challenge.Bls12381.ProofSupport.LawfulFp12
