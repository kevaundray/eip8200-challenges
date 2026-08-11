import Challenge.Bls12381.ProofSupport.LawfulFp2

set_option warningAsError true

/-! Lawful component carrier for the BLS12-381 cubic extension. -/

namespace Challenge.Bls12381.ProofSupport.LawfulFp6

structure Carrier where
  c0 : LawfulFp2.Carrier
  c1 : LawfulFp2.Carrier
  c2 : LawfulFp2.Carrier
deriving DecidableEq

/-- Inverse-free adapter from the pinned three-component wire carrier. -/
def ofWire (a : EvmSemantics.Crypto.Bls12381.Fp6) : Carrier :=
  { c0 := LawfulFp2.ofWire a.c0
    c1 := LawfulFp2.ofWire a.c1
    c2 := LawfulFp2.ofWire a.c2 }

/-- Inverse-free adapter back to the pinned wire carrier. -/
def toWire (a : Carrier) : EvmSemantics.Crypto.Bls12381.Fp6 :=
  { c0 := LawfulFp2.toWire a.c0
    c1 := LawfulFp2.toWire a.c1
    c2 := LawfulFp2.toWire a.c2 }

@[simp] theorem toWire_ofWire (a : EvmSemantics.Crypto.Bls12381.Fp6) :
    toWire (ofWire a) = a := by
  cases a
  simp [toWire, ofWire]

@[simp] theorem ofWire_toWire (a : Carrier) : ofWire (toWire a) = a := by
  cases a
  simp [toWire, ofWire]

end Challenge.Bls12381.ProofSupport.LawfulFp6
