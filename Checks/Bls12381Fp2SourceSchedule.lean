import Challenge.Bls12381.ProofSupport.Fp2Source

set_option warningAsError true

namespace Checks.Bls12381Fp2SourceSchedule

open Challenge.Bls12381.ProofSupport

example (a : Fp2.Repr) :
    Fp2.Canonical a ↔ Fp.Canonical a.c0 ∧ Fp.Canonical a.c1 :=
  Fp2.canonical_iff a

example (a b : Fp2.Repr) :
    Fp2.addSource a b =
      { c0 := Fp.addSource a.c0 b.c0
        c1 := Fp.addSource a.c1 b.c1 } := rfl

example (a b : Fp2.Repr) :
    Fp2.subSource a b =
      { c0 := Fp.subSource a.c0 b.c0
        c1 := Fp.subSource a.c1 b.c1 } := rfl

example (a : Fp2.Repr) :
    Fp2.negSource a =
      { c0 := Fp.negSource a.c0
        c1 := Fp.negSource a.c1 } := rfl

example (a b : Fp2.Repr) :
    Fp2.mulSource a b =
      let v0 := Fp.mulCanonical a.c0 b.c0
      let v1 := Fp.mulCanonical a.c1 b.c1
      let c1 := Fp.subSource
        (Fp.mulCanonical
          (Fp.addSource a.c0 a.c1) (Fp.addSource b.c0 b.c1))
        (Fp.addSource v0 v1)
      { c0 := Fp.subSource v0 v1, c1 } := rfl

example (a b : Fp2.Repr) :
    Fp2.runMulSource a b =
      let v0 := Fp.mulCanonical a.c0 b.c0
      let v1 := Fp.mulCanonical a.c1 b.c1
      let aSum := Fp.addSource a.c0 a.c1
      let bSum := Fp.addSource b.c0 b.c1
      let cross := Fp.mulCanonical aSum bSum
      let vSum := Fp.addSource v0 v1
      let c1 := Fp.subSource cross vSum
      let c0 := Fp.subSource v0 v1
      { v0, v1, aSum, bSum, cross, vSum, c1
        result := Fp2.mkRepr c0 c1 } :=
  Fp2.runMulSource_eq a b

example (a : Fp2.Repr) :
    Fp2.sqrSource a =
      let c0 := Fp.mulCanonical
        (Fp.addSource a.c0 a.c1) (Fp.subSource a.c0 a.c1)
      let product := Fp.mulCanonical a.c0 a.c1
      let c1 := Fp.addSource product product
      { c0, c1 } := rfl

example (a : Fp2.Repr) :
    Fp2.sqrSource a =
      Fp2.mkRepr (Fp2.sqrRealSource a) (Fp2.sqrC1Source a) :=
  Fp2.sqrSource_eq a

example (a : Fp2.Repr) :
    Fp2.invSource a =
      let norm := Fp.addSource
        (Fp.squareCanonical a.c0) (Fp.squareCanonical a.c1)
      let normInv := Fp.invCanonical norm
      { c0 := Fp.mulCanonical a.c0 normInv
        c1 := Fp.mulCanonical (Fp.negSource a.c1) normInv } := rfl

example (a : Fp2.Repr) :
    Fp2.runInvSource a =
      let norm := Fp2.invNormSource a
      let normInv := Fp.invCanonical norm
      let c0 := Fp2.invRealSource a.c0 normInv
      let c1 := Fp2.invImaginarySource a.c1 normInv
      { norm, normInv, c0, c1, result := Fp2.mkRepr c0 c1 } :=
  Fp2.runInvSource_eq a

example (a : Fp2.Repr) (s : Fp.Limbs) :
    Fp2.mulFpSource a s =
      { c0 := Fp.mulCanonical a.c0 s
        c1 := Fp.mulCanonical a.c1 s } := rfl

end Checks.Bls12381Fp2SourceSchedule
