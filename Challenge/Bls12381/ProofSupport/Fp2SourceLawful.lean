import Challenge.Bls12381.ProofSupport.Fp2Source
import Challenge.Bls12381.ProofSupport.FpAddSubLawful

set_option warningAsError true

/-! # Lawful refinement of source-faithful BLS12-381 Fp2 arithmetic -/

namespace Challenge.Bls12381.ProofSupport.Fp2

theorem toField_addSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toField (addSource a b) = toField a + toField b := by
  change
    ({ c0 := Fp.toField (Fp.addSource a.c0 b.c0)
       c1 := Fp.toField (Fp.addSource a.c1 b.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    ({ c0 := Fp.toField a.c0 + Fp.toField b.c0
       c1 := Fp.toField a.c1 + Fp.toField b.c1 } :
      EvmSemantics.Crypto.Bls12381.Fp2)
  rw [Fp.toField_addSource ha.c0.proof hb.c0.proof,
    Fp.toField_addSource ha.c1.proof hb.c1.proof]

theorem toField_subSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toField (subSource a b) = toField a - toField b := by
  change
    ({ c0 := Fp.toField (Fp.subSource a.c0 b.c0)
       c1 := Fp.toField (Fp.subSource a.c1 b.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    ({ c0 := Fp.toField a.c0 - Fp.toField b.c0
       c1 := Fp.toField a.c1 - Fp.toField b.c1 } :
      EvmSemantics.Crypto.Bls12381.Fp2)
  rw [Fp.toField_subSource ha.c0.proof hb.c0.proof,
    Fp.toField_subSource ha.c1.proof hb.c1.proof]

theorem toField_negSource {a : Repr} (ha : Canonical a) :
    toField (negSource a) = -toField a := by
  change
    ({ c0 := Fp.toField (Fp.negSource a.c0)
       c1 := Fp.toField (Fp.negSource a.c1) } :
      EvmSemantics.Crypto.Bls12381.Fp2) =
    ({ c0 := -Fp.toField a.c0, c1 := -Fp.toField a.c1 } :
      EvmSemantics.Crypto.Bls12381.Fp2)
  rw [Fp.toField_negSource ha.c0.proof,
    Fp.toField_negSource ha.c1.proof]

theorem toField_mulFpSource {a : Repr} {s : Fp.Limbs}
    (ha : Canonical a) (hs : Fp.Canonical s) :
    toField (mulFpSource a s) =
      { c0 := Fp.toField a.c0 * Fp.toField s
        c1 := Fp.toField a.c1 * Fp.toField s } := by
  change
    ({ c0 := Fp.toField (Fp.mulCanonical a.c0 s)
       c1 := Fp.toField (Fp.mulCanonical a.c1 s) } :
      EvmSemantics.Crypto.Bls12381.Fp2) = _
  rw [Fp.toField_mulCanonical ha.c0.proof hs,
    Fp.toField_mulCanonical ha.c1.proof hs]

theorem toLawful_addSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toLawful (addSource a b) = toLawful a + toLawful b := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, addSource, mkRepr,
      Fp.toLawful_addSource ha.c0.proof hb.c0.proof,
      Fp.toLawful_addSource ha.c1.proof hb.c1.proof]

theorem toLawful_subSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toLawful (subSource a b) = toLawful a - toLawful b := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, subSource, mkRepr,
      Fp.toLawful_subSource ha.c0.proof hb.c0.proof,
      Fp.toLawful_subSource ha.c1.proof hb.c1.proof]

theorem toLawful_negSource {a : Repr} (ha : Canonical a) :
    toLawful (negSource a) = -toLawful a := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, negSource, mkRepr,
      Fp.toLawful_negSource ha.c0.proof,
      Fp.toLawful_negSource ha.c1.proof]

theorem toLawful_mulFpSource {a : Repr} {s : Fp.Limbs}
    (ha : Canonical a) (hs : Fp.Canonical s) :
    toLawful (mulFpSource a s) =
      algebraMap LawfulFp2.Base LawfulFp2.Carrier
        (PrimeField.finEquiv (Fp.toField s)) * toLawful a := by
  apply QuadraticAlgebra.ext <;>
    simp [toLawful, LawfulFp2.ofWire, toField, mulFpSource, mkRepr,
      Fp.toField_mulCanonical ha.c0.proof hs,
      Fp.toField_mulCanonical ha.c1.proof hs, map_mul, mul_comm]

end Challenge.Bls12381.ProofSupport.Fp2
