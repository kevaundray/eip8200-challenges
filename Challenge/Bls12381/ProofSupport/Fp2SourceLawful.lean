import Challenge.Bls12381.ProofSupport.Fp2Source
import Challenge.Bls12381.ProofSupport.FpAddSubLawful
import Challenge.Bls12381.ProofSupport.FpInv

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

theorem toField_mulC0Source {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    Fp.toField (mulC0Source a b) =
      Fp.toField a.c0 * Fp.toField b.c0 -
        Fp.toField a.c1 * Fp.toField b.c1 := by
  have hv0 := (canonical_mulV0Source ha hb).proof
  have hv1 := (canonical_mulV1Source ha hb).proof
  rw [show mulC0Source a b =
      Fp.subSource (mulV0Source a b) (mulV1Source a b) by rfl]
  rw [Fp.toField_subSource hv0 hv1]
  rw [show Fp.toField (mulV0Source a b) =
      Fp.toField a.c0 * Fp.toField b.c0 by
        exact Fp.toField_mulCanonical ha.c0.proof hb.c0.proof,
    show Fp.toField (mulV1Source a b) =
      Fp.toField a.c1 * Fp.toField b.c1 by
        exact Fp.toField_mulCanonical ha.c1.proof hb.c1.proof]

theorem toField_mulC1Source {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    Fp.toField (mulC1Source a b) =
      (Fp.toField a.c0 + Fp.toField a.c1) *
          (Fp.toField b.c0 + Fp.toField b.c1) -
        Fp.toField a.c0 * Fp.toField b.c0 -
        Fp.toField a.c1 * Fp.toField b.c1 := by
  have haSum := Fp.canonical_addSource ha.c0.proof ha.c1.proof
  have hbSum := Fp.canonical_addSource hb.c0.proof hb.c1.proof
  have hv0 := (canonical_mulV0Source ha hb).proof
  have hv1 := (canonical_mulV1Source ha hb).proof
  have hcross := Fp.canonical_mulCanonical haSum hbSum
  have hvSum := Fp.canonical_addSource hv0 hv1
  rw [show mulC1Source a b = Fp.subSource
      (Fp.mulCanonical (Fp.addSource a.c0 a.c1)
        (Fp.addSource b.c0 b.c1))
      (Fp.addSource (mulV0Source a b) (mulV1Source a b)) by rfl]
  rw [Fp.toField_subSource hcross hvSum,
    Fp.toField_mulCanonical haSum hbSum,
    Fp.toField_addSource ha.c0.proof ha.c1.proof,
    Fp.toField_addSource hb.c0.proof hb.c1.proof,
    Fp.toField_addSource hv0 hv1,
    show Fp.toField (mulV0Source a b) =
      Fp.toField a.c0 * Fp.toField b.c0 by
        exact Fp.toField_mulCanonical ha.c0.proof hb.c0.proof,
    show Fp.toField (mulV1Source a b) =
      Fp.toField a.c1 * Fp.toField b.c1 by
        exact Fp.toField_mulCanonical ha.c1.proof hb.c1.proof]
  simp only [sub_eq_add_neg, neg_add_rev, add_assoc]
  ac_rfl

theorem toField_mulSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toField (mulSource a b) = toField a * toField b := by
  rw [mulSource_eq, toField_mkRepr,
    toField_mulC0Source ha hb, toField_mulC1Source ha hb]
  change _ = _root_.Fp2.mul (toField a) (toField b)
  simp only [_root_.Fp2.mul, toField]

theorem toField_sqrRealSource {a : Repr} (ha : Canonical a) :
    Fp.toField (sqrRealSource a) =
      (Fp.toField a.c0 + Fp.toField a.c1) *
        (Fp.toField a.c0 - Fp.toField a.c1) := by
  rw [show sqrRealSource a = Fp.mulCanonical
      (Fp.addSource a.c0 a.c1) (Fp.subSource a.c0 a.c1) by rfl]
  rw [Fp.toField_mulCanonical
      (Fp.canonical_addSource ha.c0.proof ha.c1.proof)
      (Fp.canonical_subSource ha.c0.proof ha.c1.proof),
    Fp.toField_addSource ha.c0.proof ha.c1.proof,
    Fp.toField_subSource ha.c0.proof ha.c1.proof]

theorem toField_sqrC1Source {a : Repr} (ha : Canonical a) :
    Fp.toField (sqrC1Source a) =
      Fp.toField a.c0 * Fp.toField a.c1 +
        Fp.toField a.c0 * Fp.toField a.c1 := by
  have hproduct := (canonical_sqrProductSource ha).proof
  rw [show sqrC1Source a = Fp.addSource
      (sqrProductSource a) (sqrProductSource a) by rfl]
  rw [Fp.toField_addSource hproduct hproduct,
    show Fp.toField (sqrProductSource a) =
      Fp.toField a.c0 * Fp.toField a.c1 by
        exact Fp.toField_mulCanonical ha.c0.proof ha.c1.proof]

theorem toField_sqrSource {a : Repr} (ha : Canonical a) :
    toField (sqrSource a) = _root_.Fp2.square (toField a) := by
  rw [sqrSource_eq, toField_mkRepr,
    toField_sqrRealSource ha, toField_sqrC1Source ha]
  change _ = _root_.Fp2.square (toField a)
  simp only [toField, _root_.Fp2.square]
  congr 1
  exact (add_mul _ _ _).symm

theorem toLawful_mulSource {a b : Repr} (ha : Canonical a)
    (hb : Canonical b) :
    toLawful (mulSource a b) = toLawful a * toLawful b := by
  rw [mulSource_eq, toLawful_mkRepr]
  apply QuadraticAlgebra.ext
  · simp [toLawful, LawfulFp2.ofWire, toField,
      toField_mulC0Source ha hb, map_sub, map_mul]
    ring
  · simp [toLawful, LawfulFp2.ofWire, toField,
      toField_mulC1Source ha hb, map_add, map_mul]
    ring

theorem toLawful_sqrSource {a : Repr} (ha : Canonical a) :
    toLawful (sqrSource a) = toLawful a * toLawful a := by
  rw [sqrSource_eq, toLawful_mkRepr]
  apply QuadraticAlgebra.ext
  · simp [toLawful, LawfulFp2.ofWire, toField,
      toField_sqrRealSource ha,
      map_add, map_sub, map_mul]
    ring
  · simp [toLawful, LawfulFp2.ofWire, toField,
      toField_sqrC1Source ha, map_add, map_mul]
    ring

theorem toLawful_invNormSource {a : Repr} (ha : Canonical a) :
    PrimeField.finEquiv (Fp.toField (invNormSource a)) =
      QuadraticAlgebra.norm (toLawful a) := by
  have hs0 := Fp.canonical_squareCanonical ha.c0.proof
  have hs1 := Fp.canonical_squareCanonical ha.c1.proof
  rw [show invNormSource a = Fp.addSource
      (Fp.squareCanonical a.c0) (Fp.squareCanonical a.c1) by rfl]
  rw [Fp.toLawful_addSource hs0 hs1,
    Fp.toField_squareCanonical ha.c0.proof,
    Fp.toField_squareCanonical ha.c1.proof,
    map_pow, map_pow]
  simp [toLawful, LawfulFp2.ofWire, toField,
    QuadraticAlgebra.norm_def, pow_two]

theorem toLawful_invNormInvSource {a : Repr} (ha : Canonical a) :
    PrimeField.finEquiv
        (Fp.toField (Fp.invCanonical (invNormSource a))) =
      (QuadraticAlgebra.norm (toLawful a))⁻¹ := by
  rw [Fp.toLawful_invCanonical (canonical_invNormSource ha).proof,
    toLawful_invNormSource ha]

theorem toLawful_invC0Source {a : Repr} (ha : Canonical a) :
    PrimeField.finEquiv (Fp.toField (invC0Source a)) =
      (toLawful a).re * (QuadraticAlgebra.norm (toLawful a))⁻¹ := by
  rw [show invC0Source a = Fp.mulCanonical a.c0
      (Fp.invCanonical (invNormSource a)) by rfl]
  rw [Fp.toField_mulCanonical ha.c0.proof
      (Fp.canonical_invCanonical (canonical_invNormSource ha).proof),
    map_mul, toLawful_invNormInvSource ha]
  rfl

theorem toLawful_invC1Source {a : Repr} (ha : Canonical a) :
    PrimeField.finEquiv (Fp.toField (invC1Source a)) =
      -(toLawful a).im * (QuadraticAlgebra.norm (toLawful a))⁻¹ := by
  rw [show invC1Source a = Fp.mulCanonical (Fp.negSource a.c1)
      (Fp.invCanonical (invNormSource a)) by rfl]
  rw [Fp.toField_mulCanonical (Fp.canonical_negSource ha.c1.proof)
      (Fp.canonical_invCanonical (canonical_invNormSource ha).proof),
    map_mul, Fp.toField_negSource ha.c1.proof, map_neg,
    toLawful_invNormInvSource ha]
  rfl

/-- The source inversion schedule refines the lawful quadratic-field inverse.
No equality to the pinned opaque `FF.modInv` is assumed or required. -/
theorem toLawful_invSource {a : Repr} (ha : Canonical a) :
    toLawful (invSource a) = (toLawful a)⁻¹ := by
  rw [invSource_eq, toLawful_mkRepr]
  apply QuadraticAlgebra.ext
  · simp [toLawful_invC0Source ha, QuadraticAlgebra.inv_def,
      QuadraticAlgebra.norm_def, mul_comm]
  · simp [toLawful_invC1Source ha, QuadraticAlgebra.inv_def,
      QuadraticAlgebra.norm_def, mul_comm]

theorem toLawful_invSource_zero {a : Repr} (ha : Canonical a)
    (hzero : toLawful a = 0) : toLawful (invSource a) = 0 := by
  rw [toLawful_invSource ha, hzero, inv_zero]

theorem toLawful_mul_invSource {a : Repr} (ha : Canonical a)
    (hne : toLawful a ≠ 0) :
    toLawful a * toLawful (invSource a) = 1 := by
  rw [toLawful_invSource ha]
  exact LawfulFp2.mul_inv_cancel (toLawful a) hne

end Challenge.Bls12381.ProofSupport.Fp2
