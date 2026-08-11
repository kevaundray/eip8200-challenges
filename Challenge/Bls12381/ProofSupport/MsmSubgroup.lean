import Challenge.Bls12381.ProofSupport.MsmSemantics
import Challenge.Bls12381.ProofSupport.SubgroupSemantics

set_option warningAsError true

/-!
# Prime-subgroup closure of naive MSM

This proof-only module combines the independent group-sum semantics with the
proof-visible subgroup characterization.  It proves that the naive fold stays
in the prime subgroup whenever every input point is accepted.
-/

namespace Challenge.Bls12381.ProofSupport.MsmSubgroup

open EvmSemantics.Crypto.Bls12381

theorem g1MathSum_nsmul_zero (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    N • MsmSemantics.g1MathSum terms = 0 := by
  induction terms with
  | nil => simp [MsmSemantics.g1MathSum]
  | cons term rest ih =>
      rcases term with ⟨point, scalar⟩
      have hpoint : N • AffineGroup.toMathlib G1Affine.curve point = 0 :=
        (SubgroupSemantics.g1Affine_eq_true_iff_nsmul_zero point).1
          (hterms (point, scalar) (by simp))
      have hscaled : N •
          (scalar.val • AffineGroup.toMathlib G1Affine.curve point) = 0 := by
        rw [smul_smul, Nat.mul_comm, ← smul_smul, hpoint, smul_zero]
      have hrest : N • MsmSemantics.g1MathSum rest = 0 := by
        apply ih
        intro term hterm
        exact hterms term (by simp [hterm])
      calc
        N • MsmSemantics.g1MathSum ((point, scalar) :: rest) =
            N • (scalar.val • AffineGroup.toMathlib G1Affine.curve point) +
              N • MsmSemantics.g1MathSum rest := by
                simp [MsmSemantics.g1MathSum, nsmul_add]
        _ = 0 := by rw [hscaled, hrest, add_zero]

theorem g2MathSum_nsmul_zero (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    N • MsmSemantics.g2MathSum terms = 0 := by
  induction terms with
  | nil => simp [MsmSemantics.g2MathSum]
  | cons term rest ih =>
      rcases term with ⟨point, scalar⟩
      have hpoint : N • AffineGroup.toMathlib G2Affine.curve point = 0 :=
        (SubgroupSemantics.g2Affine_eq_true_iff_nsmul_zero point).1
          (hterms (point, scalar) (by simp))
      have hscaled : N •
          (scalar.val • AffineGroup.toMathlib G2Affine.curve point) = 0 := by
        rw [smul_smul, Nat.mul_comm, ← smul_smul, hpoint, smul_zero]
      have hrest : N • MsmSemantics.g2MathSum rest = 0 := by
        apply ih
        intro term hterm
        exact hterms term (by simp [hterm])
      calc
        N • MsmSemantics.g2MathSum ((point, scalar) :: rest) =
            N • (scalar.val • AffineGroup.toMathlib G2Affine.curve point) +
              N • MsmSemantics.g2MathSum rest := by
                simp [MsmSemantics.g2MathSum, nsmul_add]
        _ = 0 := by rw [hscaled, hrest, add_zero]

theorem g1_output (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    Subgroup.g1Affine (MsmSemantics.g1Value terms) = true := by
  apply (SubgroupSemantics.g1Affine_eq_true_iff_nsmul_zero
    ⟨MsmSemantics.g1Value terms, MsmSemantics.g1Value_onCurve terms⟩).2
  rw [MsmSemantics.g1_nsmul_sum]
  exact g1MathSum_nsmul_zero terms hterms

theorem g2_output (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    Subgroup.g2Affine (MsmSemantics.g2Value terms) = true := by
  apply (SubgroupSemantics.g2Affine_eq_true_iff_nsmul_zero
    ⟨MsmSemantics.g2Value terms, MsmSemantics.g2Value_onCurve terms⟩).2
  rw [MsmSemantics.g2_nsmul_sum]
  exact g2MathSum_nsmul_zero terms hterms

theorem g1_wire_output (terms : List MsmSemantics.G1ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g1Affine term.1.1 = true) :
    Subgroup.g1 (G1Affine.toWire (MsmSemantics.g1Value terms)) = true := by
  simpa [Subgroup.g1] using g1_output terms hterms

theorem g2_wire_output (terms : List MsmSemantics.G2ValidTerm)
    (hterms : ∀ term ∈ terms, Subgroup.g2Affine term.1.1 = true) :
    Subgroup.g2 (G2Affine.toWire (MsmSemantics.g2Value terms)) = true := by
  simpa [Subgroup.g2] using g2_output terms hterms

end Challenge.Bls12381.ProofSupport.MsmSubgroup
