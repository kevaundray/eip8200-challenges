import Challenge.Bls12381.ProofSupport.Fp2SqrtDefs
import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true

/-! # Source-faithful BLS12-381 Fp2 square roots -/

namespace Challenge.Bls12381.ProofSupport.Fp2

theorem canonical_zero : Canonical zero := by
  constructor <;> exact ⟨Fp.canonical_normalize 0⟩

theorem canonical_sqrtSource {a : Repr} (ha : Canonical a) :
    Canonical (sqrtSource a).root := by
  exact SqrtProgram.run_good sqrtSourceOps Fp.Canonical Canonical
    canonical_zero
    (fun _ _ hx hy => canonical_mkRepr ⟨hx⟩ ⟨hy⟩)
    (fun _ _ => Fp.canonical_addSource)
    (fun _ _ => Fp.canonical_subSource)
    (fun _ => Fp.canonical_negSource)
    (fun _ _ => Fp.canonical_mulCanonical)
    (fun _ => Fp.canonical_squareCanonical)
    (fun _ => Fp.canonical_sqrtCanonical)
    (fun _ => Fp.canonical_invCanonical)
    canonical_invTwo a ⟨ha.c0.proof, ha.c1.proof⟩

@[simp] theorem toLawful_zero : toLawful zero = 0 := by
  unfold toLawful
  rw [toField_zero]
  rfl

theorem sqrSource_zero : sqrSource zero = zero := by
  apply eq_of_lawful_eq (canonical_sqrSource canonical_zero) canonical_zero
  rw [toLawful_sqrSource canonical_zero, toLawful_zero]
  norm_num

theorem sqrtSource_success {a : Repr} (_ha : Canonical a)
    (hsuccess : (sqrtSource a).exists_ = true) :
    sqrSource (sqrtSource a).root = a := by
  exact SqrtProgram.run_success sqrtSourceOps a
    (fun hzero => by
      rw [eq_zero_of_isZeroSource_true hzero]
      exact sqrSource_zero)
    (fun _ _ => eq_of_eqSource_true) hsuccess

end Challenge.Bls12381.ProofSupport.Fp2
