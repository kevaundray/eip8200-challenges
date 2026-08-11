import Challenge.Bls12381.ProofSupport.Fp2SqrtDefs
import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true

/-! # Refinement of the decoded Fp2 square-root program -/

namespace Challenge.Bls12381.ProofSupport.Fp2

open PrimeField

irreducible_def lawfulSqrt (lemma := lawfulSqrt_eq)
    (x : LawfulFp2.Base) : LawfulFp2.Base :=
  x ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4)

def lawfulInvTwo : LawfulFp2.Base :=
  (Fp.value invTwo : LawfulFp2.Base)

def lawfulSqrtOps : SqrtProgram.Ops LawfulFp2.Base LawfulFp2.Carrier where
  c0 := QuadraticAlgebra.re
  c1 := QuadraticAlgebra.im
  zero := 0
  pair := fun c0 c1 => ⟨c0, c1⟩
  isZeroPair := fun a => decide (a = 0)
  isZeroCell := fun a => decide (a = 0)
  eqCell := fun a b => decide (a = b)
  eqPair := fun a b => decide (a = b)
  add := fun a b => a + b
  sub := fun a b => a - b
  neg := (- .)
  mul := fun a b => a * b
  square := fun a => a ^ 2
  sqrt := lawfulSqrt
  inv := Inv.inv
  squarePair := fun a => a * a
  invTwo := lawfulInvTwo

def SqrtCellRel (a : Fp.Limbs) (b : LawfulFp2.Base) : Prop :=
  Fp.Canonical a ∧ (Fp.value a : LawfulFp2.Base) = b

def SqrtPairRel (a : Repr) (b : LawfulFp2.Carrier) : Prop :=
  Canonical a ∧ toLawful a = b

private theorem canonical_zero_repr : Canonical zero := by
  constructor <;> exact ⟨Fp.canonical_normalize 0⟩

theorem toLawful_zero_repr : toLawful zero = 0 := by
  unfold toLawful
  rw [toField_zero]
  rfl

theorem sqrtSourceOps_refines :
    SqrtProgram.Refines sqrtSourceOps lawfulSqrtOps SqrtCellRel SqrtPairRel := by
  constructor <;> dsimp only [sqrtSourceOps, lawfulSqrtOps]
  · rintro a b ⟨ha, hab⟩
    exact ⟨ha.c0.proof, by
      have hre := congrArg QuadraticAlgebra.re hab
      simpa [toLawful, LawfulFp2.ofWire, toField] using hre⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨ha.c1.proof, by
      have him := congrArg QuadraticAlgebra.im hab
      simpa [toLawful, LawfulFp2.ofWire, toField] using him⟩
  · exact ⟨canonical_zero_repr, toLawful_zero_repr⟩
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    refine ⟨canonical_mkRepr ⟨ha₀⟩ ⟨ha₁⟩, ?_⟩
    rw [toLawful_mkRepr]
    apply QuadraticAlgebra.ext <;> simp [hab₀, hab₁]
  · rintro a b ⟨ha, hab⟩
    apply Bool.eq_iff_iff.mpr
    simpa only [isZeroSource_iff ha, decide_eq_true_eq] using
      (show toLawful a = 0 ↔ b = 0 by rw [hab])
  · rintro a b ⟨ha, hab⟩
    apply Bool.eq_iff_iff.mpr
    rw [Fp.isZeroValue_eq_true, decide_eq_true_eq]
    constructor
    · intro hzero
      rw [← hab, hzero]
      norm_num
    · intro hzero
      apply Fp.value_eq_of_lawful_eq ha (Fp.canonical_normalize 0)
      rw [hab, hzero]
      norm_num
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    apply Bool.eq_iff_iff.mpr
    rw [Fp.eqCanonicalValue_eq_true]
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      rw [← hab₀, ← hab₁, h]
    · intro h
      exact Fp.value_eq_of_lawful_eq ha₀ ha₁ (hab₀.trans (h.trans hab₁.symm))
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    apply Bool.eq_iff_iff.mpr
    simpa only [eqSource_iff ha₀ ha₁, decide_eq_true_eq] using
      (show toLawful a₀ = toLawful a₁ ↔ b₀ = b₁ by rw [hab₀, hab₁])
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    exact ⟨Fp.canonical_addSource ha₀ ha₁, by
      change PrimeField.finEquiv (Fp.toField (Fp.addSource a₀ a₁)) = _
      rw [Fp.toLawful_addSource ha₀ ha₁,
        Fp.finEquiv_toField, Fp.finEquiv_toField, hab₀, hab₁]⟩
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    exact ⟨Fp.canonical_subSource ha₀ ha₁, by
      change PrimeField.finEquiv (Fp.toField (Fp.subSource a₀ a₁)) = _
      rw [Fp.toLawful_subSource ha₀ ha₁,
        Fp.finEquiv_toField, Fp.finEquiv_toField, hab₀, hab₁]⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨Fp.canonical_negSource ha, by
      change PrimeField.finEquiv (Fp.toField (Fp.negSource a)) = _
      rw [Fp.toLawful_negSource ha, Fp.finEquiv_toField, hab]⟩
  · rintro a₀ b₀ a₁ b₁ ⟨ha₀, hab₀⟩ ⟨ha₁, hab₁⟩
    exact ⟨Fp.canonical_mulCanonical ha₀ ha₁, by
      change PrimeField.finEquiv (Fp.toField (Fp.mulCanonical a₀ a₁)) = _
      rw [Fp.toField_mulCanonical ha₀ ha₁, map_mul,
        Fp.finEquiv_toField, Fp.finEquiv_toField, hab₀, hab₁]⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨Fp.canonical_squareCanonical ha, by
      rw [Fp.lawful_squareCanonical ha, hab]⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨Fp.canonical_sqrtCanonical ha, by
      rw [Fp.lawful_sqrtCanonical_pow ha, hab, lawfulSqrt_eq]⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨Fp.canonical_invCanonical ha, by
      change PrimeField.finEquiv (Fp.toField (Fp.invCanonical a)) = _
      rw [Fp.toLawful_invCanonical ha, Fp.finEquiv_toField, hab]⟩
  · rintro a b ⟨ha, hab⟩
    exact ⟨canonical_sqrSource ha, by
      rw [toLawful_sqrSource ha, hab]⟩
  · exact ⟨canonical_invTwo, rfl⟩

theorem sqrtSource_refines_lawful {a : Repr} (ha : Canonical a) :
    (sqrtSource a).exists_ =
        (SqrtProgram.run lawfulSqrtOps (toLawful a)).exists_ ∧
      SqrtPairRel (sqrtSource a).root
        (SqrtProgram.run lawfulSqrtOps (toLawful a)).root := by
  exact SqrtProgram.run_refines sqrtSourceOps_refines ⟨ha, rfl⟩

end Challenge.Bls12381.ProofSupport.Fp2
