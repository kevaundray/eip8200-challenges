import Challenge.Bls12381.ProofSupport.FpSqrtConstants
import Challenge.Bls12381.ProofSupport.FpSquare
import Mathlib.FieldTheory.Finite.Basic

set_option warningAsError true

/-! # Source-faithful BLS12-381 base-field square roots -/

namespace Challenge.Bls12381.ProofSupport.Fp

open PrimeField

theorem p_mod_four : EvmSemantics.Crypto.Bls12381.p % 4 = 3 := by
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

/-- Exact source call `Fp.sqrt(a) = _modexp(a, P_PLUS_1_DIV_4)`. -/
def sqrtCanonical (a : Limbs) : Limbs :=
  montgomeryPowDecoded a pPlus1Div4Bytes

theorem canonical_sqrtCanonical {a : Limbs} (ha : Canonical a) :
    Canonical (sqrtCanonical a) :=
  canonical_montgomeryPowDecoded ha pPlus1Div4Bytes

/-- The source call refines to the fixed square-root exponent. -/
theorem lawful_sqrtCanonical_pow {a : Limbs} (ha : Canonical a) :
    (value (sqrtCanonical a) : LawfulFp) =
      (value a : LawfulFp) ^
        ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) := by
  rw [sqrtCanonical, lawful_montgomeryPowDecoded ha,
    bytesValue_pPlus1Div4Bytes]

@[simp] theorem lawful_sqrtCanonical_zero {a : Limbs} (ha : Canonical a)
    (hzero : value a = 0) :
    (value (sqrtCanonical a) : LawfulFp) = 0 := by
  rw [lawful_sqrtCanonical_pow ha, hzero]
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

/-- Canonical-value zero test corresponding to the source's zero fast path.
The byte-level equivalence to `LimbMath.isZeroBytes` belongs to codec/wire
refinement. -/
def isZeroValue (a : Limbs) : Bool := value a == 0

/-- Canonical-value equality corresponding to the source's final hash equality.
Its equivalence to equality of the canonical 48-byte encodings belongs to
codec/wire refinement. -/
def eqCanonicalValue (a b : Limbs) : Bool := value a == value b

/-- Source control flow: zero fast path, square root, square-back, equality. -/
def isSquareCanonical (a : Limbs) : Bool :=
  if isZeroValue a then true
  else
    let root := sqrtCanonical a
    let check := squareCanonical root
    eqCanonicalValue check a

@[simp] theorem isZeroValue_eq_true (a : Limbs) :
    isZeroValue a = true ↔ value a = 0 := by
  simp [isZeroValue]

@[simp] theorem eqCanonicalValue_eq_true (a b : Limbs) :
    eqCanonicalValue a b = true ↔ value a = value b := by
  simp [eqCanonicalValue]

@[simp] theorem isSquareCanonical_zero {a : Limbs} (hzero : value a = 0) :
    isSquareCanonical a = true := by
  simp [isSquareCanonical, isZeroValue, hzero]

/-- In a field of the certified BLS modulus, the source exponent squares back
to a square input.  The zero case is included. -/
theorem lawful_sqrt_pow_square_of_isSquare (x : LawfulFp)
    (hsquare : IsSquare x) :
    (x ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4)) ^ 2 = x := by
  rcases hsquare with ⟨y, rfl⟩
  by_cases hy : y = 0
  · rw [hy]
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  · have hexponent :
        2 * ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) * 2 =
          (EvmSemantics.Crypto.Bls12381.p - 1) + 2 := by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU]
    calc
      ((y * y) ^ ((EvmSemantics.Crypto.Bls12381.p + 1) / 4)) ^ 2 =
          y ^ (2 * ((EvmSemantics.Crypto.Bls12381.p + 1) / 4) * 2) := by
            simp only [← pow_two, ← pow_mul]
      _ = y ^ ((EvmSemantics.Crypto.Bls12381.p - 1) + 2) := by
        rw [hexponent]
      _ = y ^ (EvmSemantics.Crypto.Bls12381.p - 1) * y ^ 2 :=
        pow_add _ _ _
      _ = y * y := by
        rw [ZMod.pow_card_sub_one_eq_one hy]
        simp [pow_two]

theorem lawful_squareCanonical {a : Limbs} (ha : Canonical a) :
    (value (squareCanonical a) : LawfulFp) =
      (value a : LawfulFp) ^ 2 := by
  rw [← finEquiv_toField, toField_squareCanonical ha, map_pow,
    finEquiv_toField]

/-- Square-back verification for every canonical quadratic residue. -/
theorem lawful_square_sqrtCanonical {a : Limbs} (ha : Canonical a)
    (hsquare : IsSquare (value a : LawfulFp)) :
    (value (squareCanonical (sqrtCanonical a)) : LawfulFp) =
      (value a : LawfulFp) := by
  rw [lawful_squareCanonical (canonical_sqrtCanonical ha),
    lawful_sqrtCanonical_pow ha]
  exact lawful_sqrt_pow_square_of_isSquare _ hsquare

theorem value_eq_of_lawful_eq {a b : Limbs} (ha : Canonical a)
    (hb : Canonical b)
    (hvalue : (value a : LawfulFp) = (value b : LawfulFp)) :
    value a = value b := by
  have hmod : Nat.ModEq EvmSemantics.Crypto.Bls12381.p (value a) (value b) :=
    (ZMod.natCast_eq_natCast_iff _ _
      EvmSemantics.Crypto.Bls12381.p).mp hvalue
  exact hmod.eq_of_lt_of_lt ha.2 hb.2

/-- Exact canonical-limb square-back result consumed by extension-field square
root algorithms. -/
theorem square_sqrtCanonical {a : Limbs} (ha : Canonical a)
    (hsquare : IsSquare (value a : LawfulFp)) :
    squareCanonical (sqrtCanonical a) = a := by
  apply limbs_ext_of_value_eq
  exact value_eq_of_lawful_eq
    (canonical_squareCanonical (canonical_sqrtCanonical ha)) ha
    (lawful_square_sqrtCanonical ha hsquare)

theorem isSquareCanonical_sound {a : Limbs} (ha : Canonical a)
    (hsquare : isSquareCanonical a = true) :
    IsSquare (value a : LawfulFp) := by
  unfold isSquareCanonical at hsquare
  split at hsquare
  next hzero =>
    have hvalueZero := (isZeroValue_eq_true a).mp hzero
    rw [hvalueZero]
    exact ⟨0, by simp⟩
  next hnonzero =>
    have hvalue := (eqCanonicalValue_eq_true _ _).mp hsquare
    refine ⟨(value (sqrtCanonical a) : LawfulFp), ?_⟩
    have hcast := congrArg (fun n : Nat => (n : LawfulFp)) hvalue
    rw [lawful_squareCanonical (canonical_sqrtCanonical ha)] at hcast
    simpa only [pow_two] using hcast.symm

theorem isSquareCanonical_complete {a : Limbs} (ha : Canonical a)
    (hsquare : IsSquare (value a : LawfulFp)) :
    isSquareCanonical a = true := by
  by_cases hzero : value a = 0
  · exact isSquareCanonical_zero hzero
  · rw [isSquareCanonical, if_neg (by simpa using hzero)]
    apply (eqCanonicalValue_eq_true _ _).2
    exact value_eq_of_lawful_eq
      (canonical_squareCanonical (canonical_sqrtCanonical ha)) ha
      (lawful_square_sqrtCanonical ha hsquare)

theorem isSquareCanonical_iff {a : Limbs} (ha : Canonical a) :
    isSquareCanonical a = true ↔
      IsSquare (value a : LawfulFp) := by
  constructor
  · exact isSquareCanonical_sound ha
  · exact isSquareCanonical_complete ha

end Challenge.Bls12381.ProofSupport.Fp
