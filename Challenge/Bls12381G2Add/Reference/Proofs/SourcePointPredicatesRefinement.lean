import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointPredicatesExec

set_option warningAsError true

/-! # Refinement of frozen G2ADD point predicates -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def PointPaddingZero (yst : EvmState) (point : U256) : Prop :=
  ((loadWord yst.memory point.toNat >>> 128) |||
    (loadWord yst.memory (point + BitVec.ofNat 256 64).toNat >>> 128)) |||
  ((loadWord yst.memory (point + BitVec.ofNat 256 128).toNat >>> 128) |||
    (loadWord yst.memory (point + BitVec.ofNat 256 192).toNat >>> 128)) = 0

private theorem b2w_eq_one_iff (condition : Bool) :
    b2w condition = 1 ↔ condition = true := by
  cases condition <;> decide

private theorem fp2ValidValue_zero_or_one' (yst : EvmState) (ptr : U256) :
    fp2ValidValue yst ptr = 0 ∨ fp2ValidValue yst ptr = 1 := by
  simp only [fp2ValidValue, fpValidValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpValidValue
    , b2w]
  split <;> split <;> decide

private theorem pointPaddingZeroValue_zero_or_one (yst : EvmState)
    (point : U256) :
    pointPaddingZeroValue yst point = 0 ∨
      pointPaddingZeroValue yst point = 1 := by
  unfold pointPaddingZeroValue
  simp only [b2w]
  split <;> decide

private theorem land_eq_one_iff_of_zero_or_one {a b : U256}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private theorem land_zero_or_one {a b : U256}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a &&& b = 0 ∨ a &&& b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem pointPaddingZeroValue_eq_one_iff (yst : EvmState) (point : U256) :
    pointPaddingZeroValue yst point = 1 ↔ PointPaddingZero yst point := by
  unfold pointPaddingZeroValue PointPaddingZero
  rw [b2w_eq_one_iff]
  simp

theorem pointValidValue_eq_one_iff (yst : EvmState) (point : U256) :
    pointValidValue yst point = 1 ↔
      Fp2.Canonical (fp2At yst point) ∧
      Fp2.Canonical (fp2At yst (point + BitVec.ofNat 256 128)) ∧
      PointPaddingZero yst point := by
  unfold pointValidValue
  rw [land_eq_one_iff_of_zero_or_one
    (land_zero_or_one
      (fp2ValidValue_zero_or_one' yst point)
      (fp2ValidValue_zero_or_one' yst (point + BitVec.ofNat 256 128)))
    (pointPaddingZeroValue_zero_or_one yst point)]
  rw [land_eq_one_iff_of_zero_or_one
    (fp2ValidValue_zero_or_one' yst point)
    (fp2ValidValue_zero_or_one' yst (point + BitVec.ofNat 256 128)),
    fp2ValidValue_eq_one_iff_canonical,
    fp2ValidValue_eq_one_iff_canonical,
    pointPaddingZeroValue_eq_one_iff]
  tauto

/-- A point-validity word is Boolean-valued.  Keeping this fact opaque avoids
reopening all five scalar validity tests when the main validation conjunction
is interpreted. -/
theorem pointValidValue_zero_or_one (yst : EvmState) (point : U256) :
    pointValidValue yst point = 0 ∨ pointValidValue yst point = 1 := by
  unfold pointValidValue
  exact land_zero_or_one
    (land_zero_or_one
      (fp2ValidValue_zero_or_one' yst point)
      (fp2ValidValue_zero_or_one' yst (point + BitVec.ofNat 256 128)))
    (pointPaddingZeroValue_zero_or_one yst point)

theorem pointZeroValue_eq_one_iff (yst : EvmState) (point : U256) :
    pointZeroValue yst point = 1 ↔
      fp2WordsAt yst point = fp2ZeroWords ∧
      fp2WordsAt yst (point + BitVec.ofNat 256 128) = fp2ZeroWords := by
  unfold pointZeroValue
  rw [land_eq_one_iff_of_zero_or_one
    (fp2ZeroValue_zero_or_one yst point)
    (fp2ZeroValue_zero_or_one yst (point + BitVec.ofNat 256 128)),
    fp2ZeroValue_eq_one_iff_words, fp2ZeroValue_eq_one_iff_words]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
