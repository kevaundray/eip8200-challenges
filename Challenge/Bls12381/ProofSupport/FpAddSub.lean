import Challenge.Bls12381.ProofSupport.FpConstants

set_option warningAsError true

/-! # Source-faithful BLS12-381 base-field add/sub/neg schedules -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

def addRaw (a b : Limbs) : Limbs :=
  let sLo := a.lo + b.lo
  let carry := UInt256.lt sLo a.lo
  { hi := a.hi + b.hi + carry, lo := sLo }

def addNeedsCorrection (sum : Limbs) : UInt256 :=
  UInt256.lor (UInt256.gt sum.hi modulusHi)
    (UInt256.land (UInt256.eq sum.hi modulusHi)
      (UInt256.isZero (UInt256.lt sum.lo modulusLo)))

def addCorrect (sum : Limbs) : Limbs :=
  let newLo := sum.lo - modulusLo
  { hi := sum.hi - (modulusHi + UInt256.gt modulusLo sum.lo)
    lo := newLo }

def addSource (a b : Limbs) : Limbs :=
  let sum := addRaw a b
  if (addNeedsCorrection sum).toNat ≠ 0 then addCorrect sum else sum

def subRaw (a b : Limbs) : Limbs :=
  { hi := a.hi - b.hi - UInt256.gt b.lo a.lo
    lo := a.lo - b.lo }

def subRepair (diff : Limbs) : Limbs :=
  let newLo := diff.lo + modulusLo
  { hi := diff.hi + modulusHi + UInt256.lt newLo diff.lo
    lo := newLo }

def subSource (a b : Limbs) : Limbs :=
  let diff := subRaw a b
  if (UInt256.gt diff.hi modulusHi).toNat ≠ 0 then subRepair diff else diff

def negNonzero (a : Limbs) : Limbs :=
  { hi := modulusHi - a.hi - UInt256.gt a.lo modulusLo
    lo := modulusLo - a.lo }

def negSource (a : Limbs) : Limbs :=
  if a.hi.toNat = 0 ∧ a.lo.toNat = 0 then pack 0 else negNonzero a

def asWide (a : Limbs) : Challenge.EvmProof.Limbs.WideProduct :=
  { hi := a.hi, lo := a.lo }

def modulusWide : Challenge.EvmProof.Limbs.WideProduct :=
  { hi := modulusHi, lo := modulusLo }

@[simp] theorem asWide_value (a : Limbs) : (asWide a).value = value a := rfl

@[simp] theorem modulusWide_value :
    modulusWide.value = EvmSemantics.Crypto.Bls12381.p := modulus_words

theorem addNeedsCorrection_eq_wideGeWord (sum : Limbs) :
    addNeedsCorrection sum = Challenge.EvmProof.Limbs.wideGeWord
      (asWide sum) modulusWide := rfl

theorem asWide_addCorrect (sum : Limbs) :
    asWide (addCorrect sum) = Challenge.EvmProof.Limbs.subWide256
      (asWide sum) modulusWide := by
  rw [Challenge.EvmProof.Limbs.WideProduct.mk.injEq]
  constructor
  · apply Challenge.EvmProof.Word.word_ext
    change ((sum.hi.val - (modulusHi.val +
      (UInt256.gt modulusLo sum.lo).val)).val) =
      ((sum.hi.val - modulusHi.val -
        (UInt256.lt sum.lo modulusLo).val).val)
    simp [sub_eq_add_neg, add_assoc, add_comm, UInt256.gt, UInt256.lt]
  · rfl

theorem value_addRaw {a b : Limbs} (ha : Canonical a) (hb : Canonical b) :
    value (addRaw a b) = value a + value b := by
  have hai := ha.1
  have hbi := hb.1
  have hlow := Challenge.EvmProof.Limbs.addTwo256_value a.lo b.lo
  have habhi : a.hi.toNat + b.hi.toNat < 2 ^ 256 := by
    have hr : 2 ^ 128 + 2 ^ 128 < 2 ^ 256 := by norm_num
    omega
  have hhi : a.hi.toNat + b.hi.toNat +
      (UInt256.lt (a.lo + b.lo) a.lo).toNat <
        Challenge.EvmProof.Limbs.radix := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    have hr : 2 ^ 128 + 2 ^ 128 + 1 <
        Challenge.EvmProof.Limbs.radix := by
      norm_num [Challenge.EvmProof.Limbs.radix]
    split <;> omega
  have hhi' : a.hi.toNat + b.hi.toNat +
      (UInt256.lt (a.lo + b.lo) a.lo).toNat < 2 ^ 256 := by
    simpa [Challenge.EvmProof.Limbs.radix] using hhi
  unfold addRaw value
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [Nat.mod_eq_of_lt habhi, Nat.mod_eq_of_lt hhi']
  change (a.lo + b.lo).toNat + Challenge.EvmProof.Limbs.radix *
      (a.hi.toNat + b.hi.toNat +
        (UInt256.lt (a.lo + b.lo) a.lo).toNat) = _
  change (a.lo + b.lo).toNat + Challenge.EvmProof.Limbs.radix *
      (UInt256.lt (a.lo + b.lo) a.lo).toNat =
    a.lo.toNat + b.lo.toNat at hlow
  calc
    _ = ((a.lo + b.lo).toNat + Challenge.EvmProof.Limbs.radix *
        (UInt256.lt (a.lo + b.lo) a.lo).toNat) +
        Challenge.EvmProof.Limbs.radix *
          (a.hi.toNat + b.hi.toNat) := by ring
    _ = (a.lo.toNat + b.lo.toNat) +
        Challenge.EvmProof.Limbs.radix *
          (a.hi.toNat + b.hi.toNat) := by rw [hlow]
    _ = _ := by ring

theorem value_addSource {a b : Limbs} (ha : Canonical a) (hb : Canonical b) :
    value (addSource a b) = (value a + value b) %
      EvmSemantics.Crypto.Bls12381.p := by
  have hp0 : 0 < EvmSemantics.Crypto.Bls12381.p := by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  have htotal : value a + value b <
      2 * EvmSemantics.Crypto.Bls12381.p := by
    have hava := ha.2
    have havb := hb.2
    omega
  have hraw := value_addRaw ha hb
  unfold addSource
  let sum := addRaw a b
  by_cases hc : (addNeedsCorrection sum).toNat ≠ 0
  · rw [if_pos hc]
    have hge : EvmSemantics.Crypto.Bls12381.p ≤ value sum := by
      rw [addNeedsCorrection_eq_wideGeWord] at hc
      exact (Challenge.EvmProof.Limbs.wideGeWord_nonzero_iff _ _).mp hc
    have hcorrect := congrArg Challenge.EvmProof.Limbs.WideProduct.value
      (asWide_addCorrect sum)
    rw [asWide_value, Challenge.EvmProof.Limbs.subWide256_value,
      modulusWide_value, asWide_value, if_pos hge] at hcorrect
    have hsum : value sum = value a + value b := hraw
    rw [hsum] at hge hcorrect
    have hred : value a + value b - EvmSemantics.Crypto.Bls12381.p <
        EvmSemantics.Crypto.Bls12381.p := by omega
    rw [hcorrect, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hred]
  · rw [if_neg hc, hraw]
    have hlt : value a + value b < EvmSemantics.Crypto.Bls12381.p := by
      have hnge : ¬EvmSemantics.Crypto.Bls12381.p ≤ value sum := by
        intro hge
        apply hc
        rw [addNeedsCorrection_eq_wideGeWord]
        exact (Challenge.EvmProof.Limbs.wideGeWord_nonzero_iff _ _).mpr hge
      rw [hraw] at hnge
      omega
    exact (Nat.mod_eq_of_lt hlt).symm

theorem asWide_subRaw (a b : Limbs) :
    asWide (subRaw a b) = Challenge.EvmProof.Limbs.subWide256
      (asWide a) (asWide b) := rfl

theorem asWide_negNonzero (a : Limbs) :
    asWide (negNonzero a) = Challenge.EvmProof.Limbs.subWide256
      modulusWide (asWide a) := rfl

theorem value_negSource {a : Limbs} (ha : Canonical a) :
    value (negSource a) =
      (EvmSemantics.Crypto.Bls12381.p - value a) %
        EvmSemantics.Crypto.Bls12381.p := by
  unfold negSource
  by_cases hzero : a.hi.toNat = 0 ∧ a.lo.toNat = 0
  · rw [if_pos hzero]
    have havalue : value a = 0 := by simp [value, hzero.1, hzero.2]
    rw [value_pack (by
      norm_num [Challenge.EvmProof.Limbs.radix]), havalue]
    simp
  · rw [if_neg hzero]
    have hapos : 0 < value a := by
      unfold value
      have hr := Challenge.EvmProof.Limbs.radix_pos
      by_cases hhi : a.hi.toNat = 0
      · have hlo : 0 < a.lo.toNat := by omega
        omega
      · have hterm : 0 < Challenge.EvmProof.Limbs.radix * a.hi.toNat :=
          Nat.mul_pos hr (Nat.pos_of_ne_zero hhi)
        omega
    have hwide := congrArg Challenge.EvmProof.Limbs.WideProduct.value
      (asWide_negNonzero a)
    rw [asWide_value, Challenge.EvmProof.Limbs.subWide256_value,
      modulusWide_value, asWide_value, if_pos ha.2.le] at hwide
    have havalueLt := ha.2
    have hred : EvmSemantics.Crypto.Bls12381.p - value a <
        EvmSemantics.Crypto.Bls12381.p := by omega
    rw [hwide, Nat.mod_eq_of_lt hred]

end Challenge.Bls12381.ProofSupport.Fp
