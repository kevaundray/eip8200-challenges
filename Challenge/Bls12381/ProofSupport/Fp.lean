import Challenge.EvmProof.Limbs
import Challenge.EvmProof.Word
import EvmSemantics.Crypto.Bls12381.Curve
import Mathlib.Tactic.NormNum

set_option warningAsError true

/-!
# BLS12-381 base-field representation

Evmification stores a canonical 381-bit field element as a 128-bit high limb
and a 256-bit low limb. This module isolates that representation from concrete
program execution.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

structure Limbs where
  hi : UInt256
  lo : UInt256
deriving DecidableEq, Repr

def value (a : Limbs) : Nat :=
  a.lo.toNat + Challenge.EvmProof.Limbs.radix * a.hi.toNat

def ofField (a : Fp) : Limbs :=
  { hi := UInt256.ofNat (a.val / Challenge.EvmProof.Limbs.radix)
    lo := UInt256.ofNat a.val }

def toField (a : Limbs) : Fp := Fin.ofNat p (value a)

def Refines (a : Limbs) (fieldValue : Fp) : Prop := toField a = fieldValue

def Canonical (a : Limbs) : Prop :=
  a.hi.toNat < 2 ^ 128 ∧ value a < p

/-- Three EVM words holding the unreduced product of two canonical base-field
values, least-significant word first. -/
structure SchoolbookProduct where
  r2 : UInt256
  r1 : UInt256
  r0 : UInt256
deriving DecidableEq, Repr

namespace SchoolbookProduct

def value (product : SchoolbookProduct) : Nat :=
  product.r0.toNat + Challenge.EvmProof.Limbs.radix * product.r1.toNat +
    Challenge.EvmProof.Limbs.radix ^ 2 * product.r2.toNat

end SchoolbookProduct

/-- The exact two-limb schoolbook schedule in `Fp.sol`.  Each partial product
uses the source's `MUL`/`MULMOD` full-word idiom and the middle word uses the
same pair of wrapped additions and overflow tests. -/
def schoolbookProduct (a b : Limbs) : SchoolbookProduct :=
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  let top := p10.hi + p01.hi + (a.hi * b.hi + middle.carry)
  { r2 := top, r1 := middle.word, r0 := p00.lo }

/-- Natural value accumulated into the source's top product word before the
final wrapped `ADD`s.  Canonical operands make this strictly less than one EVM
word, which is the crucial no-overflow obligation. -/
def schoolbookTop (a b : Limbs) : Nat :=
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  p10.hi.toNat + p01.hi.toNat + a.hi.toNat * b.hi.toNat + middle.carry.toNat

/-! ## Fixed Barrett constants from `Fp.sol` -/

def modulusLo : UInt256 := UInt256.ofNat
  0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

def modulusHi : UInt256 := UInt256.ofNat
  0x1a0111ea397fe69a4b1ba7b6434bacd7

def barrettMu0 : UInt256 := UInt256.ofNat
  0xad397b918f6ff20d533b6c08511c60e2757079ace6bd401859778ceb4dabc4f8

def barrettMu1 : UInt256 := UInt256.ofNat
  0x1b82741ff6a0a94bdf4771e0286779d3997167a058f1c07b13e207f56591ba2e

def barrettMu2 : UInt256 := UInt256.ofNat
  0x9d835d2f3cc9e45ce28101b0cc7a6ba29

def barrettMu : Nat :=
  barrettMu0.toNat + Challenge.EvmProof.Limbs.radix * barrettMu1.toNat +
    Challenge.EvmProof.Limbs.radix ^ 2 * barrettMu2.toNat

theorem modulus_words :
    modulusLo.toNat + Challenge.EvmProof.Limbs.radix * modulusHi.toNat = p := by
  norm_num [modulusLo, modulusHi, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix, p, absU]

theorem barrettMu_words :
    barrettMu = barrettMu0.toNat +
      Challenge.EvmProof.Limbs.radix * barrettMu1.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 * barrettMu2.toNat := rfl

theorem barrettMu_eq_floor :
    barrettMu = Challenge.EvmProof.Limbs.radix ^ 4 / p := by
  norm_num [barrettMu, barrettMu0, barrettMu1, barrettMu2,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Limbs.radix, p, absU]

theorem schoolbookTop_lt {a b : Limbs} (ha : Canonical a) (hb : Canonical b) :
    schoolbookTop a b < Challenge.EvmProof.Limbs.radix := by
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  let topNat := p10.hi.toNat + p01.hi.toNat +
    a.hi.toNat * b.hi.toNat + middle.carry.toNat
  have h00 := Challenge.EvmProof.Limbs.fullMul256_value a.lo b.lo
  have h10 := Challenge.EvmProof.Limbs.fullMul256_value a.hi b.lo
  have h01 := Challenge.EvmProof.Limbs.fullMul256_value a.lo b.hi
  have hmiddle := Challenge.EvmProof.Limbs.addThree256_value
    p00.hi p10.lo p01.lo
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * p00.hi.toNat =
    a.lo.toNat * b.lo.toNat at h00
  change p10.lo.toNat + Challenge.EvmProof.Limbs.radix * p10.hi.toNat =
    a.hi.toNat * b.lo.toNat at h10
  change p01.lo.toNat + Challenge.EvmProof.Limbs.radix * p01.hi.toNat =
    a.lo.toNat * b.hi.toNat at h01
  change middle.word.toNat + Challenge.EvmProof.Limbs.radix *
    middle.carry.toNat = p00.hi.toNat + p10.lo.toNat + p01.lo.toNat at hmiddle
  have hreconstruct :
      value a * value b =
        p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
          Challenge.EvmProof.Limbs.radix ^ 2 * topNat := by
    calc
      value a * value b =
          (a.lo.toNat + Challenge.EvmProof.Limbs.radix * a.hi.toNat) *
            (b.lo.toNat + Challenge.EvmProof.Limbs.radix * b.hi.toNat) := rfl
      _ = a.lo.toNat * b.lo.toNat + Challenge.EvmProof.Limbs.radix *
            (a.hi.toNat * b.lo.toNat + a.lo.toNat * b.hi.toNat) +
          Challenge.EvmProof.Limbs.radix ^ 2 *
            (a.hi.toNat * b.hi.toNat) := by ring
      _ = p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
          Challenge.EvmProof.Limbs.radix ^ 2 * topNat := by
        unfold topNat
        nlinarith [h00, h10, h01, hmiddle]
  have hpSq : p ^ 2 < Challenge.EvmProof.Limbs.radix ^ 3 := by
    norm_num [p, absU, Challenge.EvmProof.Limbs.radix]
  have hproduct : value a * value b < p ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_lt_of_lt ha.2 hb.2
  have htop : topNat < Challenge.EvmProof.Limbs.radix := by
    rw [hreconstruct] at hproduct
    nlinarith [hproduct.trans hpSq]
  change topNat < Challenge.EvmProof.Limbs.radix
  exact htop

theorem schoolbookProduct_r2_value {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    (schoolbookProduct a b).r2.toNat = schoolbookTop a b := by
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  have htop := schoolbookTop_lt ha hb
  change p10.hi.toNat + p01.hi.toNat + a.hi.toNat * b.hi.toNat +
    middle.carry.toNat < Challenge.EvmProof.Limbs.radix at htop
  have hmidBound : a.hi.toNat * b.hi.toNat <
      Challenge.EvmProof.Limbs.radix := by omega
  have hmid : (a.hi * b.hi).toNat = a.hi.toNat * b.hi.toNat := by
    change (a.hi.val * b.hi.val).val = _
    rw [Fin.val_mul]
    exact Nat.mod_eq_of_lt hmidBound
  have hleft : p10.hi.toNat + p01.hi.toNat <
      Challenge.EvmProof.Limbs.radix := by omega
  have hright : a.hi.toNat * b.hi.toNat + middle.carry.toNat <
      Challenge.EvmProof.Limbs.radix := by omega
  change (p10.hi + p01.hi + (a.hi * b.hi + middle.carry)).toNat =
    schoolbookTop a b
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [hmid, show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl]
  rw [Nat.mod_eq_of_lt hright, Nat.mod_eq_of_lt hleft]
  have htop' : p10.hi.toNat + p01.hi.toNat +
      (a.hi.toNat * b.hi.toNat + middle.carry.toNat) <
        Challenge.EvmProof.Limbs.radix := by omega
  rw [Nat.mod_eq_of_lt htop']
  simp [schoolbookTop, p00, p10, p01, middle, Nat.add_assoc]

theorem schoolbookProduct_r2_lt {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    (schoolbookProduct a b).r2.toNat < Challenge.EvmProof.Limbs.radix := by
  rw [schoolbookProduct_r2_value ha hb]
  exact schoolbookTop_lt ha hb

theorem value_schoolbookProduct {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    (schoolbookProduct a b).value = value a * value b := by
  let p00 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.lo
  let p10 := Challenge.EvmProof.Limbs.fullMul256 a.hi b.lo
  let p01 := Challenge.EvmProof.Limbs.fullMul256 a.lo b.hi
  let middle := Challenge.EvmProof.Limbs.addThree256 p00.hi p10.lo p01.lo
  have h00 := Challenge.EvmProof.Limbs.fullMul256_value a.lo b.lo
  have h10 := Challenge.EvmProof.Limbs.fullMul256_value a.hi b.lo
  have h01 := Challenge.EvmProof.Limbs.fullMul256_value a.lo b.hi
  have hmiddle := Challenge.EvmProof.Limbs.addThree256_value
    p00.hi p10.lo p01.lo
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * p00.hi.toNat =
    a.lo.toNat * b.lo.toNat at h00
  change p10.lo.toNat + Challenge.EvmProof.Limbs.radix * p10.hi.toNat =
    a.hi.toNat * b.lo.toNat at h10
  change p01.lo.toNat + Challenge.EvmProof.Limbs.radix * p01.hi.toNat =
    a.lo.toNat * b.hi.toNat at h01
  change middle.word.toNat + Challenge.EvmProof.Limbs.radix *
    middle.carry.toNat = p00.hi.toNat + p10.lo.toNat + p01.lo.toNat at hmiddle
  have hr2 : (schoolbookProduct a b).r2.toNat = schoolbookTop a b :=
    schoolbookProduct_r2_value ha hb
  unfold SchoolbookProduct.value
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 * (schoolbookProduct a b).r2.toNat =
    value a * value b
  rw [hr2]
  unfold schoolbookTop
  change p00.lo.toNat + Challenge.EvmProof.Limbs.radix * middle.word.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 *
        (p10.hi.toNat + p01.hi.toNat + a.hi.toNat * b.hi.toNat +
          middle.carry.toNat) = value a * value b
  unfold value
  nlinarith [h00, h10, h01, hmiddle]

/-- Canonical two-word encoding of a natural reduced modulo the BLS base-field
modulus.  This is the representation-level boundary used by arithmetic below;
unlike `ofField`, it does not perform a field operation and is therefore a
useful target for later EVM carry/borrow and Barrett-reduction refinements. -/
def normalize (n : Nat) : Limbs :=
  let reduced := n % p
  { hi := UInt256.ofNat (reduced / Challenge.EvmProof.Limbs.radix)
    lo := UInt256.ofNat reduced }

/-- Split a known-bounded natural into the concrete high/low EVM words without
performing field reduction.  Concrete carry, borrow, and reduction routines
target this constructor. -/
def pack (n : Nat) : Limbs :=
  { hi := UInt256.ofNat (n / Challenge.EvmProof.Limbs.radix)
    lo := UInt256.ofNat n }

theorem p_lt_radix_sq : p < Challenge.EvmProof.Limbs.radix ^ 2 := by
  norm_num [p, absU, Challenge.EvmProof.Limbs.radix]

theorem field_lt_radix_sq (a : Fp) :
    a.val < Challenge.EvmProof.Limbs.radix ^ 2 :=
  a.isLt.trans p_lt_radix_sq

@[simp] theorem value_pack {n : Nat}
    (hn : n < Challenge.EvmProof.Limbs.radix ^ 2) : value (pack n) = n := by
  have hhi := Challenge.EvmProof.Limbs.splitTwo_high_lt hn
  change n / Challenge.EvmProof.Limbs.radix <
    Challenge.EvmProof.Limbs.radix at hhi
  unfold value pack
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  change n % Challenge.EvmProof.Limbs.radix +
      Challenge.EvmProof.Limbs.radix *
        (n / Challenge.EvmProof.Limbs.radix %
          Challenge.EvmProof.Limbs.radix) = n
  rw [Nat.mod_eq_of_lt hhi]
  exact Nat.mod_add_div n Challenge.EvmProof.Limbs.radix

@[simp] theorem value_ofField (a : Fp) : value (ofField a) = a.val := by
  have hhi := Challenge.EvmProof.Limbs.splitTwo_high_lt (field_lt_radix_sq a)
  change a.val / Challenge.EvmProof.Limbs.radix <
    Challenge.EvmProof.Limbs.radix at hhi
  unfold value ofField
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  change a.val % Challenge.EvmProof.Limbs.radix +
      Challenge.EvmProof.Limbs.radix *
        ((a.val / Challenge.EvmProof.Limbs.radix) %
          Challenge.EvmProof.Limbs.radix) = a.val
  rw [Nat.mod_eq_of_lt hhi]
  exact Nat.mod_add_div a.val Challenge.EvmProof.Limbs.radix

@[simp] theorem value_normalize (n : Nat) : value (normalize n) = n % p := by
  have hreduced : n % p < Challenge.EvmProof.Limbs.radix ^ 2 :=
    (Nat.mod_lt n (by norm_num [p, absU])).trans p_lt_radix_sq
  have hhi := Challenge.EvmProof.Limbs.splitTwo_high_lt hreduced
  change (n % p) / Challenge.EvmProof.Limbs.radix <
    Challenge.EvmProof.Limbs.radix at hhi
  unfold value normalize
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  change (n % p) % Challenge.EvmProof.Limbs.radix +
      Challenge.EvmProof.Limbs.radix *
        ((n % p) / Challenge.EvmProof.Limbs.radix %
          Challenge.EvmProof.Limbs.radix) = n % p
  rw [Nat.mod_eq_of_lt hhi]
  exact Nat.mod_add_div (n % p) Challenge.EvmProof.Limbs.radix

theorem canonical_pack {n : Nat} (hn : n < p) : Canonical (pack n) := by
  constructor
  · unfold pack
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    have hdiv : n / Challenge.EvmProof.Limbs.radix < 2 ^ 128 := by
      rw [Nat.div_lt_iff_lt_mul Challenge.EvmProof.Limbs.radix_pos]
      have hp : p < Challenge.EvmProof.Limbs.radix * 2 ^ 128 := by
        norm_num [p, absU, Challenge.EvmProof.Limbs.radix]
      exact hn.trans hp
    rw [Nat.mod_eq_of_lt (hdiv.trans (by norm_num))]
    exact hdiv
  · rw [value_pack (hn.trans p_lt_radix_sq)]
    exact hn

theorem canonical_normalize (n : Nat) : Canonical (normalize n) := by
  have hp0 : 0 < p := by norm_num [p, absU]
  have hn : n % p < p := Nat.mod_lt n hp0
  unfold normalize
  exact canonical_pack hn

@[simp] theorem toField_normalize (n : Nat) :
    toField (normalize n) = Fin.ofNat p n := by
  apply Fin.ext
  simp [toField]

@[simp] theorem toField_ofField (a : Fp) : toField (ofField a) = a := by
  apply Fin.ext
  simp [toField]

theorem refines_ofField (a : Fp) : Refines (ofField a) a := by
  simp [Refines]

theorem canonical_ofField (a : Fp) : Canonical (ofField a) := by
  constructor
  · unfold ofField
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    have hdiv : a.val / Challenge.EvmProof.Limbs.radix < 2 ^ 128 := by
      rw [Nat.div_lt_iff_lt_mul Challenge.EvmProof.Limbs.radix_pos]
      have hp : p < Challenge.EvmProof.Limbs.radix * 2 ^ 128 := by
        norm_num [p, absU, Challenge.EvmProof.Limbs.radix]
      exact a.isLt.trans hp
    rw [Nat.mod_eq_of_lt (hdiv.trans (by norm_num))]
    exact hdiv
  · rw [value_ofField]
    exact a.isLt

/-- Representation-level field operations.  Their definitions expose the
natural-number reduction which concrete EVM carry/borrow and multiplication
routines must refine; they do not call the semantic field operations. -/
def add (a b : Limbs) : Limbs := normalize (value a + value b)
def sub (a b : Limbs) : Limbs := normalize (p - value b % p + value a)
def mul (a b : Limbs) : Limbs := normalize (value a * value b)
def neg (a : Limbs) : Limbs := normalize (p - value a % p)

/-- Mathematical exponentiation boundary.  This deliberately remains separate
from the future limb-level square-and-multiply implementation. -/
def PowSpec (a : Limbs) (exponent : Nat) : Fp :=
  Fin.ofNat p (value a ^ exponent)

/-- Canonical representation of `PowSpec`; not an implementation claim. -/
def powSpecRepr (a : Limbs) (exponent : Nat) : Limbs :=
  normalize (value a ^ exponent)

@[simp] theorem toField_powSpecRepr (a : Limbs) (exponent : Nat) :
    toField (powSpecRepr a exponent) = PowSpec a exponent := by
  simp [powSpecRepr, PowSpec]

/-- Carry-friendly addition for canonical operands.  The only reduction is
one conditional subtraction, matching the concrete two-word EVM routine. -/
def addCanonical (a b : Limbs) : Limbs :=
  let total := value a + value b
  if total < p then pack total else pack (total - p)

/-- Borrow-friendly subtraction for canonical operands.  Underflow is repaired
with one conditional addition of the modulus. -/
def subCanonical (a b : Limbs) : Limbs :=
  if value b ≤ value a then pack (value a - value b)
  else pack (p + value a - value b)

theorem value_addCanonical {a b : Limbs}
    (ha : Canonical a) (hb : Canonical b) :
    value (addCanonical a b) = (value a + value b) % p := by
  have hp0 : 0 < p := by norm_num [p, absU]
  have htotal : value a + value b < 2 * p := by
    have ha' := ha.2
    have hb' := hb.2
    omega
  simp only [addCanonical]
  split_ifs with hlt
  · rw [value_pack ((hlt.trans p_lt_radix_sq))]
    exact (Nat.mod_eq_of_lt hlt).symm
  · have hred : value a + value b - p < p := by omega
    rw [value_pack (hred.trans p_lt_radix_sq)]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hred]

theorem value_subCanonical {a b : Limbs}
    (ha : Canonical a) (_hb : Canonical b) :
    value (subCanonical a b) = (p + value a - value b) % p := by
  have hp0 : 0 < p := by norm_num [p, absU]
  unfold subCanonical
  split_ifs with hle
  · have hdiff : value a - value b < p :=
      (Nat.sub_le _ _).trans_lt ha.2
    rw [value_pack (hdiff.trans p_lt_radix_sq)]
    have heq : p + value a - value b = p + (value a - value b) := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt hdiff]
    exact (Nat.mod_eq_of_lt hdiff).symm
  · have hred : p + value a - value b < p := by omega
    rw [value_pack (hred.trans p_lt_radix_sq), Nat.mod_eq_of_lt hred]

theorem refines_add (a b : Limbs) : Refines (add a b) (toField a + toField b) := by
  apply Fin.ext
  simp [add, toField, Fin.add_def, Nat.add_mod]

theorem refines_sub (a b : Limbs) : Refines (sub a b) (toField a - toField b) := by
  apply Fin.ext
  simp [sub, toField, Fin.sub_def]

theorem refines_mul (a b : Limbs) : Refines (mul a b) (toField a * toField b) := by
  apply Fin.ext
  simp [mul, toField, Fin.mul_def, Nat.mul_mod]

theorem refines_neg (a : Limbs) : Refines (neg a) (-toField a) := by
  apply Fin.ext
  simp [neg, toField, Fin.neg_def]

@[simp] theorem toField_add (a b : Limbs) :
    toField (add a b) = toField a + toField b := by
  simpa only [Refines] using refines_add a b

@[simp] theorem toField_sub (a b : Limbs) :
    toField (sub a b) = toField a - toField b := by
  simpa only [Refines] using refines_sub a b

@[simp] theorem toField_mul (a b : Limbs) :
    toField (mul a b) = toField a * toField b := by
  simpa only [Refines] using refines_mul a b

@[simp] theorem toField_neg (a : Limbs) :
    toField (neg a) = -toField a := by
  simpa only [Refines] using refines_neg a

end Challenge.Bls12381.ProofSupport.Fp
