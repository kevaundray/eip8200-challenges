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

/-- Canonical two-word encoding of a natural reduced modulo the BLS base-field
modulus.  This is the representation-level boundary used by arithmetic below;
unlike `ofField`, it does not perform a field operation and is therefore a
useful target for later EVM carry/borrow and Barrett-reduction refinements. -/
def normalize (n : Nat) : Limbs :=
  let reduced := n % p
  { hi := UInt256.ofNat (reduced / Challenge.EvmProof.Limbs.radix)
    lo := UInt256.ofNat reduced }

theorem p_lt_radix_sq : p < Challenge.EvmProof.Limbs.radix ^ 2 := by
  norm_num [p, absU, Challenge.EvmProof.Limbs.radix]

theorem field_lt_radix_sq (a : Fp) :
    a.val < Challenge.EvmProof.Limbs.radix ^ 2 :=
  a.isLt.trans p_lt_radix_sq

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
