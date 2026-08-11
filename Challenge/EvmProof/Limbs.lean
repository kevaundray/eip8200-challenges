import Challenge.EvmProof.Bytes
import Mathlib.Data.Nat.Digits.Lemmas
set_option warningAsError true
/-!
# Little-endian 256-bit limbs

The general MODEXP path stores an arbitrary-precision integer as consecutive
EVM words, least-significant word first.  This module gives that memory layout
a small mathematical interface.  It deliberately does not mention the
reference control flow, so all helper and loop certificates can share it.
-/

namespace Challenge.EvmProof.Limbs

open EvmSemantics

/-- Three little-endian digits reconstruct as the expected quadratic radix
polynomial. -/
theorem ofDigits_three (base x y z : Nat) :
    Nat.ofDigits base [x, y, z] = x + base * y + base ^ 2 * z := by
  simp [Nat.ofDigits_cons]
  ring

/-- Radix of one EVM word. -/
def radix : Nat := 2 ^ 256

/-- Number of 256-bit limbs required for a byte width. -/
def limbCount (width : Nat) : Nat := (width + 31) / 32

/-- The fixed-width little-endian radix expansion of `value`. -/
def limbDigits (count value : Nat) : List Nat :=
  Nat.digitsAppend radix count value

/-- Short family-neutral name for the fixed-width digits. -/
abbrev digits := limbDigits

/-- Consecutive little-endian EVM words read from memory. -/
def memoryLimbs (memory : ByteArray) (ptr count : Nat) : List Nat :=
  (List.range count).map fun i =>
    (MachineState.readWord memory (ptr + 32 * i)).toNat

/-- `memory[ptr .. ptr + 32*count]` is the fixed-width limb encoding of
`value`.  The explicit range premise rules out truncating high limbs. -/
def Represents (memory : ByteArray) (ptr count value : Nat) : Prop :=
  value < radix ^ count ∧ memoryLimbs memory ptr count = limbDigits count value

/-- Split a natural into its low word and remaining high part. -/
def splitTwo (value : Nat) : Nat × Nat :=
  (value % radix, value / radix)

/-- Reconstruct a two-limb value, low word first. -/
def joinTwo (limbs : Nat × Nat) : Nat :=
  limbs.1 + radix * limbs.2

/-! ## Width-generic word splitting

The concrete EVM algorithms below use 256-bit words, but the arithmetic facts
that justify splitting, carries, and reconstruction do not depend on that
width.  Keeping the base explicit makes the same lemmas reusable for smaller
test models and future word sizes.
-/

/-- Split a natural at an arbitrary positive word base, low word first. -/
def splitAt (base value : Nat) : Nat × Nat :=
  (value % base, value / base)

/-- Reconstruct a low/high pair at an arbitrary word base. -/
def joinAt (base : Nat) (words : Nat × Nat) : Nat :=
  words.1 + base * words.2

/-- Split the full natural-number product of two words at `base`. -/
def mulSplit (base a b : Nat) : Nat × Nat :=
  splitAt base (a * b)

/-- Add three words at an arbitrary base, retaining the two source-style
overflow bits as a (possibly two-valued) carry. -/
def addThreeAt (base x y z : Nat) : Nat × Nat :=
  let first := (x + y) % base
  let carry₁ := if first < x then 1 else 0
  let result := (first + z) % base
  let carry₂ := if result < first then 1 else 0
  (result, carry₁ + carry₂)

/-- Result word and carry word produced by the EVM's two-`ADD` accumulation
pattern.  The carry can be 0, 1, or 2. -/
structure WordSum where
  word : UInt256
  carry : UInt256
deriving DecidableEq, Repr

namespace WordSum

def value (sum : WordSum) : Nat :=
  sum.word.toNat + radix * sum.carry.toNat

/-- Append one source-style wrapped addition to an existing word/carry state. -/
def add (sum : WordSum) (term : UInt256) : WordSum :=
  let result := sum.word + term
  let overflow := UInt256.lt result sum.word
  { word := result, carry := sum.carry + overflow }

end WordSum

/-- Add three EVM words exactly as the source does: two wrapped `ADD`s and the
sum of their two `LT` overflow bits. -/
def addThree256 (x y z : UInt256) : WordSum :=
  let first := x + y
  let carry₁ := UInt256.lt first x
  let result := first + z
  let carry₂ := UInt256.lt result first
  { word := result, carry := carry₁ + carry₂ }

@[simp] theorem join_splitAt {base : Nat} (_hbase : 0 < base) (value : Nat) :
    joinAt base (splitAt base value) = value := by
  simpa [joinAt, splitAt] using Nat.mod_add_div value base

@[simp] theorem join_mulSplit {base : Nat} (hbase : 0 < base) (a b : Nat) :
    joinAt base (mulSplit base a b) = a * b := by
  exact join_splitAt hbase (a * b)

theorem splitAt_low_lt {base value : Nat} (hbase : 0 < base) :
    (splitAt base value).1 < base := by
  exact Nat.mod_lt value hbase

theorem mulSplit_high_lt {base a b : Nat} (hbase : 0 < base)
    (ha : a < base) (hb : b < base) :
    (mulSplit base a b).2 < base := by
  simp only [mulSplit, splitAt]
  rw [Nat.div_lt_iff_lt_mul hbase]
  nlinarith

/-! ## Source-faithful EVM full-word multiplication -/

/-- Two EVM words holding a 512-bit product, low word first. -/
structure WideProduct where
  hi : UInt256
  lo : UInt256
deriving DecidableEq, Repr

namespace WideProduct

/-- Reconstruct the natural value of a low/high EVM-word pair. -/
def value (product : WideProduct) : Nat :=
  product.lo.toNat + radix * product.hi.toNat

end WideProduct

/-- The exact EVM full-multiply idiom used by `Fp.sol`: the low word comes
from `MUL`, while the high word is recovered with `MULMOD (2^256-1)` and two
wrapped subtractions. -/
def fullMul256 (a b : UInt256) : WideProduct :=
  let lo := a * b
  let mm := UInt256.mulMod a b (UInt256.lnot (UInt256.ofNat 0))
  let borrow := UInt256.lt mm lo
  { hi := mm - lo - borrow, lo := lo }

/-- Exact two-word EVM subtraction schedule: subtract the low words, propagate
the `LT` borrow, then perform the two wrapped high-word `SUB`s. -/
def subWide256 (a b : WideProduct) : WideProduct :=
  let borrow := UInt256.lt a.lo b.lo
  { hi := a.hi - b.hi - borrow, lo := a.lo - b.lo }

/-- Low two words of the schoolbook product of two two-word values.  Terms at
word position two and above are deliberately discarded. -/
def mulWideLow256 (a b : WideProduct) : WideProduct :=
  let low := fullMul256 a.lo b.lo
  { hi := low.hi + a.lo * b.hi + a.hi * b.lo, lo := low.lo }

/-- Reconstructing the exact two-word EVM subtraction gives ordinary
subtraction when it does not underflow, and the radix-squared wrapped value
otherwise. -/
theorem subWide256_value (a b : WideProduct) :
    (subWide256 a b).value =
      if b.value ≤ a.value then a.value - b.value
      else radix ^ 2 + a.value - b.value := by
  have halo := a.lo.val.isLt
  have hahi := a.hi.val.isLt
  have hblo := b.lo.val.isLt
  have hbhi := b.hi.val.isLt
  change a.lo.toNat < radix at halo
  change a.hi.toNat < radix at hahi
  change b.lo.toNat < radix at hblo
  change b.hi.toNat < radix at hbhi
  unfold subWide256 WideProduct.value
  simp only [Challenge.EvmProof.Word.word_toNat_sub_cond,
    Challenge.EvmProof.Word.word_toNat_lt,
    show 2 ^ 256 = radix by rfl]
  unfold radix at *
  split_ifs <;> omega

theorem fullMul256_words_lt (a b : UInt256) :
    (fullMul256 a b).lo.toNat < radix ∧
      (fullMul256 a b).hi.toNat < radix := by
  exact ⟨(fullMul256 a b).lo.val.isLt, (fullMul256 a b).hi.val.isLt⟩

@[simp] theorem join_splitTwo (value : Nat) :
    joinTwo (splitTwo value) = value := by
  simpa [joinTwo, splitTwo] using Nat.mod_add_div value radix


theorem radix_eq : radix = 256 ^ 32 := by
  simp [radix]

theorem radix_gt_one : 1 < radix := by
  norm_num [radix]

theorem radix_pos : 0 < radix := by
  exact Nat.zero_lt_of_lt radix_gt_one

/-- Three EVM words always reconstruct below the three-word radix bound. -/
theorem threeWords_lt (x y z : UInt256) :
    x.toNat + radix * y.toNat + radix ^ 2 * z.toNat < radix ^ 3 := by
  rw [← ofDigits_three]
  apply Nat.ofDigits_lt_base_pow_length radix_gt_one
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro digit hdigit
  rcases hdigit with rfl | rfl | rfl
  · exact x.val.isLt
  · exact y.val.isLt
  · exact z.val.isLt

theorem splitTwo_low_lt (value : Nat) : (splitTwo value).1 < radix := by
  exact Nat.mod_lt _ radix_pos

theorem splitTwo_high_lt {value : Nat} (hvalue : value < radix ^ 2) :
    (splitTwo value).2 < radix := by
  rw [splitTwo]
  rw [Nat.div_lt_iff_lt_mul radix_pos]
  simpa [pow_two] using hvalue

theorem limbCount_le_32 (width : Nat) (hwidth : width ≤ 1024) :
    limbCount width ≤ 32 := by
  unfold limbCount
  omega

theorem width_le_limbs (width : Nat) : width ≤ 32 * limbCount width := by
  unfold limbCount
  omega

theorem limbCount_pos {width : Nat} (hwidth : 0 < width) :
    0 < limbCount width := by
  unfold limbCount
  omega

theorem pow_radix (count : Nat) :
    radix ^ count = 256 ^ (32 * count) := by
  rw [radix_eq, ← Nat.pow_mul]

theorem byteValue_fits (input : ByteArray) (offset width : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded input offset width <
      radix ^ limbCount width := by
  have hbytes := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    input offset width
  have hwidth := width_le_limbs width
  have hpow : 256 ^ width ≤ 256 ^ (32 * limbCount width) := by
    exact Nat.pow_le_pow_right (by omega) hwidth
  rw [pow_radix]
  exact hbytes.trans_le hpow

@[simp] theorem length_limbDigits {count value : Nat}
    (hvalue : value < radix ^ count) :
    (limbDigits count value).length = count := by
  exact Nat.length_digitsAppend radix_gt_one count hvalue

theorem limbDigits_lt {count value digit : Nat}
    (hdigit : digit ∈ limbDigits count value) : digit < radix := by
  exact Nat.lt_of_mem_digitsAppend radix_gt_one count digit hdigit

theorem value_limbDigits (count value : Nat) :
    Nat.ofDigits radix (limbDigits count value) = value := by
  rw [limbDigits, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
    Nat.ofDigits_digits]

theorem memoryLimb_lt (memory : ByteArray) (ptr count : Nat)
    {digit : Nat} (hdigit : digit ∈ memoryLimbs memory ptr count) :
    digit < radix := by
  simp only [memoryLimbs, List.mem_map] at hdigit
  rcases hdigit with ⟨i, _, rfl⟩
  exact (MachineState.readWord memory (ptr + 32 * i)).val.isLt

@[simp] theorem length_memoryLimbs (memory : ByteArray) (ptr count : Nat) :
    (memoryLimbs memory ptr count).length = count := by
  simp [memoryLimbs]

theorem value_of_represents {memory : ByteArray} {ptr count value : Nat}
    (hrep : Represents memory ptr count value) :
    Nat.ofDigits radix (memoryLimbs memory ptr count) = value := by
  rw [hrep.2, value_limbDigits]

theorem represents_value_unique {memory : ByteArray} {ptr count a b : Nat}
    (ha : Represents memory ptr count a) (hb : Represents memory ptr count b) :
    a = b := by
  rw [← value_of_represents ha, ← value_of_represents hb]

theorem represents_iff_value {memory : ByteArray} {ptr count value : Nat}
    (hvalue : value < radix ^ count) :
    Represents memory ptr count value ↔
      Nat.ofDigits radix (memoryLimbs memory ptr count) = value := by
  constructor
  · exact value_of_represents
  · intro heq
    refine ⟨hvalue, ?_⟩
    apply Nat.ofDigits_inj_of_len_eq radix_gt_one
    · rw [length_memoryLimbs, length_limbDigits hvalue]
    · exact fun digit hdigit => memoryLimb_lt _ _ _ hdigit
    · exact fun digit hdigit => limbDigits_lt hdigit
    · rw [heq, value_limbDigits]

/-! ## Arithmetic used by `addMaskedMod`

The bytecode adds either zero or one residue and then performs one conditional
subtraction.  These lemmas isolate the mathematical reason one subtraction is
enough from the word-by-word carry and borrow implementation proved below the
bytecode layer.
-/

theorem masked_sum_lt_twice {x y take modulus : Nat}
    (hx : x < modulus) (hy : y < modulus) (htake : take ≤ 1) :
    x + take * y < 2 * modulus := by
  interval_cases take <;> simp_all <;> omega

theorem masked_sum_lt_twice_of_le {x y take modulus : Nat}
    (hx : x < modulus) (hy : y ≤ modulus) (htake : take ≤ 1) :
    x + take * y < 2 * modulus := by
  interval_cases take <;> simp_all <;> omega

theorem mod_eq_cond_sub {total modulus : Nat}
    (htotal : total < 2 * modulus) :
    total % modulus = if total < modulus then total else total - modulus := by
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

@[simp] theorem join_addThreeAt {base x y z : Nat} (_hbase : 0 < base)
    (hx : x < base) (hy : y < base) (hz : z < base) :
    joinAt base (addThreeAt base x y z) = x + y + z := by
  have hxy : x + y < 2 * base := by omega
  simp only [addThreeAt]
  rw [mod_eq_cond_sub hxy]
  by_cases hfirst : x + y < base
  · simp only [hfirst, ↓reduceIte]
    have hfirstCarry : ¬x + y < x := by omega
    rw [if_neg hfirstCarry]
    have hxyz : x + y + z < 2 * base := by omega
    rw [mod_eq_cond_sub hxyz]
    by_cases hresult : x + y + z < base
    · simp [hresult, joinAt]
    · simp only [hresult, ↓reduceIte]
      have hoverflow : x + y + z - base < x + y := by omega
      simp [hoverflow, joinAt]
      omega
  · simp only [hfirst, ↓reduceIte]
    have hfirstOverflow : x + y - base < x := by omega
    rw [if_pos hfirstOverflow]
    have hnext : x + y - base + z < 2 * base := by omega
    rw [mod_eq_cond_sub hnext]
    by_cases hresult : x + y - base + z < base
    · simp only [hresult, ↓reduceIte]
      have hnotCarry : ¬x + y - base + z < x + y - base := by omega
      simp [hnotCarry, joinAt]
      omega
    · simp only [hresult, ↓reduceIte]
      have hoverflow : x + y - base + z - base < x + y - base := by omega
      simp [hoverflow, joinAt]
      omega

theorem addThree256_value (x y z : UInt256) :
    (addThree256 x y z).value = x.toNat + y.toNat + z.toNat := by
  unfold WordSum.value addThree256
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_lt]
  rw [show 2 ^ 256 = radix by rfl]
  have hcarry :
      (if (x.toNat + y.toNat) % radix < x.toNat then 1 else 0) +
          (if ((x.toNat + y.toNat) % radix + z.toNat) % radix <
            (x.toNat + y.toNat) % radix then 1 else 0) < radix := by
    split_ifs <;> norm_num [radix]
  rw [Nat.mod_eq_of_lt hcarry]
  convert join_addThreeAt (base := radix) radix_pos
      x.val.isLt y.val.isLt z.val.isLt using 1 <;>
    simp [joinAt, addThreeAt, UInt256.toNat]

theorem addThree256_carry_lt_three (x y z : UInt256) :
    (addThree256 x y z).carry.toNat < 3 := by
  unfold addThree256
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_lt]
  split_ifs <;> norm_num

theorem WordSum.value_add (sum : WordSum) (term : UInt256)
    (hcarry : sum.carry.toNat + 1 < radix) :
    (sum.add term).value = sum.value + term.toNat := by
  unfold WordSum.add WordSum.value
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_lt]
  rw [show 2 ^ 256 = radix by rfl]
  have hsumWord := sum.word.val.isLt
  have hterm := term.val.isLt
  change sum.word.toNat < radix at hsumWord
  change term.toNat < radix at hterm
  have hword : sum.word.toNat + term.toNat < 2 * radix := by
    omega
  rw [mod_eq_cond_sub hword]
  by_cases hoverflow : sum.word.toNat + term.toNat < radix
  · rw [if_pos hoverflow, if_neg (by omega), Nat.add_zero,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg hoverflow, if_pos (by omega),
      Nat.mod_eq_of_lt hcarry]
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem WordSum.carry_add_le (sum : WordSum) (term : UInt256)
    (hcarry : sum.carry.toNat + 1 < radix) :
    (sum.add term).carry.toNat ≤ sum.carry.toNat + 1 := by
  unfold WordSum.add
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_lt]
  rw [show 2 ^ 256 = radix by rfl]
  split_ifs <;> rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The high-word identity behind the EVM `mul`/`mulmod (base - 1)` trick.
The conditional subtraction is exactly the pair of wrapped `SUB`s used by the
source implementation. -/
theorem mulSplit_high_eq_mersenne {base a b : Nat} (hbase : 1 < base)
    (ha : a < base) (hb : b < base) :
    let words := mulSplit base a b
    let mm := (a * b) % (base - 1)
    (if mm < words.1 then base + mm - words.1 - 1 else mm - words.1) =
      words.2 := by
  dsimp only
  by_cases htwo : base = 2
  · subst base
    interval_cases a <;> interval_cases b <;>
      norm_num [mulSplit, splitAt]
  have hbase2 : 2 < base := by omega
  let lo := (mulSplit base a b).1
  let hi := (mulSplit base a b).2
  have hbase0 : 0 < base := by omega
  have hlo : lo < base := splitAt_low_lt hbase0
  have hhi : hi < base - 1 := by
    have ha' : a ≤ base - 1 := by omega
    have hb' : b ≤ base - 1 := by omega
    have hproduct : a * b ≤ (base - 1) * (base - 1) :=
      Nat.mul_le_mul ha' hb'
    have hstrict : a * b < (base - 1) * base :=
      hproduct.trans_lt ((Nat.mul_lt_mul_left (by omega : 0 < base - 1)).2
        (by omega : base - 1 < base))
    simpa [hi, mulSplit, splitAt, Nat.div_lt_iff_lt_mul hbase0]
      using hstrict
  have hreconstruct : lo + base * hi = a * b := by
    change joinAt base (mulSplit base a b) = a * b
    exact join_mulSplit hbase0 a b
  have hbaseMod : base % (base - 1) = 1 := by
    rw [Nat.mod_eq_sub_mod (by omega : base - 1 ≤ base)]
    have hdiff : base - (base - 1) = 1 := by omega
    rw [hdiff, Nat.mod_eq_of_lt (by omega)]
  have hmm : (a * b) % (base - 1) = (lo + hi) % (base - 1) := by
    have heq := congrArg (fun n => n % (base - 1)) hreconstruct
    simpa [Nat.add_mod, Nat.mul_mod, hbaseMod] using heq.symm
  have hsum : lo + hi < 2 * (base - 1) := by omega
  rw [hmm, mod_eq_cond_sub hsum]
  change (if (if lo + hi < base - 1 then lo + hi
      else lo + hi - (base - 1)) < lo then
        base + (if lo + hi < base - 1 then lo + hi
          else lo + hi - (base - 1)) - lo - 1
      else (if lo + hi < base - 1 then lo + hi
        else lo + hi - (base - 1)) - lo) = hi
  split_ifs <;> omega

theorem fullMul256_value (a b : UInt256) :
    (fullMul256 a b).value = a.toNat * b.toNat := by
  have hlo : (a * b).toNat = (a.toNat * b.toNat) % radix := by
    change (a.val * b.val).val = _
    rw [Fin.val_mul]
    rfl
  have hmax : (UInt256.lnot (UInt256.ofNat 0)).toNat = radix - 1 := by
    norm_num [UInt256.lnot, UInt256.ofNat, UInt256.toNat, UInt256.size, radix]
  have hmm :
      (UInt256.mulMod a b (UInt256.lnot (UInt256.ofNat 0))).toNat =
        (a.toNat * b.toNat) % (radix - 1) := by
    unfold UInt256.mulMod
    rw [if_neg]
    · rw [Challenge.EvmProof.Word.word_toNat_ofNat]
      rw [hmax]
      apply Nat.mod_eq_of_lt
      exact (Nat.mod_lt _ (by norm_num [radix])).trans
        (by norm_num [radix])
    · simpa [UInt256.toNat] using (show
        (UInt256.lnot (UInt256.ofNat 0)).toNat ≠ 0 by
          rw [hmax]
          norm_num [radix])
  unfold WideProduct.value fullMul256
  dsimp only
  rw [Challenge.EvmProof.Word.word_toNat_sub_cond]
  rw [Challenge.EvmProof.Word.word_toNat_lt]
  rw [Challenge.EvmProof.Word.word_toNat_sub_cond]
  rw [hlo, hmm]
  rw [show 2 ^ 256 = radix by rfl]
  have hhigh := mulSplit_high_eq_mersenne
    (base := radix) (a := a.toNat) (b := b.toNat)
    (by norm_num [radix]) a.val.isLt b.val.isLt
  dsimp only at hhigh
  simp only [mulSplit, splitAt] at hhigh
  have hloBound : a.toNat * b.toNat % radix < radix :=
    Nat.mod_lt _ radix_pos
  by_cases hborrow : a.toNat * b.toNat % (radix - 1) <
      a.toNat * b.toNat % radix
  · simp only [if_pos hborrow]
    rw [if_neg (by omega)]
    rw [if_pos hborrow] at hhigh
    rw [hhigh]
    simpa [joinAt, mulSplit, splitAt] using
      join_mulSplit (base := radix) radix_pos a.toNat b.toNat
  · simp only [if_neg hborrow, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    rw [if_neg hborrow] at hhigh
    rw [hhigh]
    simpa [joinAt, mulSplit, splitAt] using
      join_mulSplit (base := radix) radix_pos a.toNat b.toNat

/-- The source-style low product reconstructs multiplication modulo two EVM
words. -/
theorem mulWideLow256_value (a b : WideProduct) :
    (mulWideLow256 a b).value = (a.value * b.value) % radix ^ 2 := by
  let low := fullMul256 a.lo b.lo
  let cross := low.hi.toNat + a.lo.toNat * b.hi.toNat +
    a.hi.toNat * b.lo.toNat
  have hlow := fullMul256_value a.lo b.lo
  change low.value = a.lo.toNat * b.lo.toNat at hlow
  have hhi : (low.hi + a.lo * b.hi + a.hi * b.lo).toNat =
      cross % radix := by
    dsimp only [cross]
    simp only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_mul,
      show 2 ^ 256 = radix by rfl]
    simp [Nat.add_mod, Nat.mul_mod]
  have hcrossSplit : cross % radix + radix * (cross / radix) = cross :=
    Nat.mod_add_div cross radix
  have hresultLt : low.lo.toNat + radix * (cross % radix) < radix ^ 2 := by
    have hlo := low.lo.val.isLt
    have hcross := Nat.mod_lt cross radix_pos
    change low.lo.toNat < radix at hlo
    nlinarith
  have hdecomp : a.value * b.value =
      (low.lo.toNat + radix * (cross % radix)) +
        radix ^ 2 * (cross / radix + a.hi.toNat * b.hi.toNat) := by
    calc
      a.value * b.value =
          a.lo.toNat * b.lo.toNat + radix *
            (a.lo.toNat * b.hi.toNat + a.hi.toNat * b.lo.toNat) +
            radix ^ 2 * (a.hi.toNat * b.hi.toNat) := by
              unfold WideProduct.value
              ring
      _ = low.lo.toNat + radix * cross +
          radix ^ 2 * (a.hi.toNat * b.hi.toNat) := by
            unfold WideProduct.value at hlow
            rw [← hlow]
            dsimp only [cross]
            ring
      _ = (low.lo.toNat + radix * (cross % radix)) +
          radix ^ 2 * (cross / radix + a.hi.toNat * b.hi.toNat) := by
            nlinarith [hcrossSplit]
  unfold mulWideLow256
  change low.lo.toNat + radix *
      (low.hi + a.lo * b.hi + a.hi * b.lo).toNat =
        (a.value * b.value) % radix ^ 2
  rw [hhi, hdecomp, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hresultLt]

theorem masked_sum_mod_eq_cond_sub {x y take modulus : Nat}
    (hx : x < modulus) (hy : y < modulus) (htake : take ≤ 1) :
    (x + take * y) % modulus =
      if x + take * y < modulus then x + take * y
      else x + take * y - modulus := by
  exact mod_eq_cond_sub (masked_sum_lt_twice hx hy htake)

/-- The bytecode selects its subtraction candidate exactly when the
mathematical sum is at least the modulus.  The first disjunct is the final
carry out of the fixed-width addition; the second is a borrow-free comparison
of the wrapped sum with the modulus. -/
theorem useSub_iff {total modulus bound : Nat} (hmodulus : modulus < bound) :
    (bound ≤ total ∨ modulus ≤ total % bound) ↔ modulus ≤ total := by
  constructor
  · rintro (hcarry | hwrapped)
    · exact hmodulus.le.trans hcarry
    · exact hwrapped.trans (Nat.mod_le total bound)
  · intro htotal
    by_cases hcarry : bound ≤ total
    · exact Or.inl hcarry
    · right
      rwa [Nat.mod_eq_of_lt (Nat.lt_of_not_ge hcarry)]

/-! ## Canonical carry recurrence -/

/-- Add two equally-sized little-endian limb lists, returning the result limbs
and the carry beyond their common width. -/
def addDigitLists : List Nat → List Nat → Nat → List Nat × Nat
  | [], [], carry => ([], carry)
  | x :: xs, y :: ys, carry =>
      let total := x + y + carry
      let next := addDigitLists xs ys (total / radix)
      (total % radix :: next.1, next.2)
  | _, _, carry => ([], carry)

theorem length_addDigitLists_left {xs ys : List Nat} {carry : Nat}
    (hlength : xs.length = ys.length) :
    (addDigitLists xs ys carry).1.length = xs.length := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp [addDigitLists, ih hlength']

theorem addDigitLists_value {xs ys : List Nat} {carry : Nat}
    (hlength : xs.length = ys.length) :
    Nat.ofDigits radix (addDigitLists xs ys carry).1 +
        radix ^ xs.length * (addDigitLists xs ys carry).2 =
      Nat.ofDigits radix xs + Nat.ofDigits radix ys + carry := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          let total := x + y + carry
          let next := addDigitLists xs ys (total / radix)
          have hnext := ih (carry := total / radix) hlength'
          have hdivide := Nat.mod_add_div total radix
          simp only [addDigitLists, Nat.ofDigits_cons,
            List.length_cons, pow_succ]
          simp only [total] at hnext hdivide
          nlinarith

theorem addDigitLists_append_single {xs ys : List Nat} {carry x y : Nat}
    (hlength : xs.length = ys.length) :
    addDigitLists (xs ++ [x]) (ys ++ [y]) carry =
      let before := addDigitLists xs ys carry
      let total := x + y + before.2
      (before.1 ++ [total % radix], total / radix) := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlength
  | cons head xs ih =>
      cases ys with
      | nil => simp at hlength
      | cons other ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp only [List.cons_append, addDigitLists]
          rw [ih hlength']

theorem addDigitLists_digits_lt {xs ys : List Nat} {carry digit : Nat}
    (hdigit : digit ∈ (addDigitLists xs ys carry).1) : digit < radix := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all [addDigitLists]
      | cons y ys =>
          simp only [addDigitLists, List.mem_cons] at hdigit
          rcases hdigit with rfl | hdigit
          · exact Nat.mod_lt _ radix_pos
          · exact ih hdigit

theorem addDigitLists_carry_le_one {xs ys : List Nat} {carry : Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ digit ∈ xs, digit < radix)
    (hys : ∀ digit ∈ ys, digit < radix) (hcarry : carry ≤ 1) :
    (addDigitLists xs ys carry).2 ≤ 1 := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          have hx : x < radix := hxs x (by simp)
          have hy : y < radix := hys y (by simp)
          have hquotient : (x + y + carry) / radix ≤ 1 := by
            rw [Nat.div_le_iff_le_mul radix_pos]
            omega
          simp only [addDigitLists]
          exact ih hlength' (fun digit hdigit => hxs digit (by simp [hdigit]))
            (fun digit hdigit => hys digit (by simp [hdigit])) hquotient

theorem ofDigits_map_mul (digits : List Nat) (take : Nat) :
    Nat.ofDigits radix (digits.map (take * ·)) =
      take * Nat.ofDigits radix digits := by
  induction digits with
  | nil => simp
  | cons digit digits ih =>
      simp [Nat.ofDigits_cons, ih]
      ring

theorem addDigitLists_masked_value_mod {xs ys : List Nat} {take : Nat}
    (hlength : xs.length = ys.length) :
    Nat.ofDigits radix (addDigitLists xs (ys.map (take * ·)) 0).1 =
      (Nat.ofDigits radix xs + take * Nat.ofDigits radix ys) %
        radix ^ xs.length := by
  have hmaskedLength : xs.length = (ys.map (take * ·)).length := by
    simpa using hlength
  have hvalue := addDigitLists_value (carry := 0) hmaskedLength
  rw [ofDigits_map_mul] at hvalue
  simp only [Nat.add_zero] at hvalue
  have hresultLength := length_addDigitLists_left
    (carry := 0) hmaskedLength
  have hresultDigits : ∀ digit ∈
      (addDigitLists xs (ys.map (take * ·)) 0).1, digit < radix :=
    fun digit hdigit => addDigitLists_digits_lt hdigit
  have hresultLt :
      Nat.ofDigits radix (addDigitLists xs (ys.map (take * ·)) 0).1 <
        radix ^ xs.length := by
    rw [← hresultLength]
    exact Nat.ofDigits_lt_base_pow_length radix_gt_one hresultDigits
  rw [← hvalue, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
    Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  exact (Nat.mod_eq_of_lt hresultLt).symm

theorem addDigitLists_masked_carry_le_one {xs ys : List Nat} {take : Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ digit ∈ xs, digit < radix)
    (hys : ∀ digit ∈ ys, digit < radix) (htake : take ≤ 1) :
    (addDigitLists xs (ys.map (take * ·)) 0).2 ≤ 1 := by
  apply addDigitLists_carry_le_one (by simpa using hlength) hxs
  · intro digit hdigit
    simp only [List.mem_map] at hdigit
    rcases hdigit with ⟨source, hsource, rfl⟩
    have hsourceLt := hys source hsource
    interval_cases take
    · simpa using radix_pos
    · simpa using hsourceLt
  · omega

private theorem div_eq_one_of_le_of_lt_twice {value divisor : Nat}
    (_hdivisor : 0 < divisor) (hle : divisor ≤ value)
    (hlt : value < 2 * divisor) : value / divisor = 1 := by
  apply Nat.div_eq_of_lt_le
  · simpa using hle
  · omega

/-- The two EVM overflow tests in one `addMaskedMod` limb iteration compute
exactly the carry quotient of the three-term natural sum. -/
theorem addCarryBits {x y carry : Nat}
    (hx : x < radix) (hy : y < radix) (hcarry : carry ≤ 1) :
    ((if (x + y) % radix < x then 1 else 0) |||
        (if ((x + y) % radix + carry) % radix < (x + y) % radix
          then 1 else 0)) =
      (x + y + carry) / radix := by
  have hsum : x + y < 2 * radix := by omega
  by_cases hwrap : x + y < radix
  · rw [Nat.mod_eq_of_lt hwrap]
    have hnotFirst : ¬ x + y < x := by omega
    simp only [if_neg hnotFirst, Nat.zero_or]
    by_cases htotal : x + y + carry < radix
    · rw [Nat.mod_eq_of_lt htotal, if_neg (by omega),
        Nat.div_eq_of_lt htotal]
    · have htotalLe : radix ≤ x + y + carry := by omega
      have htotalTwo : x + y + carry < 2 * radix := by omega
      have hzero : x + y + carry - radix = 0 := by omega
      have hsumPos : 0 < x + y := by
        have := radix_gt_one
        omega
      rw [mod_eq_cond_sub htotalTwo, if_neg htotal,
        hzero, if_pos hsumPos,
        div_eq_one_of_le_of_lt_twice radix_pos htotalLe htotalTwo]
  · have hwrapLe : radix ≤ x + y := by omega
    rw [mod_eq_cond_sub hsum, if_neg hwrap]
    have hfirst : x + y - radix < x := by omega
    rw [if_pos hfirst]
    have hdiv : (x + y + carry) / radix = 1 :=
      div_eq_one_of_le_of_lt_twice radix_pos (by omega) (by omega)
    rw [hdiv]
    split <;> norm_num

/-! ## Canonical borrow recurrence -/

/-- Subtract the second equally-sized little-endian limb list from the first,
returning the wrapped result and the final borrow. -/
def subDigitLists : List Nat → List Nat → Nat → List Nat × Nat
  | [], [], borrow => ([], borrow)
  | x :: xs, y :: ys, borrow =>
      let nextBorrow := if x < y + borrow then 1 else 0
      let digit := x + radix * nextBorrow - y - borrow
      let next := subDigitLists xs ys nextBorrow
      (digit :: next.1, next.2)
  | _, _, borrow => ([], borrow)

theorem subDigitLists_append_single {xs ys : List Nat} {borrow x y : Nat}
    (hlength : xs.length = ys.length) :
    subDigitLists (xs ++ [x]) (ys ++ [y]) borrow =
      let before := subDigitLists xs ys borrow
      let nextBorrow := if x < y + before.2 then 1 else 0
      (before.1 ++ [x + radix * nextBorrow - y - before.2], nextBorrow) := by
  induction xs generalizing ys borrow with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlength
  | cons head xs ih =>
      cases ys with
      | nil => simp at hlength
      | cons other ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp only [List.cons_append, subDigitLists]
          rw [ih hlength']
          rfl

theorem subDigitLists_value {xs ys : List Nat} {borrow : Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ digit ∈ xs, digit < radix)
    (hys : ∀ digit ∈ ys, digit < radix) (hborrow : borrow ≤ 1) :
    Nat.ofDigits radix (subDigitLists xs ys borrow).1 +
        Nat.ofDigits radix ys + borrow =
      Nat.ofDigits radix xs +
        radix ^ xs.length * (subDigitLists xs ys borrow).2 := by
  induction xs generalizing ys borrow with
  | nil =>
      cases ys <;> simp_all [subDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          have hx : x < radix := hxs x (by simp)
          have hy : y < radix := hys y (by simp)
          let nextBorrow := if x < y + borrow then 1 else 0
          have hnextBorrow : nextBorrow ≤ 1 := by
            dsimp only [nextBorrow]
            split <;> omega
          have hstep :
              x + radix * nextBorrow - y - borrow + y + borrow =
                x + radix * nextBorrow := by
            dsimp only [nextBorrow]
            split <;> omega
          have hnext := ih hlength'
            (fun digit hdigit => hxs digit (by simp [hdigit]))
            (fun digit hdigit => hys digit (by simp [hdigit])) hnextBorrow
          simp only [subDigitLists, Nat.ofDigits_cons, List.length_cons,
            pow_succ]
          dsimp only [nextBorrow] at hstep hnext ⊢
          nlinarith

theorem subDigitLists_borrow_le_one {xs ys : List Nat} {borrow : Nat}
    (hlength : xs.length = ys.length) (hborrow : borrow ≤ 1) :
    (subDigitLists xs ys borrow).2 ≤ 1 := by
  induction xs generalizing ys borrow with
  | nil =>
      cases ys <;> simp_all [subDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp only [subDigitLists]
          exact ih hlength' (by split <;> simp)

theorem subDigitLists_digits_lt {xs ys : List Nat} {borrow digit : Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ value ∈ xs, value < radix)
    (hys : ∀ value ∈ ys, value < radix) (hborrow : borrow ≤ 1)
    (hdigit : digit ∈ (subDigitLists xs ys borrow).1) : digit < radix := by
  induction xs generalizing ys borrow digit with
  | nil =>
      cases ys <;> simp_all [subDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          have hx : x < radix := hxs x (by simp)
          have hy : y < radix := hys y (by simp)
          simp only [subDigitLists, List.mem_cons] at hdigit
          rcases hdigit with rfl | hdigit
          · split <;> omega
          · apply ih hlength'
              (fun value hvalue => hxs value (by simp [hvalue]))
              (fun value hvalue => hys value (by simp [hvalue]))
              (by split <;> simp) hdigit

/-- Natural-number specification of the EVM's two-stage `SUB`/`LT` borrow
sequence for one limb. -/
theorem subLimbBits {x y borrow : Nat}
    (hx : x < radix) (hy : y < radix) (hborrow : borrow ≤ 1) :
    let difference := if x < y then radix + x - y else x - y
    let digit := if difference < borrow then radix + difference - borrow
      else difference - borrow
    let nextBorrow := if x < y + borrow then 1 else 0
    digit = x + radix * nextBorrow - y - borrow ∧
      ((if x < y then 1 else 0) |||
        (if difference < borrow then 1 else 0)) = nextBorrow := by
  dsimp only
  interval_cases borrow
  · by_cases hxy : x < y
    · rw [if_pos hxy, if_neg (by omega), if_pos (by omega),
        if_pos hxy, if_neg (by omega)]
      constructor
      · omega
      · norm_num
    · rw [if_neg hxy, if_neg (by omega), if_neg (by omega),
        if_neg hxy, if_neg (by omega)]
      constructor <;> norm_num
  · by_cases hxy : x < y
    · have hdiffPos : 0 < radix + x - y := by omega
      rw [if_pos hxy, if_neg (by omega), if_pos (by omega),
        if_pos hxy, if_neg (by omega)]
      constructor
      · omega
      · norm_num
    · rw [if_neg hxy, if_neg hxy]
      by_cases heq : x = y
      · subst x
        rw [Nat.sub_self, if_pos (by omega), if_pos (by omega),
          if_pos (by omega)]
        constructor <;> norm_num
      · have hyxStrict : y < x := by omega
        have hdiffPos : 0 < x - y := by omega
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        constructor
        · omega
        · norm_num

end Challenge.EvmProof.Limbs
