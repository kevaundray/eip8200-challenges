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

@[simp] theorem join_splitTwo (value : Nat) :
    joinTwo (splitTwo value) = value := by
  simpa [joinTwo, splitTwo] using Nat.mod_add_div value radix


theorem radix_eq : radix = 256 ^ 32 := by
  simp [radix]

theorem radix_gt_one : 1 < radix := by
  norm_num [radix]

theorem radix_pos : 0 < radix := by
  exact Nat.zero_lt_of_lt radix_gt_one

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

