import Challenge.Bls12381.ProofSupport.FpBarrettSchedule

set_option warningAsError true

/-!
# BLS12-381 fixed Barrett quotient

This module identifies the two quotient words produced by the source-level
schedule with the high two words of `(x / 2^256) * mu`.  The proof is split
into small opaque declarations so checking the final theorem does not replay
the schedule reconstruction's larger proof term.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- The low three words discarded by the Barrett quotient fit below the
three-word divisor. -/
theorem barrettLower_lt (product : SchoolbookProduct) :
    let partials := barrettPartials product
    let l1 := barrettL1 partials
    let l2 := barrettL2 partials
    partials.p00.lo.toNat + Challenge.EvmProof.Limbs.radix * l1.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 2 * l2.word.toNat <
      Challenge.EvmProof.Limbs.radix ^ 3 := by
  exact Challenge.EvmProof.Limbs.threeWords_lt _ _ _

/-- Regroup the reconstructed schedule around the three discarded words. -/
theorem barrettSchedule_regroup (product : SchoolbookProduct) :
    let partials := barrettPartials product
    let l1 := barrettL1 partials
    let l2 := barrettL2 partials
    let l3 := barrettL3 partials
    (product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat) *
        barrettMu =
      (partials.p00.lo.toNat +
        Challenge.EvmProof.Limbs.radix * l1.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 2 * l2.word.toNat) +
      Challenge.EvmProof.Limbs.radix ^ 3 *
        (l3.word.toNat + Challenge.EvmProof.Limbs.radix *
          (partials.p12.hi.toNat + l3.carry.toNat)) := by
  dsimp only
  rw [barrettSchedule_value product]
  simp only [pow_succ]
  ring

/-- Dividing the schedule by three words leaves exactly its two quotient
words. -/
theorem barrettSchedule_div (product : SchoolbookProduct) :
    ((product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat) *
        barrettMu) / Challenge.EvmProof.Limbs.radix ^ 3 =
      let partials := barrettPartials product
      let l3 := barrettL3 partials
      l3.word.toNat + Challenge.EvmProof.Limbs.radix *
        (partials.p12.hi.toNat + l3.carry.toNat) := by
  rw [barrettSchedule_regroup product]
  rw [Nat.add_mul_div_left _ _
    (pow_pos Challenge.EvmProof.Limbs.radix_pos 3)]
  rw [Nat.div_eq_of_lt (barrettLower_lt product), Nat.zero_add]

/-- The quotient structure reconstructs the same two schedule words. -/
theorem barrettQuotient_value_eq_schedule (product : SchoolbookProduct) :
    (barrettQuotient product).value =
      let partials := barrettPartials product
      let l3 := barrettL3 partials
      l3.word.toNat + Challenge.EvmProof.Limbs.radix *
        (partials.p12.hi.toNat + l3.carry.toNat) := by
  have hq1 := barrettQuotient_q1_value product
  change (barrettQuotient product).q1.toNat =
    (barrettPartials product).p12.hi.toNat +
      (barrettL3 (barrettPartials product)).carry.toNat at hq1
  unfold BarrettQuotient.value
  change (barrettL3 (barrettPartials product)).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (barrettQuotient product).q1.toNat = _
  rw [hq1]

/-- The source-level quotient words reconstruct the mathematical Barrett
quotient `((x / 2^256) * mu) / 2^768`. -/
theorem value_barrettQuotient (product : SchoolbookProduct) :
    (barrettQuotient product).value =
      ((product.r1.toNat + Challenge.EvmProof.Limbs.radix *
          product.r2.toNat) * barrettMu) /
        Challenge.EvmProof.Limbs.radix ^ 3 := by
  rw [barrettQuotient_value_eq_schedule, barrettSchedule_div]

end Challenge.Bls12381.ProofSupport.Fp
