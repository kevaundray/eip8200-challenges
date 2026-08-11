import Challenge.Bls12381.ProofSupport.FpMontgomeryReduceBound

set_option warningAsError true

/-! # BLS12-381 CIOS reduction source value -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

/-- Under the three-word numerator bound, all three nested source top-word
`ADD`s are nonwrapping. -/
theorem montgomeryReduceStep_t1_value (state : MontgomeryState)
    (hbound : montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    (montgomeryReduceStep state).t1.toNat =
      montgomeryReductionTopNat state := by
  have htop := montgomeryReductionTopNat_lt state hbound
  unfold montgomeryReductionTopNat at htop
  have hcarries :
      (montgomeryReductionHighSum state).carry.toNat +
          (montgomeryReductionShiftedSum state).carry.toNat <
        Challenge.EvmProof.Limbs.radix := by omega
  have hhigh : (montgomeryReductionHighProduct state).hi.toNat +
        ((montgomeryReductionHighSum state).carry.toNat +
          (montgomeryReductionShiftedSum state).carry.toNat) <
      Challenge.EvmProof.Limbs.radix := by omega
  have hall : state.t2.toNat +
        ((montgomeryReductionHighProduct state).hi.toNat +
          ((montgomeryReductionHighSum state).carry.toNat +
            (montgomeryReductionShiftedSum state).carry.toNat)) <
      Challenge.EvmProof.Limbs.radix := by omega
  change (state.t2 +
      ((montgomeryReductionHighProduct state).hi +
        ((montgomeryReductionHighSum state).carry +
          (montgomeryReductionShiftedSum state).carry))).toNat =
    montgomeryReductionTopNat state
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [show 2 ^ 256 = Challenge.EvmProof.Limbs.radix by rfl,
    Nat.mod_eq_of_lt hcarries, Nat.mod_eq_of_lt hhigh,
    Nat.mod_eq_of_lt hall]
  simp [montgomeryReductionTopNat, Nat.add_assoc]

/-- The exact source state reconstructs the unwrapped two-word quotient. -/
theorem montgomeryReduceStep_value (state : MontgomeryState)
    (hbound : montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    (montgomeryReduceStep state).value =
      montgomeryReductionQuotient state := by
  have htop := montgomeryReduceStep_t1_value state hbound
  unfold MontgomeryState.value
  change (montgomeryReductionShiftedSum state).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (montgomeryReduceStep state).t1.toNat +
      Challenge.EvmProof.Limbs.radix ^ 2 * (UInt256.ofNat 0).toNat = _
  rw [htop, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod,
    Nat.mul_zero, Nat.add_zero]
  rfl

/-- One exact source reduction divides the reconstructed numerator by one
word radix. -/
theorem montgomeryReduceStep_scaled (state : MontgomeryState)
    (hbound : montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    Challenge.EvmProof.Limbs.radix * (montgomeryReduceStep state).value =
      montgomeryReductionNumerator state := by
  rw [montgomeryReduceStep_value state hbound]
  exact montgomeryReduction_reconstruct_numerator state

end Challenge.Bls12381.ProofSupport.Fp
