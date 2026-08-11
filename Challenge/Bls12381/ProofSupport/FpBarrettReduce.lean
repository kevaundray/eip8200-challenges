import Challenge.Bls12381.ProofSupport.FpBarrettSubtract

set_option warningAsError true

/-!
# BLS12-381 Barrett corrective subtractions

This module models the two identical source conditionals which subtract the
fixed modulus when the current two-word remainder is at least `p`.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- One exact source correction: compute the high-first EVM comparison word
and, when nonzero, execute the low-word subtraction with propagated borrow. -/
def barrettCorrectOnce (remainder : Challenge.EvmProof.Limbs.WideProduct) :
    Challenge.EvmProof.Limbs.WideProduct :=
  Challenge.EvmProof.Limbs.conditionalSubWide256 remainder modulusWords

/-- The two identical correction blocks emitted by `Fp.sol`. -/
def barrettReduce (product : SchoolbookProduct) :
    Challenge.EvmProof.Limbs.WideProduct :=
  barrettCorrectOnce (barrettCorrectOnce (barrettRemainder product))

/-- One source correction subtracts `p` exactly when the current remainder is
at least `p`. -/
theorem value_barrettCorrectOnce
    (remainder : Challenge.EvmProof.Limbs.WideProduct) :
    (barrettCorrectOnce remainder).value =
      if EvmSemantics.Crypto.Bls12381.p ≤ remainder.value then
        remainder.value - EvmSemantics.Crypto.Bls12381.p
      else remainder.value := by
  unfold barrettCorrectOnce
  rw [Challenge.EvmProof.Limbs.conditionalSubWide256_value,
    modulusWords_value]

/-- Two conditional subtractions compute reduction modulo `p` for every
input below `3p`. -/
theorem twoConditionalSubtractions_eq_mod {n : Nat}
    (hn : n < 3 * EvmSemantics.Crypto.Bls12381.p) :
    (if EvmSemantics.Crypto.Bls12381.p ≤
        (if EvmSemantics.Crypto.Bls12381.p ≤ n then
          n - EvmSemantics.Crypto.Bls12381.p else n) then
      (if EvmSemantics.Crypto.Bls12381.p ≤ n then
          n - EvmSemantics.Crypto.Bls12381.p else n) -
        EvmSemantics.Crypto.Bls12381.p
    else
      if EvmSemantics.Crypto.Bls12381.p ≤ n then
        n - EvmSemantics.Crypto.Bls12381.p else n) =
      n % EvmSemantics.Crypto.Bls12381.p := by
  have hp : 0 < EvmSemantics.Crypto.Bls12381.p := by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  by_cases hsmall : n < EvmSemantics.Crypto.Bls12381.p
  · rw [if_neg (Nat.not_le_of_lt hsmall),
      if_neg (Nat.not_le_of_lt hsmall), Nat.mod_eq_of_lt hsmall]
  · have hge : EvmSemantics.Crypto.Bls12381.p ≤ n := by omega
    by_cases hmiddle : n < 2 * EvmSemantics.Crypto.Bls12381.p
    · have hdifference : n - EvmSemantics.Crypto.Bls12381.p <
          EvmSemantics.Crypto.Bls12381.p := by omega
      rw [if_pos hge, if_neg (Nat.not_le_of_lt hdifference)]
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hdifference]
    · have hsecond : EvmSemantics.Crypto.Bls12381.p ≤
          n - EvmSemantics.Crypto.Bls12381.p := by omega
      have hdifference : n - EvmSemantics.Crypto.Bls12381.p -
          EvmSemantics.Crypto.Bls12381.p <
            EvmSemantics.Crypto.Bls12381.p := by omega
      rw [if_pos hge, if_pos hsecond]
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_sub_mod hsecond,
        Nat.mod_eq_of_lt hdifference]

/-- The source quotient, initial subtraction, and two correction blocks
reconstruct the full product modulo the fixed BLS base-field modulus. -/
theorem value_barrettReduce (product : SchoolbookProduct)
    (hproduct : product.value < EvmSemantics.Crypto.Bls12381.p ^ 2) :
    (barrettReduce product).value =
      product.value % EvmSemantics.Crypto.Bls12381.p := by
  let remainder := product.value -
    (barrettQuotient product).value * EvmSemantics.Crypto.Bls12381.p
  have hremainderValue := value_barrettRemainder product hproduct
  change (barrettRemainder product).value = remainder at hremainderValue
  have hremainderLt : remainder <
      3 * EvmSemantics.Crypto.Bls12381.p := by
    exact barrettRemainder_lt_three_mul_modulus product hproduct
  have hremainderMod : remainder % EvmSemantics.Crypto.Bls12381.p =
      product.value % EvmSemantics.Crypto.Bls12381.p := by
    have hmultiple := barrettQuotient_mul_modulus_le product
    have hsplit : remainder +
        (barrettQuotient product).value *
          EvmSemantics.Crypto.Bls12381.p = product.value := by
      exact Nat.sub_add_cancel hmultiple
    calc
      remainder % EvmSemantics.Crypto.Bls12381.p =
          (remainder + (barrettQuotient product).value *
            EvmSemantics.Crypto.Bls12381.p) %
              EvmSemantics.Crypto.Bls12381.p := by
                simp [Nat.add_mod]
      _ = product.value % EvmSemantics.Crypto.Bls12381.p := by rw [hsplit]
  unfold barrettReduce
  rw [value_barrettCorrectOnce, value_barrettCorrectOnce, hremainderValue]
  rw [twoConditionalSubtractions_eq_mod hremainderLt, hremainderMod]

end Challenge.Bls12381.ProofSupport.Fp
