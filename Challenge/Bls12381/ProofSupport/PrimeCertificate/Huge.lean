import Challenge.Bls12381.ProofSupport.PrimeCertificate.VeryLarge

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM
open PrimeField

theorem prime7259797099061183477 : Nat.Prime 7259797099061183477 := by
  apply prime_of_modPow_lucas_factors 7259797099061183477 2
    [2, 2, 941, 1928745244171409]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, prime941,
      prime1928745244171409, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 2
        ((7259797099061183477 - 1) / 2) 7259797099061183477 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime475709467 : Nat.Prime 475709467 := by
  apply prime_of_modPow_lucas_factors 475709467 2 [2, 3, 47, 1686913]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, by decide +kernel, prime1686913, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate
