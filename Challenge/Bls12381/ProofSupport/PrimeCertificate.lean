import Challenge.Bls12381.ProofSupport.PrimeField

set_option warningAsError true

/-!
# Kernel-checked BLS12-381 primality certificate

The certificate is assembled bottom-up from shallow Lucas nodes.  Concrete
modular powers are checked by the terminating square-and-multiply evaluator,
one recursion equation at a time; this avoids expanding a linear `Monoid.pow`
term or trusting a native evaluator.
-/

namespace Challenge.Bls12381.ProofSupport.PrimeCertificate

open EvmSemantics.EVM
open PrimeField

/-- Reduce one concrete fast modular-power computation in logarithmically
many kernel-checked steps. -/
macro "bls_norm_mod_pow" : tactic =>
  `(tactic|
    (unfold Precompile.modPow
     norm_num
     repeat
       rw [Precompile.modPowAux]
       norm_num))

private theorem prime281 : Nat.Prime 281 := by decide +kernel
private theorem prime137 : Nat.Prime 137 := by decide +kernel
private theorem prime947 : Nat.Prime 947 := by decide +kernel
private theorem prime67 : Nat.Prime 67 := by decide +kernel
private theorem prime4349 : Nat.Prime 4349 := by decide +kernel
private theorem prime5 : Nat.Prime 5 := by decide +kernel
private theorem prime11 : Nat.Prime 11 := by decide +kernel
private theorem prime13 : Nat.Prime 13 := by decide +kernel
private theorem prime17 : Nat.Prime 17 := by decide +kernel
private theorem prime23 : Nat.Prime 23 := by decide +kernel

theorem prime3373 : Nat.Prime 3373 := by
  apply prime_of_modPow_lucas_factors 3373 5 [2, 2, 3, 281]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, prime281, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime1453 : Nat.Prime 1453 := by
  apply prime_of_modPow_lucas_factors 1453 2 [2, 2, 3, 11, 11]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, prime11,
      prime11, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime1327 : Nat.Prime 1327 := by
  apply prime_of_modPow_lucas_factors 1327 3 [2, 3, 13, 17]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime13, prime17, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime2741 : Nat.Prime 2741 := by
  apply prime_of_modPow_lucas_factors 2741 2 [2, 2, 5, 137]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, prime5, prime137, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime7577 : Nat.Prime 7577 := by
  apply prime_of_modPow_lucas_factors 7577 3 [2, 2, 2, 947]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, prime947, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime582767 : Nat.Prime 582767 := by
  apply prime_of_modPow_lucas_factors 582767 5 [2, 67, 4349]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime67, prime4349, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime8101 : Nat.Prime 8101 := by
  apply prime_of_modPow_lucas_factors 8101 6 [2, 2, 3, 3, 3, 3, 5, 5]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, Nat.prime_three,
      Nat.prime_three, Nat.prime_three, prime5, prime5, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime1151 : Nat.Prime 1151 := by
  apply prime_of_modPow_lucas_factors 1151 17 [2, 5, 5, 23]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime5, prime5, prime23, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate
