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
private theorem prime7 : Nat.Prime 7 := by decide +kernel
private theorem prime41 : Nat.Prime 41 := by decide +kernel
private theorem prime43 : Nat.Prime 43 := by decide +kernel
private theorem prime53 : Nat.Prime 53 := by decide +kernel
private theorem prime97 : Nat.Prime 97 := by decide +kernel
private theorem prime151 : Nat.Prime 151 := by decide +kernel
private theorem prime191 : Nat.Prime 191 := by decide +kernel
private theorem prime409 : Nat.Prime 409 := by decide +kernel
private theorem prime449 : Nat.Prime 449 := by decide +kernel

theorem prime3373 : Nat.Prime 3373 := by
  apply prime_of_modPow_lucas_factors 3373 5 [2, 2, 3, 281]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, prime281, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 5 ((3373 - 1) / 2) 3373 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime1453 : Nat.Prime 1453 := by
  apply prime_of_modPow_lucas_factors 1453 2 [2, 2, 3, 11, 11]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, prime11,
      prime11, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 2 ((1453 - 1) / 2) 1453 ≠ 1 := by
      bls_norm_mod_pow
    have h11 : Precompile.modPow 2 ((1453 - 1) / 11) 1453 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, h11, h11, by simp⟩

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
    have h2 : Precompile.modPow 2 ((2741 - 1) / 2) 2741 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime7577 : Nat.Prime 7577 := by
  apply prime_of_modPow_lucas_factors 7577 3 [2, 2, 2, 947]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, prime947, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 3 ((7577 - 1) / 2) 7577 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, by bls_norm_mod_pow, by simp⟩

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
    have h2 : Precompile.modPow 6 ((8101 - 1) / 2) 8101 ≠ 1 := by
      bls_norm_mod_pow
    have h3 : Precompile.modPow 6 ((8101 - 1) / 3) 8101 ≠ 1 := by
      bls_norm_mod_pow
    have h5 : Precompile.modPow 6 ((8101 - 1) / 5) 8101 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h3, h3, h3, h3, h5, h5, by simp⟩

theorem prime1151 : Nat.Prime 1151 := by
  apply prime_of_modPow_lucas_factors 1151 17 [2, 5, 5, 23]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime5, prime5, prime23, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h5 : Precompile.modPow 17 ((1151 - 1) / 5) 1151 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨by bls_norm_mod_pow, h5, h5, by bls_norm_mod_pow, by simp⟩

theorem prime1686913 : Nat.Prime 1686913 := by
  apply prime_of_modPow_lucas_factors 1686913 10
    [2, 2, 2, 2, 2, 2, 2, 3, 23, 191]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_two,
      Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_three,
      prime23, prime191, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 10 ((1686913 - 1) / 2) 1686913 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h2, h2, h2, h2, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime16447 : Nat.Prime 16447 := by
  apply prime_of_modPow_lucas_factors 16447 3 [2, 3, 2741]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime2741, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime43591 : Nat.Prime 43591 := by
  apply prime_of_modPow_lucas_factors 43591 11 [2, 3, 5, 1453]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime5, prime1453, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime927093389 : Nat.Prime 927093389 := by
  apply prime_of_modPow_lucas_factors 927093389 3 [2, 2, 13, 409, 43591]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, prime13, prime409, prime43591, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 3 ((927093389 - 1) / 2) 927093389 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime51376543 : Nat.Prime 51376543 := by
  apply prime_of_modPow_lucas_factors 51376543 3 [2, 3, 7, 151, 8101]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime7, prime151, prime8101, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime755057 : Nat.Prime 755057 := by
  apply prime_of_modPow_lucas_factors 755057 3 [2, 2, 2, 2, 41, 1151]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_two,
      prime41, prime1151, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 3 ((755057 - 1) / 2) 755057 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h2, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

theorem prime421987 : Nat.Prime 421987 := by
  apply prime_of_modPow_lucas_factors 421987 2 [2, 3, 53, 1327]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, prime53, prime1327, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime47737 : Nat.Prime 47737 := by
  apply prime_of_modPow_lucas_factors 47737 5 [2, 2, 2, 3, 3, 3, 13, 17]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_three,
      Nat.prime_three, Nat.prime_three, prime13, prime17, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 5 ((47737 - 1) / 2) 47737 ≠ 1 := by
      bls_norm_mod_pow
    have h3 : Precompile.modPow 5 ((47737 - 1) / 3) 47737 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h3, h3, h3, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime609743 : Nat.Prime 609743 := by
  apply prime_of_modPow_lucas_factors 609743 5 [2, 7, 97, 449]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime7, prime97, prime449, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime10177 : Nat.Prime 10177 := by
  apply prime_of_modPow_lucas_factors 10177 7 [2, 2, 2, 2, 2, 2, 3, 53]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_two, Nat.prime_two, Nat.prime_two,
      Nat.prime_two, Nat.prime_two, Nat.prime_three, prime53, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h2 : Precompile.modPow 7 ((10177 - 1) / 2) 10177 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨h2, h2, h2, h2, h2, h2, by bls_norm_mod_pow,
      by bls_norm_mod_pow, by simp⟩

theorem prime859267 : Nat.Prime 859267 := by
  apply prime_of_modPow_lucas_factors 859267 2 [2, 3, 3, 47737]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, Nat.prime_three, Nat.prime_three, prime47737, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    have h3 : Precompile.modPow 2 ((859267 - 1) / 3) 859267 ≠ 1 := by
      bls_norm_mod_pow
    exact ⟨by bls_norm_mod_pow, h3, h3, by bls_norm_mod_pow, by simp⟩

theorem prime52437899 : Nat.Prime 52437899 := by
  apply prime_of_modPow_lucas_factors 52437899 2 [2, 43, 609743]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Nat.prime_two, prime43, prime609743, by simp⟩
  · bls_norm_mod_pow
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by bls_norm_mod_pow, by bls_norm_mod_pow, by bls_norm_mod_pow, by simp⟩

end Challenge.Bls12381.ProofSupport.PrimeCertificate
