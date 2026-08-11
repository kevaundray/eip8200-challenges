import Challenge.Bls12381.ProofSupport.FpMontgomerySecond

set_option warningAsError true

/-! # Final conditional subtraction in BLS12-381 `montMul2` -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics
open EvmSemantics.Crypto.Bls12381

/-- Fixed modulus pair in the same low/high order as the source result. -/
def montgomeryModulusWords : Challenge.EvmProof.Limbs.WideProduct :=
  { lo := modulusLo, hi := modulusHi }

@[simp] theorem montgomeryModulusWords_value :
    montgomeryModulusWords.value = p := by
  unfold montgomeryModulusWords Challenge.EvmProof.Limbs.WideProduct.value
  exact modulus_words

/-- Exact source subtraction block.  In particular, the borrow is the source
`GT(_n0,z0)`, rather than a normalized semantic comparison. -/
def montgomeryFinalSubModulus
    (result : Challenge.EvmProof.Limbs.WideProduct) :
    Challenge.EvmProof.Limbs.WideProduct :=
  let newZ0 := result.lo - modulusLo
  { hi := result.hi - modulusHi - UInt256.gt modulusLo result.lo
    lo := newZ0 }

theorem montgomeryFinalSubModulus_eq_subWide256
    (result : Challenge.EvmProof.Limbs.WideProduct) :
    montgomeryFinalSubModulus result =
      Challenge.EvmProof.Limbs.subWide256 result montgomeryModulusWords := rfl

/-- Exact high-first source comparison and conditional subtraction. -/
def montgomeryFinalCorrect
    (result : Challenge.EvmProof.Limbs.WideProduct) :
    Challenge.EvmProof.Limbs.WideProduct :=
  if (Challenge.EvmProof.Limbs.wideGeWord result
      montgomeryModulusWords).toNat ≠ 0 then
    montgomeryFinalSubModulus result
  else result

/-- One final source correction subtracts `p` exactly when needed. -/
theorem montgomeryFinalCorrect_value
    (result : Challenge.EvmProof.Limbs.WideProduct) :
    (montgomeryFinalCorrect result).value =
      if p ≤ result.value then result.value - p else result.value := by
  unfold montgomeryFinalCorrect
  have hcondition :
      (Challenge.EvmProof.Limbs.wideGeWord result
          montgomeryModulusWords).toNat ≠ 0 ↔ p ≤ result.value := by
    rw [Challenge.EvmProof.Limbs.wideGeWord_nonzero_iff,
      montgomeryModulusWords_value]
  by_cases hge : p ≤ result.value
  · rw [if_pos (hcondition.mpr hge), if_pos hge,
      montgomeryFinalSubModulus_eq_subWide256,
      Challenge.EvmProof.Limbs.subWide256_value,
      montgomeryModulusWords_value, if_pos hge]
  · rw [if_neg (mt hcondition.mp hge), if_neg hge]

/-- Low/high pair output by the second exact CIOS reduction. -/
def montgomeryResultWords (x y : Limbs) :
    Challenge.EvmProof.Limbs.WideProduct :=
  { lo := (montgomerySecondReduce x y).t0
    hi := (montgomerySecondReduce x y).t1 }

/-- Complete source-faithful `montMul2` word schedule. -/
def montMul2Words (x y : Limbs) : Challenge.EvmProof.Limbs.WideProduct :=
  montgomeryFinalCorrect (montgomeryResultWords x y)

end Challenge.Bls12381.ProofSupport.Fp
