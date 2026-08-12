import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddTotal
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFinitePredicates
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true

/-!
Lawful readback of the fixed high-memory point cells used by G2MSM.

The runtime represents infinity by eight zero words.  A finite point occupies
two canonical `Fp2` values in the following 128-byte halves.  Keeping this
adapter local to the G2MSM proof avoids adding another executable point type.
-/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

/-- Interpret one runtime point cell as the shared lawful affine point. -/
def pointAt (yst : EvmState) (ptr : U256) : G2Affine.Point :=
  if pointZeroValue yst ptr = 0 then
    .affine (Fp2.toLawful (fp2At yst ptr))
      (Fp2.toLawful (fp2At yst (ptr + 128)))
  else .infinity

@[simp] theorem pointAt_of_zero (yst : EvmState) (ptr : U256)
    (hzero : pointZeroValue yst ptr = 0) :
    pointAt yst ptr = .affine (Fp2.toLawful (fp2At yst ptr))
      (Fp2.toLawful (fp2At yst (ptr + 128))) := by
  simp [pointAt, hzero]

@[simp] theorem pointAt_of_infinity (yst : EvmState) (ptr : U256)
    (hinfinity : pointZeroValue yst ptr ≠ 0) :
    pointAt yst ptr = G2Affine.infinity := by
  rw [pointAt, if_neg]
  exact hinfinity

theorem pointAt_storeInfinity_3840 (yst : EvmState) :
    pointAt (msmStoreInfinityState yst 3840) 3840 = G2Affine.infinity := by
  apply pointAt_of_infinity
  simp only [pointZeroValue,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.pointZeroValue,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2ZeroValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpZeroValue,
    b2w]
  rw [show (msmStoreInfinityState yst 3840).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord yst.memory 3840 0) 3872 0)
                    3904 0)
                  3936 0)
                3968 0)
              4000 0)
            4032 0)
          4064 0 by
    simpa using msmStoreInfinityState_memory yst 3840]
  simp [loadWord_storeWord_same,
    loadWord_storeWord_disjoint]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
