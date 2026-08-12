import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulLawful
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true

/-! # Low-input locality used by frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fpMulFinalState_loadWord_before_scratch (yst : EvmState)
    (ahi alo bhi blo : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (fpMulFinalState yst ahi alo bhi blo).memory offset =
      loadWord yst.memory offset :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulFinalState_loadWord_before_scratch
    yst ahi alo bhi blo offset hend

theorem fp2MulAfterV0Stores_loadWord_before_scratch
    (yst : EvmState) (a b : U256) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (fp2MulAfterV0Stores yst a b).memory offset =
      loadWord yst.memory offset := by
  rw [fp2MulAfterV0Stores, fp2MulAfterV0High]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterV0Call yst a b).memory 1536
        (fp2MulV0 yst a b).1)
      1568 (fp2MulV0 yst a b).2) offset = _
  rw [loadWord_storeWord_disjoint _ 1568 offset _ (by omega),
    loadWord_storeWord_disjoint _ 1536 offset _ (by omega)]
  unfold fp2MulAfterV0Call
  rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ offset hend]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
