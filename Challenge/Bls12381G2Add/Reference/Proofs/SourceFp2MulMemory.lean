import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulRefinement
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true

/-! # Memory refinement for frozen G2ADD `fp2Mul`

This module proves the scratch read-back facts separately from arithmetic.
That separation is deliberate: expanding both the MODEXP state graph and the
Fp2 source schedule in one theorem causes avoidable elaborator memory growth.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2MulAfterV0Stores_load1536 (yst : EvmState) (a b : U256) :
    loadWord (fp2MulAfterV0Stores yst a b).memory 1536 =
      (fp2MulV0 yst a b).1 := by
  rw [fp2MulAfterV0Stores, fp2MulAfterV0High]
  change loadWord
      (storeWord
        (storeWord (fp2MulAfterV0Call yst a b).memory 1536
          (fp2MulV0 yst a b).1)
        1568 (fp2MulV0 yst a b).2) 1536 = _
  rw [loadWord_storeWord_disjoint _ 1568 1536 _ (by omega)]
  rw [loadWord_storeWord_same]

theorem fp2MulAfterV0Stores_load1568 (yst : EvmState) (a b : U256) :
    loadWord (fp2MulAfterV0Stores yst a b).memory 1568 =
      (fp2MulV0 yst a b).2 := by
  rw [fp2MulAfterV0Stores]
  change loadWord
      (storeWord (fp2MulAfterV0High yst a b).memory 1568
        (fp2MulV0 yst a b).2) 1568 = _
  exact loadWord_storeWord_same _ _ _

theorem fp2MulAfterV0Stores_v0 (yst : EvmState) (a b : U256) :
    fpWords (loadWord (fp2MulAfterV0Stores yst a b).memory 1536)
        (loadWord (fp2MulAfterV0Stores yst a b).memory 1568) =
      pairWords (fp2MulV0 yst a b) := by
  rw [fp2MulAfterV0Stores_load1536, fp2MulAfterV0Stores_load1568]
  rfl

theorem fp2MulAfterV1Call_load1536 (yst : EvmState) (a b : U256) :
    loadWord (fp2MulAfterV1Call yst a b).memory 1536 =
      loadWord (fp2MulAfterV0Stores yst a b).memory 1536 := by
  unfold fp2MulAfterV1Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rfl

theorem fp2MulAfterV1Call_load1568 (yst : EvmState) (a b : U256) :
    loadWord (fp2MulAfterV1Call yst a b).memory 1568 =
      loadWord (fp2MulAfterV0Stores yst a b).memory 1568 := by
  unfold fp2MulAfterV1Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rfl

theorem fp2MulAfterV1Stores_v0 (yst : EvmState) (a b : U256) :
    fpWords (loadWord (fp2MulAfterV1Stores yst a b).memory 1536)
        (loadWord (fp2MulAfterV1Stores yst a b).memory 1568) =
      pairWords (fp2MulV0 yst a b) := by
  rw [fp2MulAfterV1Stores, fp2MulAfterV1High]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterV1Call yst a b).memory 1600
          (fp2MulV1 yst a b).1)
        1632 (fp2MulV1 yst a b).2) 1536)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterV1Call yst a b).memory 1600
          (fp2MulV1 yst a b).1)
        1632 (fp2MulV1 yst a b).2) 1568) = _
  rw [loadWord_storeWord_disjoint _ 1632 1536 _ (by omega),
    loadWord_storeWord_disjoint _ 1600 1536 _ (by omega),
    loadWord_storeWord_disjoint _ 1632 1568 _ (by omega),
    loadWord_storeWord_disjoint _ 1600 1568 _ (by omega),
    fp2MulAfterV1Call_load1536, fp2MulAfterV1Call_load1568,
    fp2MulAfterV0Stores_load1536, fp2MulAfterV0Stores_load1568]
  rfl

theorem fp2MulAfterV1Stores_v1 (yst : EvmState) (a b : U256) :
    fpWords (loadWord (fp2MulAfterV1Stores yst a b).memory 1600)
        (loadWord (fp2MulAfterV1Stores yst a b).memory 1632) =
      pairWords (fp2MulV1 yst a b) := by
  rw [fp2MulAfterV1Stores, fp2MulAfterV1High]
  change fpWords
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterV1Call yst a b).memory 1600
          (fp2MulV1 yst a b).1)
        1632 (fp2MulV1 yst a b).2) 1600)
    (loadWord
      (storeWord
        (storeWord (fp2MulAfterV1Call yst a b).memory 1600
          (fp2MulV1 yst a b).1)
        1632 (fp2MulV1 yst a b).2) 1632) = _
  rw [loadWord_storeWord_disjoint _ 1632 1600 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
