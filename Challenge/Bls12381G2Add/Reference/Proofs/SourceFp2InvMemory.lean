import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvRefinement
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true
/-! # Memory refinement for frozen G2ADD `fp2Inv` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem fp2InvAfterSquare0Stores_square0 (yst : EvmState) (a : U256) :
    fpWords (loadWord (fp2InvAfterSquare0Stores yst a).memory 1536)
        (loadWord (fp2InvAfterSquare0Stores yst a).memory 1568) =
      pairWords (fp2InvSquare0 yst a) := by
  rw [fp2InvAfterSquare0Stores, fp2InvAfterSquare0High]
  change fpWords
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare0Call yst a).memory 1536
        (fp2InvSquare0 yst a).1) 1568 (fp2InvSquare0 yst a).2) 1536)
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare0Call yst a).memory 1536
        (fp2InvSquare0 yst a).1) 1568 (fp2InvSquare0 yst a).2) 1568) = _
  rw [loadWord_storeWord_disjoint _ 1568 1536 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2InvAfterSquare1Stores_square0 (yst : EvmState) (a : U256) :
    fpWords (loadWord (fp2InvAfterSquare1Stores yst a).memory 1536)
        (loadWord (fp2InvAfterSquare1Stores yst a).memory 1568) =
      pairWords (fp2InvSquare0 yst a) := by
  rw [fp2InvAfterSquare1Stores, fp2InvAfterSquare1High]
  change fpWords
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare1Call yst a).memory 1600
        (fp2InvSquare1 yst a).1) 1632 (fp2InvSquare1 yst a).2) 1536)
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare1Call yst a).memory 1600
        (fp2InvSquare1 yst a).1) 1632 (fp2InvSquare1 yst a).2) 1568) = _
  rw [loadWord_storeWord_disjoint _ 1632 1536 _ (by omega),
    loadWord_storeWord_disjoint _ 1600 1536 _ (by omega),
    loadWord_storeWord_disjoint _ 1632 1568 _ (by omega),
    loadWord_storeWord_disjoint _ 1600 1568 _ (by omega)]
  unfold fp2InvAfterSquare1Call
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega),
    fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  change fpWords
    (loadWord (fp2InvAfterSquare0Stores yst a).memory 1536)
    (loadWord (fp2InvAfterSquare0Stores yst a).memory 1568) = _
  exact fp2InvAfterSquare0Stores_square0 yst a

theorem fp2InvAfterSquare1Stores_square1 (yst : EvmState) (a : U256) :
    fpWords (loadWord (fp2InvAfterSquare1Stores yst a).memory 1600)
        (loadWord (fp2InvAfterSquare1Stores yst a).memory 1632) =
      pairWords (fp2InvSquare1 yst a) := by
  rw [fp2InvAfterSquare1Stores, fp2InvAfterSquare1High]
  change fpWords
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare1Call yst a).memory 1600
        (fp2InvSquare1 yst a).1) 1632 (fp2InvSquare1 yst a).2) 1600)
    (loadWord (storeWord
      (storeWord (fp2InvAfterSquare1Call yst a).memory 1600
        (fp2InvSquare1 yst a).1) 1632 (fp2InvSquare1 yst a).2) 1632) = _
  rw [loadWord_storeWord_disjoint _ 1632 1600 _ (by omega),
    loadWord_storeWord_same, loadWord_storeWord_same]
  rfl

theorem fp2InvNorm_eq_squares (yst : EvmState) (a : U256) :
    pairWords (fp2InvNorm yst a) =
      Fp.addSource (pairWords (fp2InvSquare0 yst a))
        (pairWords (fp2InvSquare1 yst a)) := by
  rw [fp2InvNorm_eq_addSource, fp2InvAfterSquare1Stores_square0,
    fp2InvAfterSquare1Stores_square1]

theorem fp2InvNorm_canonical (yst : EvmState) (a : U256)
    (h0 : Fp.Canonical (pairWords (fp2InvSquare0 yst a)))
    (h1 : Fp.Canonical (pairWords (fp2InvSquare1 yst a))) :
    Fp.Canonical (pairWords (fp2InvNorm yst a)) := by
  rw [fp2InvNorm_eq_squares]
  exact Fp.canonical_addSource h0 h1

theorem fp2InvNorm_hi_lt (yst : EvmState) (a : U256)
    (h0 : Fp.Canonical (pairWords (fp2InvSquare0 yst a)))
    (h1 : Fp.Canonical (pairWords (fp2InvSquare1 yst a))) :
    (fp2InvNorm yst a).1.toNat < 2 ^ 128 :=
  (fp2InvNorm_canonical yst a h0 h1).1

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
