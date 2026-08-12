import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointMemory
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubPreservation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulHighInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvPreservation

set_option warningAsError true

/-!
High-cell preservation needed by the fixed G2MSM layout.

G2ADD mostly consumes operands below its output, whereas G2MSM deliberately
keeps point cells above all arithmetic scratch.  These are the symmetric
after-output memory facts; they keep that layout choice out of arithmetic
refinement proofs.
-/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

theorem fp2AddFinalState_fp2At_after_out (yst : EvmState)
    (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hafter : out.toNat + 128 ≤ ptr.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2AddFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    unfold fp2AddFinalState
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddFinalState
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC1High
    change loadWord
      (storeWord (storeWord (fp2AddAfterC1Reads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat _)
        (out + BitVec.ofNat 256 96).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    have hreads : (fp2AddAfterC1Reads yst out a b).memory =
        (fp2AddAfterC0Stores yst out a b).memory := rfl
    rw [hreads]
    unfold fp2AddAfterC0Stores
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0Stores
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0High
    change loadWord (storeWord (storeWord yst.memory out.toNat _)
      (out + BitVec.ofNat 256 32).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]

theorem fp2SubFinalState_fp2At_after_out (yst : EvmState)
    (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hafter : out.toNat + 128 ≤ ptr.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2SubFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    unfold fp2SubFinalState
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC1High
    change loadWord
      (storeWord (storeWord (fp2SubAfterC1Reads yst out a b).memory
        (out + BitVec.ofNat 256 64).toNat _)
        (out + BitVec.ofNat 256 96).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    have hreads : (fp2SubAfterC1Reads yst out a b).memory =
        (fp2SubAfterC0Stores yst out a b).memory := rfl
    rw [hreads]
    unfold fp2SubAfterC0Stores
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0Stores
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0High
    change loadWord (storeWord (storeWord yst.memory out.toNat _)
      (out + BitVec.ofNat 256 32).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]

private theorem fp2MulAfterRealStores_loadWord_after_out
    (yst : EvmState) (out a b : U256) (offset : Nat)
    (hstart : 1664 ≤ offset) (hafter : out.toNat + 64 ≤ offset)
    (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2MulAfterRealStores yst out a b).memory offset =
      loadWord yst.memory offset := by
  have h32 : (out + BitVec.ofNat 256 32).toNat = out.toNat + 32 := by
    bv_omega
  unfold fp2MulAfterRealStores
  rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterRealStores,
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2MulAfterRealHigh]
  change loadWord
    (storeWord
      (storeWord (fp2MulAfterRealReads yst a b).memory out.toNat _)
      (out + BitVec.ofNat 256 32).toNat _) offset = _
  rw [h32,
    loadWord_storeWord_disjoint _ (out.toNat + 32) offset _
      (by left; omega),
    loadWord_storeWord_disjoint _ out.toNat offset _ (by left; omega)]
  exact fp2MulAfterV1Stores_loadWord_high_input yst a b offset hstart

theorem fp2MulFinalState_fp2At_after_out (yst : EvmState)
    (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1920 ≤ ptr.toNat)
    (hafter : out.toNat + 128 ≤ ptr.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2MulFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    rw [fp2MulFinalState, fp2MulAfterImagHigh]
    change loadWord
      (storeWord
        (storeWord (fp2MulAfterImagReads yst out a b).memory
          (out + BitVec.ofNat 256 64).toNat _)
        (out + BitVec.ofNat 256 96).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    have hreads : (fp2MulAfterImagReads yst out a b).memory =
        (fp2MulAfterVSumStores yst out a b).memory := rfl
    rw [hreads, fp2MulAfterVSumStores_loadWord_high _ _ _ _ _
      (by bv_omega)]
    exact fp2MulAfterRealStores_loadWord_after_out yst out a b _
      (by bv_omega) (by bv_omega) (by bv_omega)

private theorem fp2InvAfterRealStores_loadWord_after_out
    (yst : EvmState) (out a : U256) (offset : Nat)
    (hstart : 1728 ≤ offset) (hafter : out.toNat + 64 ≤ offset)
    (hout : out.toNat + 32 < 2 ^ 256) :
    loadWord (fp2InvAfterRealStores yst out a).memory offset =
      loadWord yst.memory offset := by
  unfold fp2InvAfterRealStores
  unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealStores
    Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealHigh
  change loadWord
    (storeWord
      (storeWord
        (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealCall
          yst a).memory out.toNat _)
      (out + BitVec.ofNat 256 32).toNat _) offset = _
  rw [loadWord_storeWord_disjoint _ _ offset _ (by left; bv_omega),
    loadWord_storeWord_disjoint _ _ offset _ (by left; bv_omega)]
  unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealCall
  rw [fpMulFinalState_loadWord_after_scratch (hstart := by omega)]
  rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterRealReads,
    fp2AddReadState_memory]
  exact fp2InvAfterScalarStores_loadWord_high yst a offset hstart

theorem fp2InvFinalState_fp2At_after_out (yst : EvmState)
    (out a ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrHigh : 1728 ≤ ptr.toNat)
    (hafter : out.toNat + 128 ≤ ptr.toNat)
    (houtEnd : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2InvFinalState yst out a) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    unfold fp2InvFinalState
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvFinalState
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagHigh
    change loadWord
      (storeWord
        (storeWord
          (Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagCall
            yst out a).memory (out + BitVec.ofNat 256 64).toNat _)
        (out + BitVec.ofNat 256 96).toNat _) _ = _
    rw [loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega),
      loadWord_storeWord_disjoint _ _ _ _ (by left; bv_omega)]
    unfold Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagCall
    rw [fpMulFinalState_loadWord_after_scratch (hstart := by bv_omega)]
    rw [Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterImagReads,
      Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2InvAfterNegReads]
    change loadWord (fp2InvAfterRealStores yst out a).memory _ = _
    exact fp2InvAfterRealStores_loadWord_after_out yst out a _
      (by bv_omega) (by bv_omega) (by bv_omega)

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
