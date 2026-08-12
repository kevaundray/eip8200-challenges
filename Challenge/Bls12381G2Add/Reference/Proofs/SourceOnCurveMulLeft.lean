import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveMulInputs

set_option warningAsError true

/-! # Scheduled left input for frozen G2ADD Fp2 products -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

theorem fp2At_eq_of_loads (left right : EvmState) (ptr : U256)
    (h0 : loadWord left.memory ptr.toNat = loadWord right.memory ptr.toNat)
    (h1 : loadWord left.memory (ptr + BitVec.ofNat 256 32).toNat =
      loadWord right.memory (ptr + BitVec.ofNat 256 32).toNat)
    (h2 : loadWord left.memory (ptr + BitVec.ofNat 256 64).toNat =
      loadWord right.memory (ptr + BitVec.ofNat 256 64).toNat)
    (h3 : loadWord left.memory (ptr + BitVec.ofNat 256 96).toNat =
      loadWord right.memory (ptr + BitVec.ofNat 256 96).toNat) :
    fp2At left ptr = fp2At right ptr := by
  unfold fp2At
  rw [h0, h1, h2, h3]

theorem fp2MulScheduledLeft_eq_of_low (yst : EvmState)
    (out a b : U256)
    (ha : a.toNat + 96 < 2 ^ 256) (haLow : a.toNat + 128 ≤ 1024)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 32 < 2 ^ 256) :
    fp2At (fp2MulAfterRealStores yst out a b) a =
      fp2MulLeftInput yst a b := by
  rw [fp2MulLeftInput_eq_fp2At_of_low yst a b ha haLow]
  apply fp2At_eq_of_loads
  all_goals
    exact fp2MulAfterRealStores_loadWord_before_scratch yst out a b _
      (by bv_omega) houtHigh hout

theorem fp2MulFinalState_fp2At_before_scratch (yst : EvmState)
    (out a b ptr : U256)
    (hptrEnd : ptr.toNat + 96 < 2 ^ 256)
    (hptrLow : ptr.toNat + 128 ≤ 1024)
    (houtHigh : 1920 ≤ out.toNat) (hout : out.toNat + 96 < 2 ^ 256) :
    fp2At (fp2MulFinalState yst out a b) ptr = fp2At yst ptr := by
  apply fp2At_eq_of_loads
  all_goals
    exact fp2MulFinalState_loadWord_before_scratch yst out a b _
      (by bv_omega) houtHigh hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
