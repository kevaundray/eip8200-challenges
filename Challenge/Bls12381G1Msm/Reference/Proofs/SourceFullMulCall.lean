import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulBody

set_option warningAsError true

/-! Relational call semantics of the frozen G1MSM `fullMul` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fullMulRuntimeValue (ahi alo bhi blo : U256) : FullMulValue :=
  let middle := fullMulMiddleValue (fullWordValue alo blo).hi
    (fullWordValue ahi blo).lo (fullWordValue alo bhi).lo
  { r2 := fullMulHighValue ahi alo bhi blo
    r1 := middle.word
    r0 := (fullWordValue alo blo).lo }

theorem fullMulRuntimeValue_eq (ahi alo bhi blo : U256) :
    fullMulRuntimeValue ahi alo bhi blo = fullMulValue ahi alo bhi blo := by
  rw [
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.FullMulValue.mk.injEq]
  constructor
  · exact fullMulHighValue_eq ahi alo bhi blo
  · constructor <;> rfl

private theorem step_fullMulRuntime (ahi alo bhi blo : U256) (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x006" [.var "ahi", .var "alo", .var "bhi", .var "blo"])
      (.vals [(fullMulRuntimeValue ahi alo bhi blo).r2,
        (fullMulRuntimeValue ahi alo bhi blo).r1,
        (fullMulRuntimeValue ahi alo bhi blo).r0] yst) := by
  let outer : VEnv Challenge.EvmProof.modexpExec.toDialect :=
    [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)]
  have hhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns outer yst
      (.var "ahi") (.vals [ahi] yst) := Step.var rfl
  have halo : EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns outer yst
      (.var "alo") (.vals [alo] yst) := Step.var rfl
  have hbhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns outer yst
      (.var "bhi") (.vals [bhi] yst) := Step.var rfl
  have hblo : EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns outer yst
      (.var "blo") (.vals [blo] yst) := Step.var rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect sourceFuns outer yst
      [.var "ahi", .var "alo", .var "bhi", .var "blo"]
      (.vals [ahi, alo, bhi, blo] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      hblo) hbhi) halo) hhi
  have hcall := Step.callOk hargs lookup_fullMul rfl
    (step_fullMulBody ahi alo bhi blo yst) (Or.inl rfl)
  simpa [outer, fullMulDecl, fullMulBodyResultEnv, fullMulInitialEnv,
    fullMulFinalEnv, fullMulRuntimeValue, restore, VEnv.get,
    Dialect.zero, litValue] using hcall

theorem step_fullMul (ahi alo bhi blo : U256) (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("ahi", ahi), ("alo", alo), ("bhi", bhi), ("blo", blo)] yst
      (.call "\x006" [.var "ahi", .var "alo", .var "bhi", .var "blo"])
      (.vals [(fullMulValue ahi alo bhi blo).r2,
        (fullMulValue ahi alo bhi blo).r1,
        (fullMulValue ahi alo bhi blo).r0] yst) := by
  rw [← fullMulRuntimeValue_eq ahi alo bhi blo]
  exact step_fullMulRuntime ahi alo bhi blo yst

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
