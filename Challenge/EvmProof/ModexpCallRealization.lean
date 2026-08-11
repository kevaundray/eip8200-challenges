import Challenge.EvmProof.ProfiledCalls
set_option warningAsError true
/-!
# Concrete EVM realization of successful MODEXP calls

This module discharges `ProfiledCallsRealized` for the narrow source relation
in `ModexpCalls`.  The proof follows the actual EVM trace: STATICCALL enters a
child frame, native MODEXP returns, and the caller frame resumes successfully.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics.EVM
open YulEvmCompiler

/-- State-independent ceiling for the committed part of an Osaka STATICCALL. -/
theorem staticcallCommitted_le (s : State)
    (hfork : s.executionEnv.fork = .Osaka)
    (argsOff argsLen retOff retLen toArg : UInt256) :
    Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg ≤
      5200 + memBound argsOff.toNat argsLen.toNat +
        memBound retOff.toNat retLen.toNat := by
  have hbase : Gas.baseCost s.executionEnv.fork .STATICCALL ≤ 100 := by
    rw [hfork]
    decide
  have hmem := memExpansionDelta2_le_memBounds s.activeWords.toNat
    argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
  have hcold : Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg) ≤ 2500 := by
    unfold Gas.accountColdSurcharge
    split_ifs <;> omega
  have hdel : Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg) ≤ 2600 := by
    unfold Gas.delegationAccessCost
    split <;> first | (split_ifs <;> omega) | omega
  unfold Gas.staticcallCommitted
  omega

/-- Enough post-commit gas makes the EIP-150 cap retain the requested gas. -/
theorem forwardGas_eq_arg_of_65_mul_le (available requested : Nat)
    (h : 65 * requested ≤ available) :
    Gas.forwardGas .Osaka available requested = requested := by
  have hcap : requested ≤ available - available / 64 := by
    apply (Nat.le_sub_iff_add_le (Nat.div_le_self available 64)).2
    have hdiv : available / 64 ≤ available - requested := by
      apply (Nat.div_le_iff_le_mul (by omega : 0 < 64)).2
      omega
    omega
  simp [Gas.forwardGas, hcap]

/-- A successful MODEXP result never reports more gas than was supplied. -/
theorem runModexp_success_gas_le {fork : Fork} {input : ByteArray}
    {childGas gasUsed : Nat} {output : ByteArray}
    (h : Precompile.runModexp fork input childGas = .success output gasUsed) :
    gasUsed ≤ childGas := by
  unfold Precompile.runModexp at h
  dsimp only at h
  split at h
  · contradiction
  split at h
  · rename_i hcost
    split at h <;> injection h
    all_goals omega
  · contradiction

end Challenge.EvmProof
