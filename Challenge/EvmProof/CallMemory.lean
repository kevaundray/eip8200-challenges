import YulEvmCompiler.StateRel
set_option warningAsError true
/-!
# External-call return memory

The source and target call semantics use different memory representations.
This module proves their shared caller-local return-copy operation once, so
profiled precompile realizations do not duplicate byte-level reasoning.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

namespace MemMatch

/-- A byte array matches the total zero-padded view of its own byte list. -/
theorem byteFrom_toList (output : ByteArray) :
    YulEvmCompiler.MemMatch
      (YulSemantics.EVM.byteFrom output.toList) output := by
  intro address
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, ByteArray.toList_eq_data,
    Array.getElem?_toList, getElem?_def]
  split
  · rename_i haddress
    rw [Option.getD_some]
    rw [dif_pos (show address < output.size from haddress)]
    rw [ByteArray.getElem_eq_getElem_data]
    rfl
  · rename_i haddress
    rw [Option.getD_none]
    rw [dif_neg (show ¬address < output.size from haddress)]

/-- Source `copyReturn` agrees with target `State.writeReturn`, including the
empty-copy case that deliberately avoids extending target memory. -/
theorem copyReturn {ymem : Nat → UInt8} {memory : ByteArray}
    (h : YulEvmCompiler.MemMatch ymem memory) (dst size : Nat)
    (output : ByteArray) :
    YulEvmCompiler.MemMatch
      (YulSemantics.EVM.copyReturn ymem dst size output.toList)
      (State.writeReturn memory output dst size) := by
  have hlen : output.toList.length = output.size := by
    rw [ByteArray.toList_eq_data, Array.length_toList]
    rfl
  unfold State.writeReturn
  dsimp only
  split
  · rename_i hzero
    have hmin : min output.size size = 0 := by
      simpa [ByteArray.size_extract, Nat.min_comm] using hzero
    intro address
    simp only [YulSemantics.EVM.copyReturn, hlen]
    rw [if_neg (by omega)]
    exact h address
  · rename_i hnonzero
    intro address
    rw [← YulEvmCompiler.getD_eq_dite,
      MachineState.writeBytes_getElem?_getD, ByteArray.size_extract]
    simp only [Nat.sub_zero, YulSemantics.EVM.copyReturn, hlen,
      Nat.min_assoc, Nat.min_left_comm, Nat.min_self]
    by_cases hwindow : dst ≤ address ∧
        address < dst + min size output.size
    · rw [if_pos hwindow, if_pos (by simpa [Nat.min_comm] using hwindow)]
      unfold YulSemantics.EVM.byteFrom
      rw [ByteArray.toList_eq_data, List.getD_eq_getElem?_getD,
        Array.getElem?_toList]
      have hi : address - dst < output.size := by omega
      have hicopy : address - dst <
          (output.extract 0 (min output.size size)).size := by
        rw [ByteArray.size_extract]
        omega
      rw [Array.getElem?_eq_getElem hi]
      rw [getElem?_def, dif_pos hicopy, Option.getD_some]
      rw [ByteArray.getElem_extract]
      simp only [Option.getD_some, Nat.zero_add]
      rw [ByteArray.getElem_eq_getElem_data]
    · rw [if_neg hwindow, if_neg (by simpa [Nat.min_comm] using hwindow),
        YulEvmCompiler.getD_eq_dite]
      exact h address

end MemMatch
end Challenge.EvmProof
