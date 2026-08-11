import Challenge.EvmProof.CallMemory
set_option warningAsError true
/-!
# External-call return-memory checks
-/

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

example {ymem : Nat → UInt8} {memory output : ByteArray}
    (h : MemMatch ymem memory) (dst size : Nat) :
    MemMatch (YulSemantics.EVM.copyReturn ymem dst size output.toList)
      (State.writeReturn memory output dst size) :=
  Challenge.EvmProof.MemMatch.copyReturn h dst size output

example (output : ByteArray) :
    MemMatch (YulSemantics.EVM.byteFrom output.toList) output :=
  Challenge.EvmProof.MemMatch.byteFrom_toList output

/-- info: 'Challenge.EvmProof.MemMatch.copyReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.MemMatch.copyReturn

/-- info: 'Challenge.EvmProof.MemMatch.byteFrom_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.MemMatch.byteFrom_toList
