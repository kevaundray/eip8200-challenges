import Challenge.EvmProof.ModexpExec

set_option warningAsError true

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

example {op args st result}
    (h : Challenge.EvmProof.modexpBuiltinFn op args st = some result) :
    (evmWithExternal Challenge.EvmProof.successfulModexpCalls
      ExternalCreates.none).Builtin op args st result :=
  Challenge.EvmProof.modexpBuiltinFn_sound h

/-- info: 'Challenge.EvmProof.modexpBuiltinFn_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.modexpBuiltinFn_sound
