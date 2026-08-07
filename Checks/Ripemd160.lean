import Challenge.Ripemd160
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
set_option warningAsError true
/-! RIPEMD-160 axiom-footprint checks. -/

/-- info: 'Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact.referenceRows_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact.referenceRows_valid

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution

open EvmSemantics EvmSemantics.EVM

private abbrev LegacyPath := List
  (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka)

example : LegacyPath := path_start
example : LegacyPath := path_1b
example : LegacyPath := path_2e
example : LegacyPath := path_46
example : LegacyPath := path_5a
example : LegacyPath := path_73
example : LegacyPath := path_8e
example : LegacyPath := path_10f
example : LegacyPath := path_1b2
example : LegacyPath := path_1db
example : LegacyPath := path_231
example : LegacyPath := path_268
example : LegacyPath := path_3c1
example : LegacyPath := path_3ee

example (input : ByteArray) :
    Challenge.EvmProof.GasSteps
      (initialState referenceBytecode input 0) (atPC input 0x1b) :=
  gasSteps_start input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b) (atPC input 0x2e) :=
  gasSteps_1b input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x2e) (atPC input 0x46) :=
  gasSteps_2e input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x46) (atPC input 0x5a) :=
  gasSteps_46 input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x5a) (atPC input 0x73) :=
  gasSteps_5a input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x73) (atPC input 0x8e) :=
  gasSteps_73 input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x8e) (atPC input 0x10f) :=
  gasSteps_8e input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x10f) (atPC input 0x1b2) :=
  gasSteps_10f input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b2) (atPC input 0x1db) :=
  gasSteps_1b2 input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1db) (atPC input 0x231) :=
  gasSteps_1db input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x231) (atPC input 0x268) :=
  gasSteps_231 input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x268) (atPC input 0x3c1) :=
  gasSteps_268 input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3c1) (atPC input 0x3ee) :=
  gasSteps_3c1 input
example (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3ee) (mainStart input) :=
  gasSteps_3ee input

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution

/--
info: 'Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution.gasSteps_entry_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution.gasSteps_entry_cost

/--
info: 'Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correctWithSchedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correctWithSchedule

/--
info: 'Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct
