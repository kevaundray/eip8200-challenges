import Challenge.EvmProof
import Challenge.EvmProof.CertifiedArtifact
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
import Checks.CertifiedArtifact
set_option warningAsError true
/-!
# Shared EVM proof checks

Each `#guard_msgs in #print axioms …` pins the exact axiom set of a theorem.
If a `sorry` (which appears as `sorryAx`), a `native_decide`
(`Lean.ofReduceBool`), or any new axiom slips in, elaboration fails.
-/

/-- info: 'Challenge.EvmProof.Bytecode.assemble_disassemble' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Bytecode.assemble_disassemble

/-- info: 'Challenge.EvmProof.Bytecode.JumpDestCertificate.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Bytecode.JumpDestCertificate.valid

/-- info: 'Challenge.EvmProof.CertifiedArtifact.rowsOfBytecode_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CertifiedArtifact.rowsOfBytecode_valid

/-- info: 'Challenge.EvmProof.CertifiedArtifact.fromBytecode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CertifiedArtifact.fromBytecode

/-- info: 'Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact.referenceRows_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact.referenceRows_valid

/-- info: 'Challenge.EvmProof.eval_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.eval_of_steps

/-- info: 'Challenge.EvmProof.Reaches.toEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Reaches.toEval

/-- info: 'Challenge.EvmProof.CertifiedArtifact.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CertifiedArtifact.run_sound

/-- info: 'Challenge.EvmProof.CertifiedArtifact.decoderCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CertifiedArtifact.decoderCertificate

/-- info: 'Challenge.EvmProof.CertifiedArtifact.runSelected_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CertifiedArtifact.runSelected_nil

/-- info: 'Challenge.EvmProof.CertifiedArtifact.runSelected_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CertifiedArtifact.runSelected_cons

/-- info: 'Challenge.EvmProof.CertifiedArtifact.runSelected_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CertifiedArtifact.runSelected_append

/-- info: 'Challenge.EvmProof.CertifiedArtifact.runSelected_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.CertifiedArtifact.runSelected_sound

/--
info: 'Challenge.EvmProof.CertifiedArtifact.runSelected_sound_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.EvmProof.CertifiedArtifact.runSelected_sound_exists

/-- info: 'Checks.CertifiedArtifact.tiny_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Checks.CertifiedArtifact.tiny_sound

/-- info: 'Checks.CertifiedArtifact.selected_tiny_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Checks.CertifiedArtifact.selected_tiny_sound

/-- info: 'Checks.CertifiedArtifact.selected_tiny_sound_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Checks.CertifiedArtifact.selected_tiny_sound_exists

/-- info: 'Checks.CertifiedArtifact.abstract_selected_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Checks.CertifiedArtifact.abstract_selected_sound
