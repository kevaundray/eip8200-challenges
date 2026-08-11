import Challenge.EvmProof
import Checks.EvmProofByteWindow
import Checks.EvmProofCallMemory
import Checks.EvmProofModexpCallGas
import Checks.EvmProofModexpCalls
import Checks.EvmProofProfiledCorrectness
import Checks.EvmProofProfiledCalls
import Checks.EvmProofProfiledLower
import Checks.EvmProofProfiledSteps
import Checks.EvmProofWideMul
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

/-- info: 'Challenge.EvmProof.eval_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.eval_of_steps

/-- info: 'Challenge.EvmProof.Reaches.toEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Reaches.toEval

/-- info: 'Challenge.EvmProof.Limbs.join_splitTwo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Limbs.join_splitTwo

/-- info: 'Challenge.EvmProof.MemoryRegion.disjoint_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms Challenge.EvmProof.MemoryRegion.disjoint_symm
