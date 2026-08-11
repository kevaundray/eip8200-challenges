import Challenge.EvmProof.ProfiledCorrectness

set_option warningAsError true

/-- info: 'Challenge.EvmProof.profiled_compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.profiled_compile_correct

/-- info: 'Challenge.EvmProof.profiled_compiledAssembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.profiled_compiledAssembly_correct
