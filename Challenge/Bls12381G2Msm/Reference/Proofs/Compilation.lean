import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlock
import Challenge.Bls12381G2Msm.Reference.Bytecode
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

/-! Compiler front-end over the already frozen normalized G2MSM block. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

def referenceCompiledBlock : Block Op := frozenReferenceBlock

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem referenceCompileProgramSucceeded :
    (YulEvmCompiler.compileProgram referenceCompiledBlock).isSome := by
  with_unfolding_all decide

def referenceAssembly : List YulEvmCompiler.Asm :=
  (YulEvmCompiler.compileProgram referenceCompiledBlock).get
    referenceCompileProgramSucceeded

theorem referenceCompiled_compileProgram :
    YulEvmCompiler.compileProgram referenceCompiledBlock =
      some referenceAssembly := by
  exact Option.eq_some_of_isSome referenceCompileProgramSucceeded

def referenceComputedOptimizedAssembly : List YulEvmCompiler.Asm :=
  YulEvmCompiler.optimizeAsm referenceAssembly

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
