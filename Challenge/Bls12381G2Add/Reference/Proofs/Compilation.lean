import Challenge.Bls12381G2Add.ProofSupport.YulDialect
import Challenge.Bls12381G2Add.Reference.Bytecode
import Challenge.Bls12381G2Add.Reference.Proofs.FrozenBlock
import Challenge.Bls12381G2Add.Reference.Proofs.FrozenAssembly
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

/-!
# G2ADD source/compiler boundary

The parsed/normalized definitions remain executable regressions. A subsequent
module freezes the normalized block and optimized assembly as ordinary Lean
data, so source and EVM proofs do not repeatedly unfold the parser or compiler.
-/

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

def referenceParsedBlock : Block Op :=
  Challenge.Bls12381G2Add.referenceBlock?.getD []

def referencePrunedBlock : Block Op :=
  YulParser.pruneLinkerBlock
    (YulParser.decodeValueStmts referenceParsedBlock)

def referenceRawBlock : Block Op :=
  referencePrunedBlock.map YulParser.desugarStmt

def referenceParsedCompiledBlock : Block Op :=
  @YulEvmCompiler.Optimizer.Normalize.normalize
    Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect referenceRawBlock

/-- Exact normalized block accepted by the verified direct compiler. -/
def referenceCompiledBlock : Block Op := frozenReferenceBlock

theorem referenceCompileProgramSucceeded :
    (YulEvmCompiler.compileProgram referenceCompiledBlock).isSome := by
  set_option maxRecDepth 20000 in
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

def referenceOptimizedAssembly : List YulEvmCompiler.Asm :=
  frozenReferenceAssembly

theorem referenceComputedOptimizedAssembly_eq :
    referenceComputedOptimizedAssembly = referenceOptimizedAssembly := by
  set_option maxRecDepth 30000 in
    with_unfolding_all decide

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation
