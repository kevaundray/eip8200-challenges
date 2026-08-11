import Challenge.Bls12381G1Add.ProofSupport.Yul
import Challenge.Bls12381G1Add.Reference.Bytecode
import Challenge.Bls12381G1Add.Reference.Proofs.FrozenBlock
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

/-!
# Frozen G1ADD source/compiler certificate

This module names the exact normalized and optimized Yul block whose verified
compiler output is the frozen 1674-byte runtime.  It is an ordinary checked
source/assembly equality; it does not use a certified-artifact builder.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op ExternalCreates)
open YulEvmCompiler
open Challenge.Bls12381G1Add.ProofSupport.Yul

def referenceParsedBlock : Block Op :=
  referenceBlock?.getD []

def referencePrunedBlock : Block Op :=
  YulParser.pruneLinkerBlock
    (YulParser.decodeValueStmts referenceParsedBlock)

def referenceRawBlock : Block Op :=
  referencePrunedBlock.map YulParser.desugarStmt

def referenceParsedCompiledBlock : Block Op :=
  @Optimizer.Normalize.normalize localDialect referenceRawBlock

/-- Exact normalized block accepted by the verified backend.  This is frozen
as ordinary Lean data so compilation can reduce in the kernel; the source
parser equivalence remains an executable regression check. -/
def referenceCompiledBlock : Block Op := frozenReferenceBlock

/-- Concrete evidence that the transparent source-to-assembly phase accepts
the frozen block. -/
theorem referenceCompileProgramSucceeded :
    (compileProgram referenceCompiledBlock).isSome := by
  set_option maxRecDepth 10000 in
    with_unfolding_all decide

/-- The exact labeled assembly produced by the transparent first phase. -/
def referenceAssembly : List Asm :=
  (compileProgram referenceCompiledBlock).get referenceCompileProgramSucceeded

theorem referenceCompiled_compileProgram :
    compileProgram referenceCompiledBlock = some referenceAssembly := by
  exact Option.eq_some_of_isSome referenceCompileProgramSucceeded

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
