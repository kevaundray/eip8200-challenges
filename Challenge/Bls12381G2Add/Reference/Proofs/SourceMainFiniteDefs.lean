import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPointScope

set_option warningAsError true

/-! # Frozen G2ADD finite-path syntax and initial state graph -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFiniteStmt0 : Stmt Op := Compilation.referenceCompiledBlock[44]!
def mainFiniteStmt1 : Stmt Op := Compilation.referenceCompiledBlock[45]!
def mainFiniteStmt2 : Stmt Op := Compilation.referenceCompiledBlock[46]!
def mainFiniteStmt3 : Stmt Op := Compilation.referenceCompiledBlock[47]!
def mainFiniteStmt4 : Stmt Op := Compilation.referenceCompiledBlock[48]!
def mainFiniteStmt5 : Stmt Op := Compilation.referenceCompiledBlock[49]!
def mainFiniteStmt6 : Stmt Op := Compilation.referenceCompiledBlock[50]!
def mainFiniteStmt7 : Stmt Op := Compilation.referenceCompiledBlock[51]!
def mainFiniteStmt8 : Stmt Op := Compilation.referenceCompiledBlock[52]!
def mainFiniteStmt9 : Stmt Op := Compilation.referenceCompiledBlock[53]!

def mainFiniteBody : Block Op := (Compilation.referenceCompiledBlock).drop 44

theorem mainFiniteBody_eq : mainFiniteBody =
    [mainFiniteStmt0, mainFiniteStmt1, mainFiniteStmt2, mainFiniteStmt3,
      mainFiniteStmt4, mainFiniteStmt5, mainFiniteStmt6, mainFiniteStmt7,
      mainFiniteStmt8, mainFiniteStmt9] := by rfl

def mainFiniteXEq1 (yst : EvmState) : U256 :=
  fp2EqValue (mainValidatedState yst) 0 256

def mainAfterFiniteXEq1 (yst : EvmState) : EvmState :=
  fp2EqReadState (mainValidatedState yst) 0 256

def mainFiniteXEq2 (yst : EvmState) : U256 :=
  fp2EqValue (mainAfterFiniteXEq1 yst) 0 256

def mainAfterFiniteXEq2 (yst : EvmState) : EvmState :=
  fp2EqReadState (mainAfterFiniteXEq1 yst) 0 256

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
