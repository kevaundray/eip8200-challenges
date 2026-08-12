import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainValidationExec
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveExec

set_option warningAsError true

/-! # Frozen G2ADD point-scope syntax and state graph -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainPointStmt0 : Stmt Op := mainPointScopeBody[0]!
def mainPointStmt1 : Stmt Op := mainPointScopeBody[1]!
def mainPointStmt2 : Stmt Op := mainPointScopeBody[2]!
def mainPointStmt3 : Stmt Op := mainPointScopeBody[3]!
def mainPointStmt4 : Stmt Op := mainPointScopeBody[4]!
def mainPointStmt5 : Stmt Op := mainPointScopeBody[5]!
def mainPointStmt6 : Stmt Op := mainPointScopeBody[6]!

theorem mainPointScopeBody_eq : mainPointScopeBody =
    [mainPointStmt0, mainPointStmt1, mainPointStmt2, mainPointStmt3,
      mainPointStmt4, mainPointStmt5, mainPointStmt6] := by rfl

def mainInf1 (yst : EvmState) : U256 :=
  pointZeroValue (mainAfterValidationReads yst) 0

def mainAfterInf1Reads (yst : EvmState) : EvmState :=
  pointZeroReadState (mainAfterValidationReads yst) 0

def mainInf2 (yst : EvmState) : U256 :=
  pointZeroValue (mainAfterInf1Reads yst) 256

def mainAfterInf2Reads (yst : EvmState) : EvmState :=
  pointZeroReadState (mainAfterInf1Reads yst) 256

def mainPointEnv (yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00132", mainInf2 yst), ("\x00131", mainInf1 yst)]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
