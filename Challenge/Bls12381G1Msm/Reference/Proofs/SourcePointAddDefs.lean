import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointInfinityRefinement

set_option warningAsError true

/-! Frozen declaration and prefix boundary for the G1MSM `pointAdd` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def pointAddBody : Block Op :=
  match referenceBackendBlock[9]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointAddStmt0 : Stmt Op := pointAddBody[0]!
def pointAddStmt1 : Stmt Op := pointAddBody[1]!
def pointAddStmt2 : Stmt Op := pointAddBody[2]!
def pointAddStmt3 : Stmt Op := pointAddBody[3]!
def pointAddAfterPrefix : Block Op := pointAddBody.drop 3

def pointAddLeftInfinityCondition : Expr Op :=
  match pointAddStmt3 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

theorem pointAddLeftInfinityCondition_eq : pointAddLeftInfinityCondition =
    .call "\x0015" [.builtin .mload [.lit (.number 1568)]] := by
  rfl

theorem pointAddBody_length : pointAddBody.length = 27 := by
  rfl

theorem pointAddBody_eq : pointAddBody =
    [pointAddStmt0, pointAddStmt1, pointAddStmt2] ++ pointAddAfterPrefix := by
  rfl

theorem hoist_pointAddBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddBody = [] := by
  rfl

def pointAddBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: sourceFuns

def pointAddDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00107", "\x00108", "\x00109"]
    rets := []
    body := pointAddBody }

theorem lookup_pointAdd : lookupFun sourceFuns "\x0016" =
    some (pointAddDecl, sourceFuns) := by
  rfl

def pointAddInitialEnv (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00107", out), ("\x00108", left), ("\x00109", right)]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
