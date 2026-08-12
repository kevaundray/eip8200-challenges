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
def pointAddStmt4 : Stmt Op := pointAddBody[4]!
def pointAddAfterPrefix : Block Op := pointAddBody.drop 3

def pointAddLeftInfinityCondition : Expr Op :=
  match pointAddStmt3 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddLeftInfinityBody : Block Op :=
  match pointAddStmt3 with
  | .cond _ body => body
  | _ => []

def pointAddLeftCopyStmt : Stmt Op := pointAddLeftInfinityBody[0]!

def pointAddLeftCopyBody : Block Op :=
  match pointAddLeftCopyStmt with
  | .block body => body
  | _ => []

def pointAddLeftCopyStmt0 : Stmt Op := pointAddLeftCopyBody[0]!
def pointAddLeftCopyStmt1 : Stmt Op := pointAddLeftCopyBody[1]!
def pointAddLeftCopyStmt2 : Stmt Op := pointAddLeftCopyBody[2]!
def pointAddLeftCopyStmt3 : Stmt Op := pointAddLeftCopyBody[3]!
def pointAddLeftCopyStmt4 : Stmt Op := pointAddLeftCopyBody[4]!
def pointAddLeftCopyStmt5 : Stmt Op := pointAddLeftCopyBody[5]!
def pointAddLeftCopyStmt6 : Stmt Op := pointAddLeftCopyBody[6]!

theorem pointAddLeftInfinityCondition_eq : pointAddLeftInfinityCondition =
    .call "\x0015" [.builtin .mload [.lit (.number 1568)]] := by
  rfl

theorem pointAddStmt3_eq : pointAddStmt3 =
    .cond pointAddLeftInfinityCondition pointAddLeftInfinityBody := by
  rfl

def pointAddRightInfinityCondition : Expr Op :=
  match pointAddStmt4 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddRightInfinityBody : Block Op :=
  match pointAddStmt4 with
  | .cond _ body => body
  | _ => []

theorem pointAddRightInfinityCondition_eq : pointAddRightInfinityCondition =
    .call "\x0015" [.builtin .mload [.lit (.number 1600)]] := by
  rfl

theorem pointAddStmt4_eq : pointAddStmt4 =
    .cond pointAddRightInfinityCondition pointAddRightInfinityBody := by
  rfl

theorem pointAddLeftInfinityBody_eq : pointAddLeftInfinityBody =
    [pointAddLeftCopyStmt, .leave] := by
  rfl

theorem pointAddLeftCopyStmt_eq : pointAddLeftCopyStmt =
    .block pointAddLeftCopyBody := by
  rfl

theorem pointAddLeftCopyBody_eq : pointAddLeftCopyBody =
    [pointAddLeftCopyStmt0, pointAddLeftCopyStmt1, pointAddLeftCopyStmt2,
      pointAddLeftCopyStmt3, pointAddLeftCopyStmt4, pointAddLeftCopyStmt5,
      pointAddLeftCopyStmt6] := by
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
