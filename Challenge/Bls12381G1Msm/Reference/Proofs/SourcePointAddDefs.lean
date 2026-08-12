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
def pointAddStmt5 : Stmt Op := pointAddBody[5]!
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

def pointAddRightCopyStmt : Stmt Op := pointAddRightInfinityBody[0]!

def pointAddRightCopyBody : Block Op :=
  match pointAddRightCopyStmt with
  | .block body => body
  | _ => []

def pointAddRightCopyStmt0 : Stmt Op := pointAddRightCopyBody[0]!
def pointAddRightCopyStmt1 : Stmt Op := pointAddRightCopyBody[1]!
def pointAddRightCopyStmt2 : Stmt Op := pointAddRightCopyBody[2]!
def pointAddRightCopyStmt3 : Stmt Op := pointAddRightCopyBody[3]!
def pointAddRightCopyStmt4 : Stmt Op := pointAddRightCopyBody[4]!
def pointAddRightCopyStmt5 : Stmt Op := pointAddRightCopyBody[5]!
def pointAddRightCopyStmt6 : Stmt Op := pointAddRightCopyBody[6]!

theorem pointAddRightInfinityCondition_eq : pointAddRightInfinityCondition =
    .call "\x0015" [.builtin .mload [.lit (.number 1600)]] := by
  rfl

theorem pointAddStmt4_eq : pointAddStmt4 =
    .cond pointAddRightInfinityCondition pointAddRightInfinityBody := by
  rfl

theorem pointAddRightInfinityBody_eq : pointAddRightInfinityBody =
    [pointAddRightCopyStmt, .leave] := by
  rfl

theorem pointAddRightCopyStmt_eq : pointAddRightCopyStmt =
    .block pointAddRightCopyBody := by
  rfl

theorem pointAddRightCopyBody_eq : pointAddRightCopyBody =
    [pointAddRightCopyStmt0, pointAddRightCopyStmt1, pointAddRightCopyStmt2,
      pointAddRightCopyStmt3, pointAddRightCopyStmt4, pointAddRightCopyStmt5,
      pointAddRightCopyStmt6] := by
  rfl

def pointAddXEqCondition : Expr Op :=
  match pointAddStmt5 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddXEqBody : Block Op :=
  match pointAddStmt5 with
  | .cond _ body => body
  | _ => []

theorem pointAddStmt5_eq : pointAddStmt5 =
    .cond pointAddXEqCondition pointAddXEqBody := by
  rfl

theorem pointAddXEqCondition_eq : pointAddXEqCondition =
    .call "\x003"
      [.builtin .mload [.builtin .mload [.lit (.number 1568)]],
       .builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]],
       .builtin .mload [.builtin .mload [.lit (.number 1600)]],
       .builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]]] := by
  rfl

def pointAddXEqMainStmt : Stmt Op := pointAddXEqBody[0]!

def pointAddXEqMainBody : Block Op :=
  match pointAddXEqMainStmt with
  | .block body => body
  | _ => []

def pointAddXEqExceptionalStmt : Stmt Op := pointAddXEqMainBody[0]!

def pointAddXEqExceptionalBody : Block Op :=
  match pointAddXEqExceptionalStmt with
  | .block body => body
  | _ => []

def pointAddYSumStmt : Stmt Op := pointAddXEqExceptionalBody[0]!
def pointAddYZeroStmt : Stmt Op := pointAddXEqExceptionalBody[1]!
def pointAddDoubleXSqStmt : Stmt Op := pointAddXEqMainBody[1]!
def pointAddDoubleNum2Stmt : Stmt Op := pointAddXEqMainBody[2]!
def pointAddDoubleNum3Stmt : Stmt Op := pointAddXEqMainBody[3]!
def pointAddDoubleDenStmt : Stmt Op := pointAddXEqMainBody[4]!

def pointAddDoubleXSqExpr : Expr Op :=
  match pointAddDoubleXSqStmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddDoubleXSqArgs : List (Expr Op) :=
  match pointAddDoubleXSqExpr with
  | .call _ args => args
  | _ => []

theorem pointAddDoubleXSqStmt_eq : pointAddDoubleXSqStmt =
    .letDecl ["\x00112", "\x00113"] (some pointAddDoubleXSqExpr) := by
  rfl

theorem pointAddDoubleXSqExpr_eq : pointAddDoubleXSqExpr =
    .call "\x009" pointAddDoubleXSqArgs := by
  rfl

theorem pointAddDoubleXSqArgs_eq : pointAddDoubleXSqArgs =
    [.builtin .mload [.builtin .mload [.lit (.number 1568)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]],
     .builtin .mload [.builtin .mload [.lit (.number 1568)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]]] := by
  rfl

def pointAddDoubleNum2Expr : Expr Op :=
  match pointAddDoubleNum2Stmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

theorem pointAddDoubleNum2Stmt_eq : pointAddDoubleNum2Stmt =
    .letDecl ["\x00114", "\x00115"] (some pointAddDoubleNum2Expr) := by
  rfl

theorem pointAddDoubleNum2Expr_eq : pointAddDoubleNum2Expr =
    .call "\x004"
      [.var "\x00112", .var "\x00113", .var "\x00112", .var "\x00113"] := by
  rfl

def pointAddDoubleNum3Expr : Expr Op :=
  match pointAddDoubleNum3Stmt with
  | .assign _ expr => expr
  | _ => .lit (.number 0)

theorem pointAddDoubleNum3Stmt_eq : pointAddDoubleNum3Stmt =
    .assign ["\x00114", "\x00115"] pointAddDoubleNum3Expr := by
  rfl

theorem pointAddDoubleNum3Expr_eq : pointAddDoubleNum3Expr =
    .call "\x004"
      [.var "\x00114", .var "\x00115", .var "\x00112", .var "\x00113"] := by
  rfl

def pointAddDoubleDenExpr : Expr Op :=
  match pointAddDoubleDenStmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddDoubleDenArgs : List (Expr Op) :=
  match pointAddDoubleDenExpr with
  | .call _ args => args
  | _ => []

theorem pointAddDoubleDenStmt_eq : pointAddDoubleDenStmt =
    .letDecl ["\x00116", "\x00117"] (some pointAddDoubleDenExpr) := by
  rfl

theorem pointAddDoubleDenExpr_eq : pointAddDoubleDenExpr =
    .call "\x004" pointAddDoubleDenArgs := by
  rfl

theorem pointAddDoubleDenArgs_eq : pointAddDoubleDenArgs =
    [.builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]]] := by
  rfl

def pointAddYSumExpr : Expr Op :=
  match pointAddYSumStmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddYSumArgs : List (Expr Op) :=
  match pointAddYSumExpr with
  | .call _ args => args
  | _ => []

theorem pointAddXEqBody_eq : pointAddXEqBody =
    [pointAddXEqMainStmt, .leave] := by
  rfl

theorem pointAddXEqMainStmt_eq : pointAddXEqMainStmt =
    .block pointAddXEqMainBody := by
  rfl

theorem pointAddXEqExceptionalStmt_eq : pointAddXEqExceptionalStmt =
    .block pointAddXEqExceptionalBody := by
  rfl

theorem pointAddXEqExceptionalBody_eq : pointAddXEqExceptionalBody =
    [pointAddYSumStmt, pointAddYZeroStmt] := by
  rfl

theorem pointAddYSumStmt_eq : pointAddYSumStmt =
    .letDecl ["\x00110", "\x00111"]
      (some pointAddYSumExpr) := by
  rfl

theorem pointAddYSumExpr_eq : pointAddYSumExpr =
    .call "\x004" pointAddYSumArgs := by
  rfl

theorem pointAddYSumArgs_eq : pointAddYSumArgs =
    [.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]],
         .builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]],
         .builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1600)], .lit (.number 64)]],
         .builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1600)], .lit (.number 96)]]] := by
  rfl

def pointAddYZeroCondition : Expr Op :=
  match pointAddYZeroStmt with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddYZeroBody : Block Op :=
  match pointAddYZeroStmt with
  | .cond _ body => body
  | _ => []

theorem pointAddYZeroStmt_eq : pointAddYZeroStmt =
    .cond pointAddYZeroCondition pointAddYZeroBody := by
  rfl

theorem pointAddYZeroCondition_eq : pointAddYZeroCondition =
    .call "\x002" [.var "\x00110", .var "\x00111"] := by
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
