import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubEnvLookup
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalPostludeFull

set_option warningAsError true

/-! Single bridge from the final field subtraction to the output-store postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalPostContext (yst : EvmState)
    (out left right : U256) : PointAddUnequalPostContext where
  env := pointAddUnequalYSubConcreteEnv yst out left right
  state := pointAddUnequalYSubConcreteState yst out left right
  xHi := (pointAddUnequalXSubResult yst out left right).1
  xLo := (pointAddUnequalXSubResult yst out left right).2
  yHi := (pointAddUnequalYSubResult
    (pointAddUnequalYSubContext yst out left right)).1
  yLo := (pointAddUnequalYSubResult
    (pointAddUnequalYSubContext yst out left right)).2
  tempHi := (pointAddUnequalDeltaResult
    (pointAddUnequalDeltaContext yst out left right)).1
  tempLo := (pointAddUnequalDeltaResult
    (pointAddUnequalDeltaContext yst out left right)).2
  env_xHi := pointAddUnequalYSubConcreteEnv_xHi yst out left right
  env_xLo := pointAddUnequalYSubConcreteEnv_xLo yst out left right
  env_yHi := pointAddUnequalYSubConcreteEnv_yHi yst out left right
  env_yLo := pointAddUnequalYSubConcreteEnv_yLo yst out left right
  env_tempHi := pointAddUnequalYSubConcreteEnv_tempHi yst out left right
  env_tempLo := pointAddUnequalYSubConcreteEnv_tempLo yst out left right

def pointAddUnequalFinalEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  pointAddUnequalPostEnv (pointAddUnequalPostContext yst out left right)

def pointAddUnequalFinalState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddUnequalPostState (pointAddUnequalPostContext yst out left right)

theorem step_pointAddUnequalPostlude (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalPostContext yst out left right).env
      (pointAddUnequalPostContext yst out left right).state
      pointAddUnequalPostlude
      (pointAddUnequalPostEnv (pointAddUnequalPostContext yst out left right))
      (pointAddUnequalPostState (pointAddUnequalPostContext yst out left right))
      .normal :=
  step_pointAddUnequalPostludeGeneric
    (pointAddUnequalPostContext yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
