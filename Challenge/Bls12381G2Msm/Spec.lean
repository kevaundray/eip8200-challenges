import EvmSemantics.EVM.BigStep
import Challenge.Bls12381.ProofSupport.Subgroup

set_option warningAsError true

namespace Challenge.Bls12381G2Msm

open EvmSemantics EvmSemantics.EVM

def pairBytes : Nat := 288

abbrev inSubgroup := Challenge.Bls12381.ProofSupport.Subgroup.g2

/-- EIP-2537-conformant core. This adds the subgroup rejection omitted by the
pinned `Bls12381G2Msm.run?` wrapper. -/
def spec (input : ByteArray) : Option ByteArray := Id.run do
  if input.size = 0 ∨ input.size % pairBytes ≠ 0 then return none
  let k := input.size / pairBytes
  let mut acc : Crypto.Bls12381.G2Point := .infinity
  for i in [0:k] do
    let off := i * pairBytes
    match Crypto.Bls12381G2Add.decodePoint input off with
    | none => return none
    | some point =>
      if !inSubgroup point then return none
      let scalar := Data.Bytes.bytesToBigEndianNat
        (input.extract (off + 256) (off + pairBytes))
      acc := Crypto.G2.addPoint acc (Crypto.G2.scalarMul scalar point)
  return some (Crypto.Bls12381G2Add.encodePoint acc)

def deployAddress : AccountAddress := AccountAddress.ofNat 0x820e

def executionConfig : PrecompileConfig :=
  { disabled := [Precompile.blsG2MsmAddress] }

def initialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let account : Account := { Account.empty with code }
  let accounts := AccountMap.empty.set deployAddress account
  let env : ExecutionEnv := {
    (default : ExecutionEnv) with
    address := deployAddress
    codeAddr := deployAddress
    origin := AccountAddress.ofNat 0
    caller := AccountAddress.ofNat 0
    weiValue := 0
    calldata
    code
    gasPrice := 0
    depth := 0
    permitStateMutation := true
    blobVersionedHashes := #[]
    fork := .Osaka
    precompileConfig := executionConfig
  }
  { (default : EVM.State) with
    pc := 0
    stack := []
    execLength := 0
    halt := .Running
    callStack := []
    gasAvailable := gas
    activeWords := 0
    memory := .empty
    returnData := .empty
    hReturn := .empty
    accountMap := accounts
    substate := { Substate.empty with originalAccountMap := accounts }
    executionEnv := env }

def Matches (input : ByteArray) : ExecutionResult → Prop :=
  match spec input with
  | some output => fun result => result = .returned output
  | none => fun result => ∃ exception, result = .exception exception

def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, calldata.size < 2 ^ 64 →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      ∃ result, Eval (initialState code calldata g) result ∧ Matches calldata result

end Challenge.Bls12381G2Msm
