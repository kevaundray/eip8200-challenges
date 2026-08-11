import Challenge.Bls12381.Vectors
import Challenge.Bls12381G1Msm.Spec

set_option warningAsError true

namespace Checks.Bls12381G1MsmSpec

open Challenge.Bls12381
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G1Msm

private def oneByte : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded 1 1

private def paddingInvalid : ByteArray :=
  oneByte ++ Vectors.zeros 159

private def fieldInvalid : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded
      EvmSemantics.Crypto.Bls12381.p 64 ++
    Vectors.zeros 96

private def offCurve : ByteArray :=
  Vectors.zeros 64 ++
    EvmSemantics.Data.Bytes.natToBytesPadded 1 64 ++
    Vectors.zeros 32

private def maxScalarInput : ByteArray :=
  Vectors.generatorG1 ++
    EvmSemantics.Data.Bytes.natToBytesPadded (2 ^ 256 - 1) 32

private def decodesMaxScalar : Bool :=
  match decodeTerm maxScalarInput 0 with
  | some (_, scalar) => scalar.val == 2 ^ 256 - 1
  | none => false

example (input : ByteArray) (offset : Nat) :
    Option Msm.G1WireTerm := decodeTerm input offset

example (input : ByteArray) (offset count : Nat) :
    Option (List Msm.G1WireTerm) := decodeTerms input offset count

#guard pairBytes = Codec.g1Bytes + Codec.scalarBytes
#guard spec ByteArray.empty = none
#guard spec (Vectors.zeros 159) = none
#guard spec (Vectors.zeros 161) = none
#guard spec (Vectors.zeros 160) = some (Vectors.zeros Codec.g1Bytes)
#guard spec (Vectors.zeros 320) = some (Vectors.zeros Codec.g1Bytes)
#guard spec paddingInvalid = none
#guard spec fieldInvalid = none
#guard spec offCurve = none
#guard spec Vectors.g1MsmNonSubgroup = none
#guard spec Vectors.g1Msm.input = some Vectors.g1Msm.expected
#guard spec Vectors.g1MsmMulti.input = some Vectors.g1MsmMulti.expected
#guard decodesMaxScalar

end Checks.Bls12381G1MsmSpec
