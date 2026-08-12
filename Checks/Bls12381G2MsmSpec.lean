import Challenge.Bls12381.Vectors
import Challenge.Bls12381G2Msm.Spec

set_option warningAsError true

namespace Checks.Bls12381G2MsmSpec

open Challenge.Bls12381
open Challenge.Bls12381.ProofSupport
open Challenge.Bls12381G2Msm

private def oneByte : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded 1 1

private def paddingInvalid : ByteArray :=
  oneByte ++ Vectors.zeros 287

private def fieldInvalid : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded
      EvmSemantics.Crypto.Bls12381.p 64 ++
    Vectors.zeros 224

private def offCurve : ByteArray :=
  Vectors.zeros 192 ++
    EvmSemantics.Data.Bytes.natToBytesPadded 1 64 ++
    Vectors.zeros 32

private def maxScalarInput : ByteArray :=
  Vectors.generatorG2 ++
    EvmSemantics.Data.Bytes.natToBytesPadded (2 ^ 256 - 1) 32

private def decodesMaxScalar : Bool :=
  match decodeTerm maxScalarInput 0 with
  | some (_, scalar) => scalar.val == 2 ^ 256 - 1
  | none => false

example (input : ByteArray) (offset : Nat) :
    ScalarMul.Scalar256 := scalarAt input offset

example (input : ByteArray) (offset : Nat) :
    Option Msm.G2WireTerm := decodeTerm input offset

example (input : ByteArray) (offset count : Nat) :
    Option (List Msm.G2WireTerm) := decodeTerms input offset count

#guard pairBytes = Codec.g2Bytes + Codec.scalarBytes
#guard spec ByteArray.empty = none
#guard spec (Vectors.zeros 287) = none
#guard spec (Vectors.zeros 289) = none
#guard spec (Vectors.zeros 288) = some (Vectors.zeros Codec.g2Bytes)
#guard spec (Vectors.zeros 576) = some (Vectors.zeros Codec.g2Bytes)
#guard spec paddingInvalid = none
#guard spec fieldInvalid = none
#guard spec offCurve = none
#guard spec Vectors.g2MsmNonSubgroup = none
#guard spec Vectors.g2Msm.input = some Vectors.g2Msm.expected
#guard spec Vectors.g2MsmMulti.input = some Vectors.g2MsmMulti.expected
#guard decodesMaxScalar

end Checks.Bls12381G2MsmSpec
