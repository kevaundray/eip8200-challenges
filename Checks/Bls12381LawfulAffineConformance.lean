import Challenge.Bls12381.Vectors
import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.LawfulG1Affine
import Challenge.Bls12381.ProofSupport.LawfulG2Affine

set_option warningAsError true

/-! # Lawful affine regressions against EIP-2537 vectors -/

namespace Checks.Bls12381LawfulAffineConformance

open Challenge.Bls12381
open Challenge.Bls12381.ProofSupport
open EvmSemantics.Crypto.Bls12381

private def inverseGeneratorG1 : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded Gx 64 ++
    EvmSemantics.Data.Bytes.natToBytesPadded (p - Gy) 64

private def inverseGeneratorG2 : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded G2xC0 64 ++
    EvmSemantics.Data.Bytes.natToBytesPadded G2xC1 64 ++
    EvmSemantics.Data.Bytes.natToBytesPadded (p - G2yC0) 64 ++
    EvmSemantics.Data.Bytes.natToBytesPadded (p - G2yC1) 64

private def lawfulG1DoubleMatches : Bool :=
  match Codec.decodeG1 Vectors.generatorG1 0 with
  | none => false
  | some generator =>
      Codec.encodeG1 (G1Affine.toWire
        (G1Affine.double (G1Affine.ofWire generator))) ==
        Vectors.g1Msm.expected

private def lawfulG2DoubleMatches : Bool :=
  match Codec.decodeG2 Vectors.generatorG2 0 with
  | none => false
  | some generator =>
      Codec.encodeG2 (G2Affine.toWire
        (G2Affine.double (G2Affine.ofWire generator))) ==
        Vectors.g2Msm.expected

private def lawfulG1InverseMatches : Bool :=
  match Codec.decodeG1 Vectors.generatorG1 0 with
  | none => false
  | some generator =>
      Codec.encodeG1 (G1Affine.toWire
        (G1Affine.neg (G1Affine.ofWire generator))) == inverseGeneratorG1

private def lawfulG2InverseMatches : Bool :=
  match Codec.decodeG2 Vectors.generatorG2 0 with
  | none => false
  | some generator =>
      Codec.encodeG2 (G2Affine.toWire
        (G2Affine.neg (G2Affine.ofWire generator))) == inverseGeneratorG2

private def lawfulG1InverseAddsToInfinity : Bool :=
  match Codec.decodeG1 Vectors.generatorG1 0 with
  | none => false
  | some generator =>
      let point := G1Affine.ofWire generator
      Codec.encodeG1 (G1Affine.toWire (G1Affine.add point (G1Affine.neg point))) ==
        Vectors.zeros Codec.g1Bytes

private def lawfulG2InverseAddsToInfinity : Bool :=
  match Codec.decodeG2 Vectors.generatorG2 0 with
  | none => false
  | some generator =>
      let point := G2Affine.ofWire generator
      Codec.encodeG2 (G2Affine.toWire (G2Affine.add point (G2Affine.neg point))) ==
        Vectors.zeros Codec.g2Bytes

private def lawfulG1InfinityIdentity : Bool :=
  match Codec.decodeG1 Vectors.generatorG1 0 with
  | none => false
  | some generator =>
      Codec.encodeG1 (G1Affine.toWire
        (G1Affine.add .infinity (G1Affine.ofWire generator))) ==
        Vectors.generatorG1

private def lawfulG2InfinityIdentity : Bool :=
  match Codec.decodeG2 Vectors.generatorG2 0 with
  | none => false
  | some generator =>
      Codec.encodeG2 (G2Affine.toWire
        (G2Affine.add .infinity (G2Affine.ofWire generator))) ==
        Vectors.generatorG2

#guard lawfulG1DoubleMatches
#guard lawfulG2DoubleMatches
#guard lawfulG1InverseMatches
#guard lawfulG2InverseMatches
#guard lawfulG1InverseAddsToInfinity
#guard lawfulG2InverseAddsToInfinity
#guard lawfulG1InfinityIdentity
#guard lawfulG2InfinityIdentity

end Checks.Bls12381LawfulAffineConformance
