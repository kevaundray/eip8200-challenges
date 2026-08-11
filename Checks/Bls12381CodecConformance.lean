import Challenge.Bls12381.Vectors
import Challenge.Bls12381.ProofSupport.CodecFp
import Challenge.Bls12381.ProofSupport.CodecFp2
import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.CodecScalar
import Challenge.Bls12381.ProofSupport.CodecSubgroup

set_option warningAsError true

/-! # Official-vector codec regressions -/

namespace Checks.Bls12381CodecConformance

open Challenge.Bls12381
open Challenge.Bls12381.ProofSupport

#guard (Codec.decodeG1 Vectors.generatorG1 0).isSome
#guard (Codec.decodeG2 Vectors.generatorG2 0).isSome

#guard (Codec.decodeG1 Vectors.nonSubgroupG1 0).isSome
#guard (Codec.decodeG2 Vectors.nonSubgroupG2 0).isSome
#guard Codec.decodeG1Subgroup Vectors.nonSubgroupG1 0 = none
#guard Codec.decodeG2Subgroup Vectors.nonSubgroupG2 0 = none

#guard Codec.decodeScalar Vectors.g1Msm.input Codec.g1Bytes = some 2
#guard Codec.decodeScalar Vectors.g2Msm.input Codec.g2Bytes = some 2

#guard (Codec.decodeFp Vectors.mapFpToG1.input 0).isSome
#guard (Codec.decodeFp2 Vectors.mapFp2ToG2.input 0).isSome

end Checks.Bls12381CodecConformance
