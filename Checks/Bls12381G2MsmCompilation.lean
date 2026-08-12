import Challenge.Bls12381G2Msm.Reference.Proofs.FrozenBlock

set_option warningAsError true

open Challenge.Bls12381G2Msm
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

#guard referenceBlock?.isSome
#guard referenceNormalizedBlock?.map List.length = some 41
#guard frozenReferenceBlock.length = 41

#guard referenceNormalizedChunk0Matches
#guard referenceNormalizedChunk1Matches
#guard referenceNormalizedChunk2Matches
#guard referenceNormalizedChunk3Matches
#guard referenceNormalizedChunk4Matches
#guard referenceNormalizedChunk5Matches
#guard referenceNormalizedChunk6Matches
#guard referenceNormalizedChunk7Matches
#guard referenceNormalizedChunk8Matches
#guard referenceNormalizedChunk9Matches
#guard referenceNormalizedChunk10Matches
