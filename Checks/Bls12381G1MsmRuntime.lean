import Challenge.Bls12381G1Msm.Reference

set_option warningAsError true

open Challenge.Bls12381G1Msm

#guard referenceSource.length > 0
#guard referenceBlock?.isSome
#guard referenceBytecode.size = 2259
#guard referenceBytecode? = some referenceBytecode
