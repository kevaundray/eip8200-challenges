import Challenge.Bls12381G2Add.Reference

set_option warningAsError true

open Challenge.Bls12381G2Add

#guard referenceBlock?.isSome
#guard optimizedReferenceBytecode?.isSome
#guard referenceNormalizedBlock?.isSome
#guard referenceBytecode?.isSome
#guard referenceBytecode? = some referenceBytecode
#guard decodedReferenceBytecode = referenceBytecode
#guard referenceBytecode.size = referenceBytecodeSize
#guard referenceBytecodeSize = 2788
