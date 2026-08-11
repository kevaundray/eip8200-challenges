import Challenge.Bls12381G2Add.Reference.Source
import Challenge.Bls12381G2Add.Reference.FrozenBytecode
import EvmSemantics.Data.Hex

set_option warningAsError true

namespace Challenge.Bls12381G2Add

open EvmSemantics

/-- Frozen output of `lake exe yulc Challenge/Bls12381G2Add/Reference/reference.yul`. -/
def referenceHex : String := (include_str "reference.hex").trimAscii.copy

/-- Source-hex decoding retained as an executable artifact regression. -/
def decodedReferenceBytecode : ByteArray := Hex.hexToBytes referenceHex

/-- Concrete runtime scored and proved by the G2ADD challenge. -/
def referenceBytecode : ByteArray := ByteArray.mk frozenReferenceBytes.toArray

def referenceBytecodeSize : Nat := 3339

end Challenge.Bls12381G2Add

