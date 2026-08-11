import Challenge.Bls12381G1Add.Reference.Source
import EvmSemantics.Data.Hex

set_option warningAsError true

namespace Challenge.Bls12381G1Add

open EvmSemantics

/-- Frozen output of `lake exe yulc Challenge/Bls12381G1Add/Reference/reference.yul`. -/
def referenceHex : String := (include_str "reference.hex").trimAscii.copy

/-- Concrete runtime scored and proved by the G1ADD challenge. -/
def referenceBytecode : ByteArray := Hex.hexToBytes referenceHex

end Challenge.Bls12381G1Add
