import Challenge.Bls12381G1Msm.Reference.Source
import EvmSemantics.Data.Hex

set_option warningAsError true

namespace Challenge.Bls12381G1Msm

open EvmSemantics

/-- Frozen output of
`lake exe yulc Challenge/Bls12381G1Msm/Reference/reference.yul`. -/
def referenceHex : String := (include_str "reference.hex").trimAscii.copy

/-- Frozen concrete runtime used by the G1MSM challenge. -/
def referenceBytecode : ByteArray := Hex.hexToBytes referenceHex

end Challenge.Bls12381G1Msm
