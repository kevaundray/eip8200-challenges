import Challenge.Bls12381G1Add.Reference.Proofs.SourceSubRaw

set_option warningAsError true

open YulSemantics.EVM

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

example (ahi alo bhi blo : U256) :
    convPair (fpSubRawValue ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.subRaw
        { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }
        { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo } :=
  conv_fpSubRawValue ahi alo bhi blo

example (diff : U256 × U256) :
    YulEvmCompiler.conv (fpSubNeedsRepairValue diff) =
      EvmSemantics.UInt256.gt (convPair diff).hi
        Challenge.Bls12381.ProofSupport.Fp.modulusHi :=
  conv_fpSubNeedsRepairValue diff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubRawValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms conv_fpSubRawValue

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubNeedsRepairValue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms conv_fpSubNeedsRepairValue

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
