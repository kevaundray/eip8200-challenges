import Challenge.EvmProof.ModexpFixed

set_option warningAsError true

namespace Challenge.EvmProof.ModexpFixed

open EvmSemantics.EVM

example {input : ByteArray} {base exponent modulus expHead : Nat}
    (hbaseSize : Precompile.bytesToNatPadded input 0 32 = 48)
    (hexponentSize : Precompile.bytesToNatPadded input 32 32 = 48)
    (hmodulusSize : Precompile.bytesToNatPadded input 64 32 = 48)
    (hbase : Precompile.bytesToNatPadded input 96 48 = base)
    (hexponent : Precompile.bytesToNatPadded input 144 48 = exponent)
    (hmodulus : Precompile.bytesToNatPadded input 192 48 = modulus)
    (hexponentHead : Precompile.bytesToNatPadded input 144 32 = expHead)
    (hcost : Precompile.modexpGas .Osaka 48 48 48 expHead = 36576) :
    Precompile.runModexp .Osaka input 36576 =
      .success (Precompile.natToBytes
        (Precompile.modPow base exponent modulus) 48) 36576 :=
  runModexp_48_48_48 hbaseSize hexponentSize hmodulusSize hbase
    hexponent hmodulus hexponentHead hcost

/-- info: 'Challenge.EvmProof.ModexpFixed.runModexp_48_48_48' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms runModexp_48_48_48

end Challenge.EvmProof.ModexpFixed
