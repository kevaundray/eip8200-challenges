import Challenge.Bls12381.ProofSupport.FpConstants

set_option warningAsError true

/-! # Source-faithful BLS12-381 base-field add/sub/neg schedules -/

namespace Challenge.Bls12381.ProofSupport.Fp

open EvmSemantics

def addRaw (a b : Limbs) : Limbs :=
  let sLo := a.lo + b.lo
  let carry := UInt256.lt sLo a.lo
  { hi := a.hi + b.hi + carry, lo := sLo }

def addNeedsCorrection (sum : Limbs) : UInt256 :=
  UInt256.lor (UInt256.gt sum.hi modulusHi)
    (UInt256.land (UInt256.eq sum.hi modulusHi)
      (UInt256.isZero (UInt256.lt sum.lo modulusLo)))

def addCorrect (sum : Limbs) : Limbs :=
  let newLo := sum.lo - modulusLo
  { hi := sum.hi - (modulusHi + UInt256.gt modulusLo sum.lo)
    lo := newLo }

def addSource (a b : Limbs) : Limbs :=
  let sum := addRaw a b
  if (addNeedsCorrection sum).toNat ≠ 0 then addCorrect sum else sum

def subRaw (a b : Limbs) : Limbs :=
  { hi := a.hi - b.hi - UInt256.gt b.lo a.lo
    lo := a.lo - b.lo }

def subRepair (diff : Limbs) : Limbs :=
  let newLo := diff.lo + modulusLo
  { hi := diff.hi + modulusHi + UInt256.lt newLo diff.lo
    lo := newLo }

def subSource (a b : Limbs) : Limbs :=
  let diff := subRaw a b
  if (UInt256.gt diff.hi modulusHi).toNat ≠ 0 then subRepair diff else diff

def negNonzero (a : Limbs) : Limbs :=
  { hi := modulusHi - a.hi - UInt256.gt a.lo modulusLo
    lo := modulusLo - a.lo }

def negSource (a : Limbs) : Limbs :=
  if a.hi.toNat = 0 ∧ a.lo.toNat = 0 then pack 0 else negNonzero a

end Challenge.Bls12381.ProofSupport.Fp
