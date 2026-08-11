import Challenge.Bls12381.ProofSupport.Fp2Source

set_option warningAsError true

namespace Checks.Bls12381Fp2SourceCanonical

open Challenge.Bls12381.ProofSupport

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.Canonical (Fp2.addSource a b) := Fp2.canonical_addSource ha hb

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.Canonical (Fp2.subSource a b) := Fp2.canonical_subSource ha hb

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.Canonical (Fp2.negSource a) := Fp2.canonical_negSource ha

example {a b : Fp2.Repr} (ha : Fp2.Canonical a) (hb : Fp2.Canonical b) :
    Fp2.Canonical (Fp2.mulSource a b) := Fp2.canonical_mulSource ha hb

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.Canonical (Fp2.sqrSource a) := Fp2.canonical_sqrSource ha

example {a : Fp2.Repr} (ha : Fp2.Canonical a) :
    Fp2.Canonical (Fp2.invSource a) := Fp2.canonical_invSource ha

example {a : Fp2.Repr} {s : Fp.Limbs}
    (ha : Fp2.Canonical a) (hs : Fp.Canonical s) :
    Fp2.Canonical (Fp2.mulFpSource a s) := Fp2.canonical_mulFpSource ha hs

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.canonical_iff

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mkRepr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.canonical_mkRepr

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.mulSource_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.mulSource_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.sqrSource_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.sqrSource_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.invSource_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.invSource_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_addSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_addSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_subSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_subSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_negSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_negSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_mulSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_sqrSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_sqrSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_invSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_invSource

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.canonical_mulFpSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp2.canonical_mulFpSource

end Checks.Bls12381Fp2SourceCanonical
