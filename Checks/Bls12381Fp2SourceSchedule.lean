import Challenge.Bls12381.ProofSupport.Fp2SourceSchedule
import Challenge.Bls12381.ProofSupport.Fp2Source

set_option warningAsError true

namespace Checks.Bls12381Fp2SourceSchedule

open Challenge.Bls12381.ProofSupport

example (a : Fp2.Repr) :
    Fp2.Canonical a ↔ Fp.Canonical a.c0 ∧ Fp.Canonical a.c1 :=
  Fp2.canonical_iff a

example (a b : Fp2.Repr) :
    Fp2.addSource a b =
      { c0 := Fp.addSource a.c0 b.c0
        c1 := Fp.addSource a.c1 b.c1 } := rfl

example (a b : Fp2.Repr) :
    Fp2.subSource a b =
      { c0 := Fp.subSource a.c0 b.c0
        c1 := Fp.subSource a.c1 b.c1 } := rfl

example (a : Fp2.Repr) :
    Fp2.negSource a =
      { c0 := Fp.negSource a.c0
        c1 := Fp.negSource a.c1 } := rfl

example (a b : Fp2.Repr) :
    Fp2.mulSource a b =
      let v0 := Fp2.mulV0Source a b
      let v1 := Fp2.mulV1Source a b
      let c1 := Fp2.mulImaginarySource a b v0 v1
      Fp2.mkRepr (Fp2.mulRealSource v0 v1) c1 :=
  Fp2.mulSource_eq a b

example : Fp2.mulSourceDag =
    [.mul .a0 .b0 .v0,
     .mul .a1 .b1 .v1,
     .add .a0 .a1 .aSum,
     .add .b0 .b1 .bSum,
     .mul .aSum .bSum .cross,
     .add .v0 .v1 .vSum,
     .sub .cross .vSum .c1,
     .sub .v0 .v1 .c0] := rfl

example (a b : Fp2.Repr) :
    (Fp2.runMulSource a b).events = Fp2.mulSourceDag :=
  Fp2.runMulSource_events a b

example (a : Fp2.Repr) :
    Fp2.sqrSource a =
      let c0 := Fp.mulCanonical
        (Fp.addSource a.c0 a.c1) (Fp.subSource a.c0 a.c1)
      let product := Fp.mulCanonical a.c0 a.c1
      let c1 := Fp.addSource product product
      { c0, c1 } := rfl

example (a : Fp2.Repr) :
    Fp2.sqrSource a =
      Fp2.mkRepr (Fp2.sqrRealSource a) (Fp2.sqrC1Source a) :=
  Fp2.sqrSource_eq a

example (a : Fp2.Repr) :
    Fp2.invSource a =
      let norm := Fp2.invNormSource a
      let normInv := Fp.invCanonical norm
      Fp2.mkRepr (Fp2.invRealSource a.c0 normInv)
        (Fp2.invImaginarySource a.c1 normInv) :=
  Fp2.invSource_eq a

example : Fp2.invSourceDag =
    [.square .a0 .a0Square,
     .square .a1 .a1Square,
     .add .a0Square .a1Square .norm,
     .inv .norm .normInv,
     .mul .a0 .normInv .c0,
     .neg .a1 .negA1,
     .mul .negA1 .normInv .c1] := rfl

example (a : Fp2.Repr) :
    (Fp2.runInvSource a).events = Fp2.invSourceDag :=
  Fp2.runInvSource_events a

example (a : Fp2.Repr) (s : Fp.Limbs) :
    Fp2.mulFpSource a s =
      { c0 := Fp.mulCanonical a.c0 s
        c1 := Fp.mulCanonical a.c1 s } := rfl

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.runMulSource_events' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.runMulSource_events

/-- info: 'Challenge.Bls12381.ProofSupport.Fp2.runInvSource_events' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp2.runInvSource_events

end Checks.Bls12381Fp2SourceSchedule
