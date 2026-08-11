import Challenge.Bls12381.ProofSupport.Fp2SourceDefs

set_option warningAsError true

/-! # Auditable source-order Fp2 operation schedules -/

namespace Challenge.Bls12381.ProofSupport.Fp2

inductive SourceRef where
  | a0 | a1 | b0 | b1
  | v0 | v1 | aSum | bSum | cross | vSum | c0 | c1
  | a0Square | a1Square | norm | normInv | negA1
deriving DecidableEq

inductive SourceEvent where
  | add (left right output : SourceRef)
  | sub (left right output : SourceRef)
  | mul (left right output : SourceRef)
  | square (input output : SourceRef)
  | inv (input output : SourceRef)
  | neg (input output : SourceRef)
deriving DecidableEq

structure Traced (α : Type) where
  value : α
  events : List SourceEvent

def tracedAdd (left right output : SourceRef) (a b : Fp.Limbs) :
    Traced Fp.Limbs :=
  ⟨Fp.addSource a b, [.add left right output]⟩

def tracedSub (left right output : SourceRef) (a b : Fp.Limbs) :
    Traced Fp.Limbs :=
  ⟨Fp.subSource a b, [.sub left right output]⟩

def tracedMul (left right output : SourceRef) (a b : Fp.Limbs) :
    Traced Fp.Limbs :=
  ⟨Fp.mulCanonical a b, [.mul left right output]⟩

def tracedSquare (input output : SourceRef) (a : Fp.Limbs) :
    Traced Fp.Limbs :=
  ⟨Fp.squareCanonical a, [.square input output]⟩

def tracedInv (input output : SourceRef) (a : Fp.Limbs) :
    Traced Fp.Limbs :=
  ⟨Fp.invCanonical a, [.inv input output]⟩

def tracedNeg (input output : SourceRef) (a : Fp.Limbs) :
    Traced Fp.Limbs :=
  ⟨Fp.negSource a, [.neg input output]⟩

structure MulSourceTrace where
  v0 : Fp.Limbs
  v1 : Fp.Limbs
  aSum : Fp.Limbs
  bSum : Fp.Limbs
  cross : Fp.Limbs
  vSum : Fp.Limbs
  c1 : Fp.Limbs
  result : Repr
  events : List SourceEvent

def mulSourceDag : List SourceEvent :=
  [.mul .a0 .b0 .v0,
   .mul .a1 .b1 .v1,
   .add .a0 .a1 .aSum,
   .add .b0 .b1 .bSum,
   .mul .aSum .bSum .cross,
   .add .v0 .v1 .vSum,
   .sub .cross .vSum .c1,
   .sub .v0 .v1 .c0]

/-- Authoritative source-order Fp2 multiplication evaluator. Each value is
produced by the same traced primitive that emits its symbolic DAG event. -/
def runMulSource (a b : Repr) : MulSourceTrace :=
  let v0 := tracedMul .a0 .b0 .v0 a.c0 b.c0
  let v1 := tracedMul .a1 .b1 .v1 a.c1 b.c1
  let aSum := tracedAdd .a0 .a1 .aSum a.c0 a.c1
  let bSum := tracedAdd .b0 .b1 .bSum b.c0 b.c1
  let cross := tracedMul .aSum .bSum .cross aSum.value bSum.value
  let vSum := tracedAdd .v0 .v1 .vSum v0.value v1.value
  let c1 := tracedSub .cross .vSum .c1 cross.value vSum.value
  let c0 := tracedSub .v0 .v1 .c0 v0.value v1.value
  { v0 := v0.value, v1 := v1.value
    aSum := aSum.value, bSum := bSum.value
    cross := cross.value, vSum := vSum.value, c1 := c1.value
    result := mkRepr c0.value c1.value
    events := v0.events ++ v1.events ++ aSum.events ++ bSum.events ++
      cross.events ++ vSum.events ++ c1.events ++ c0.events }

theorem runMulSource_events (a b : Repr) :
    (runMulSource a b).events = mulSourceDag := rfl

def mulSource (a b : Repr) : Repr :=
  (runMulSource a b).result

theorem mulSource_eq (a b : Repr) :
    mulSource a b =
      let v0 := mulV0Source a b
      let v1 := mulV1Source a b
      let c1 := mulImaginarySource a b v0 v1
      mkRepr (mulRealSource v0 v1) c1 := by
  change (runMulSource a b).result = _
  simp only [runMulSource, tracedMul, tracedAdd, tracedSub,
    mulV0Source, mulV1Source, mulImaginarySource, mulRealSource]

structure InvSourceTrace where
  norm : Fp.Limbs
  normInv : Fp.Limbs
  c0 : Fp.Limbs
  c1 : Fp.Limbs
  result : Repr
  events : List SourceEvent

def invSourceDag : List SourceEvent :=
  [.square .a0 .a0Square,
   .square .a1 .a1Square,
   .add .a0Square .a1Square .norm,
   .inv .norm .normInv,
   .mul .a0 .normInv .c0,
   .neg .a1 .negA1,
   .mul .negA1 .normInv .c1]

/-- Authoritative source-order Fp2 inversion evaluator. Both output products
consume the single `.normInv` result recorded by the DAG. -/
def runInvSource (a : Repr) : InvSourceTrace :=
  let a0Square := tracedSquare .a0 .a0Square a.c0
  let a1Square := tracedSquare .a1 .a1Square a.c1
  let norm := tracedAdd .a0Square .a1Square .norm
    a0Square.value a1Square.value
  let normInv := tracedInv .norm .normInv norm.value
  let c0 := tracedMul .a0 .normInv .c0 a.c0 normInv.value
  let negA1 := tracedNeg .a1 .negA1 a.c1
  let c1 := tracedMul .negA1 .normInv .c1 negA1.value normInv.value
  { norm := norm.value, normInv := normInv.value
    c0 := c0.value, c1 := c1.value
    result := mkRepr c0.value c1.value
    events := a0Square.events ++ a1Square.events ++ norm.events ++
      normInv.events ++ c0.events ++ negA1.events ++ c1.events }

theorem runInvSource_events (a : Repr) :
    (runInvSource a).events = invSourceDag := rfl

def invSource (a : Repr) : Repr :=
  (runInvSource a).result

theorem invSource_eq (a : Repr) :
    invSource a =
      let norm := invNormSource a
      let normInv := Fp.invCanonical norm
      mkRepr (invRealSource a.c0 normInv)
        (invImaginarySource a.c1 normInv) := by
  change (runInvSource a).result = _
  simp only [runInvSource, tracedSquare, tracedAdd, tracedInv, tracedMul,
    tracedNeg, invNormSource, invRealSource, invImaginarySource]

end Challenge.Bls12381.ProofSupport.Fp2
