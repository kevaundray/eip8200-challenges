import Challenge.Bls12381.ProofSupport.G1Affine
import Challenge.Bls12381.ProofSupport.G2Affine
import Challenge.Bls12381.ProofSupport.CodecScalar

set_option warningAsError true

/-! Shared inversion-free scalar multiplication algorithms. -/

namespace Challenge.Bls12381.ProofSupport.ScalarMul

open EvmSemantics.Crypto.Bls12381

/-- An exact EIP-2537 scalar: an unreduced unsigned 256-bit integer. -/
abbrev Scalar256 := Fin (2 ^ 256)

/-- Package the exact scalar returned by the approved 32-byte codec. -/
def scalar256OfDecode {input : ByteArray} {offset scalar : Nat}
    (hdecode : Codec.decodeScalar input offset = some scalar) : Scalar256 :=
  ⟨scalar, Codec.decodeScalar_value_lt hdecode⟩

@[simp] theorem scalar256OfDecode_val {input : ByteArray} {offset scalar : Nat}
    (hdecode : Codec.decodeScalar input offset = some scalar) :
    (scalar256OfDecode hdecode).val = scalar := rfl

/-! ## Transparent binary scalar semantics -/

/-- Proof-friendly right-to-left binary double-and-add.  This transparent
recursion is the local mathematical scalar operation; no equality to the
pinned inverse-dependent curve scalar multiplication is claimed. -/
def binary {Point : Type} (zero : Point) (add : Point → Point → Point)
    (double : Point → Point) (scalar : Nat) (point : Point) : Point :=
  if hzero : scalar = 0 then zero
  else
    let rest := binary zero add double (scalar / 2) (double point)
    if scalar % 2 = 1 then add rest point else rest
termination_by scalar
decreasing_by
  exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero hzero) (by omega)

@[simp] theorem binary_zero {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    binary zero add double 0 point = zero := by
  rw [binary]
  simp

theorem binary_step {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) (hscalar : scalar ≠ 0) :
    binary zero add double scalar point =
      if scalar % 2 = 1 then
        add (binary zero add double (scalar / 2) (double point)) point
      else binary zero add double (scalar / 2) (double point) := by
  rw [binary]
  simp [hscalar]

theorem binary_even {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) :
    binary zero add double (2 * scalar) point =
      binary zero add double scalar (double point) := by
  cases scalar with
  | zero => simp
  | succ scalar =>
      rw [binary_step]
      · norm_num
      · omega

theorem binary_odd {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) :
    binary zero add double (2 * scalar + 1) point =
      add (binary zero add double scalar (double point)) point := by
  rw [binary_step]
  · rw [show (2 * scalar + 1) / 2 = scalar by omega]
    norm_num
  · omega

/-- Binary scalar multiplication preserves any invariant preserved by the
identity, addition, and doubling operations. -/
theorem binary_preserves {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (Valid : Point → Prop)
    (hzero : Valid zero)
    (hadd : ∀ left right, Valid left → Valid right → Valid (add left right))
    (hdouble : ∀ point, Valid point → Valid (double point))
    (scalar : Nat) (point : Point) (hpoint : Valid point) :
    Valid (binary zero add double scalar point) := by
  induction scalar using Nat.strong_induction_on generalizing point with
  | h scalar ih =>
      by_cases hscalar : scalar = 0
      · subst scalar
        simpa using hzero
      · rw [binary_step zero add double scalar point hscalar]
        have hhalf : scalar / 2 < scalar :=
          Nat.div_lt_self (Nat.zero_lt_of_ne_zero hscalar) (by omega)
        have hrest :
            Valid (binary zero add double (scalar / 2) (double point)) :=
          ih (scalar / 2) hhalf (double point) (hdouble point hpoint)
        by_cases hodd : scalar % 2 = 1
        · rw [if_pos hodd]
          exact hadd _ _ hrest hpoint
        · rw [if_neg hodd]
          exact hrest

/-! ## BLS12-381 curve instantiations -/

/-- Local EIP-correct G1 scalar multiplication. -/
def g1 (scalar : Nat) (point : G1Affine.Point) : G1Affine.Point :=
  binary G1Affine.infinity G1Affine.add G1Affine.double scalar point

/-- Local EIP-correct G2 scalar multiplication. -/
def g2 (scalar : Nat) (point : G2Affine.Point) : G2Affine.Point :=
  binary G2Affine.infinity G2Affine.add G2Affine.double scalar point

/-- Restrict G1 scalar multiplication to an exact EIP 256-bit scalar. -/
def g1Eip (scalar : Scalar256) (point : G1Affine.Point) : G1Affine.Point :=
  g1 scalar.val point

/-- Restrict G2 scalar multiplication to an exact EIP 256-bit scalar. -/
def g2Eip (scalar : Scalar256) (point : G2Affine.Point) : G2Affine.Point :=
  g2 scalar.val point

@[simp] theorem g1_zero (point : G1Affine.Point) :
    g1 0 point = G1Affine.infinity := binary_zero _ _ _ point

@[simp] theorem g2_zero (point : G2Affine.Point) :
    g2 0 point = G2Affine.infinity := binary_zero _ _ _ point

@[simp] theorem g1_one (point : G1Affine.Point) : g1 1 point = point := by
  simpa [g1, G1Affine.add] using
    binary_odd G1Affine.infinity G1Affine.add G1Affine.double 0 point

@[simp] theorem g2_one (point : G2Affine.Point) : g2 1 point = point := by
  simpa [g2, G2Affine.add] using
    binary_odd G2Affine.infinity G2Affine.add G2Affine.double 0 point

theorem g1_even (scalar : Nat) (point : G1Affine.Point) :
    g1 (2 * scalar) point = g1 scalar (G1Affine.double point) :=
  binary_even _ _ _ scalar point

theorem g2_even (scalar : Nat) (point : G2Affine.Point) :
    g2 (2 * scalar) point = g2 scalar (G2Affine.double point) :=
  binary_even _ _ _ scalar point

theorem g1_odd (scalar : Nat) (point : G1Affine.Point) :
    g1 (2 * scalar + 1) point =
      G1Affine.add (g1 scalar (G1Affine.double point)) point :=
  binary_odd _ _ _ scalar point

theorem g2_odd (scalar : Nat) (point : G2Affine.Point) :
    g2 (2 * scalar + 1) point =
      G2Affine.add (g2 scalar (G2Affine.double point)) point :=
  binary_odd _ _ _ scalar point

theorem g1_onCurve (scalar : Nat) (point : G1Affine.Point)
    (hpoint : G1Affine.OnCurve point) :
    G1Affine.OnCurve (g1 scalar point) :=
  binary_preserves _ _ _ G1Affine.OnCurve
    (LawfulAffine.onCurve_infinity G1Affine.curve)
    G1Affine.onCurve_add G1Affine.onCurve_double scalar point hpoint

theorem g2_onCurve (scalar : Nat) (point : G2Affine.Point)
    (hpoint : G2Affine.OnCurve point) :
    G2Affine.OnCurve (g2 scalar point) :=
  binary_preserves _ _ _ G2Affine.OnCurve
    (LawfulAffine.onCurve_infinity G2Affine.curve)
    G2Affine.onCurve_add G2Affine.onCurve_double scalar point hpoint

/-- Decode-level wire adapter for lawful G1 scalar multiplication. -/
def g1Wire (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.Point) :
    EvmSemantics.Crypto.Bls12381.Point :=
  G1Affine.toWire (g1 scalar (G1Affine.ofWire point))

/-- Decode-level wire adapter for lawful G2 scalar multiplication. -/
def g2Wire (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    EvmSemantics.Crypto.Bls12381.G2Point :=
  G2Affine.toWire (g2 scalar (G2Affine.ofWire point))

theorem g1Wire_refines (scalar : Nat)
    (point : EvmSemantics.Crypto.Bls12381.Point) :
    G1Affine.ofWire (g1Wire scalar point) =
      g1 scalar (G1Affine.ofWire point) := by
  simp [g1Wire]

theorem g2Wire_refines (scalar : Nat)
    (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    G2Affine.ofWire (g2Wire scalar point) =
      g2 scalar (G2Affine.ofWire point) := by
  simp [g2Wire]

end Challenge.Bls12381.ProofSupport.ScalarMul
