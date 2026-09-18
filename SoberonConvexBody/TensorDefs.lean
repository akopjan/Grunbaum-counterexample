import Mathlib

/-!
# The analytic tensors from Soberon's Theorem 2

This file defines the explicit tensors used in Section 3 of Soberon's v2
proof.  The elementary polarization identities are proved here.  The global nonvanishing statement remains in Tensors.lean. This module
contains only definitions and elementary proofs, so it can be checked separately.
-/

noncomputable section

namespace SoberonConvexBody
namespace Tensors

open scoped BigOperators

abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev E5 := EuclideanSpace ℝ (Fin 5)

/-- Coordinate notation. -/
local notation "x₀(" x ")" => x (0 : Fin 4)
local notation "x₁(" x ")" => x (1 : Fin 4)
local notation "x₂(" x ")" => x (2 : Fin 4)
local notation "x₃(" x ")" => x (3 : Fin 4)

/-- The symmetric bilinear form with matrix
`[[0,1,1,1],[1,1,0,0],[1,0,2,0],[1,0,0,4]]`. -/
def mForm (x y : E4) : ℝ :=
  x₀(x) * (x₁(y) + x₂(y) + x₃(y)) +
  x₁(x) * (x₀(y) + x₁(y)) +
  x₂(x) * (x₀(y) + 2 * x₂(y)) +
  x₃(x) * (x₀(y) + 4 * x₃(y))

/-- `N = M + e₀ e₀ᵀ`. -/
def nForm (x y : E4) : ℝ := mForm x y + x₀(x) * x₀(y)

/-- Polarization of `x₀ * mForm x x`. -/
def A0 (x y z : E4) : ℝ :=
  (x₀(x) * mForm y z + x₀(y) * mForm x z + x₀(z) * mForm x y) / 3

/-- The symmetric trilinear form whose diagonal polynomial is `6 x₁ x₂ x₃`. -/
def C (x y z : E4) : ℝ :=
    x₁(x) * x₂(y) * x₃(z) + x₁(x) * x₃(y) * x₂(z)
  + x₂(x) * x₁(y) * x₃(z) + x₂(x) * x₃(y) * x₁(z)
  + x₃(x) * x₁(y) * x₂(z) + x₃(x) * x₂(y) * x₁(z)

/-- Polarization of `(nForm x x)^2`. -/
def B (w x y z : E4) : ℝ :=
  (nForm w x * nForm y z + nForm w y * nForm x z +
    nForm w z * nForm x y) / 3

/-- The perturbed cubic tensor. -/
def A (tau : ℝ) (x y z : E4) : ℝ := A0 x y z + tau * C x y z

/-- Diagonal polynomial associated to `A0`. -/
theorem A0_diag (x : E4) :
    A0 x x x = x₀(x) * mForm x x := by
  simp [A0]
  ring

/-- Diagonal polynomial associated to `C`. -/
theorem C_diag (x : E4) :
    C x x x = 6 * x₁(x) * x₂(x) * x₃(x) := by
  simp [C]
  ring

/-- Diagonal polynomial associated to `B`. -/
theorem B_diag (x : E4) :
    B x x x x = (nForm x x)^2 := by
  simp [B]
  ring

/-- The formula used throughout Soberon's proof. -/
theorem three_mul_A0 (x y z : E4) :
    3 * A0 x y z =
      x₀(x) * mForm y z + x₀(y) * mForm x z + x₀(z) * mForm x y := by
  simp [A0]
  ring

/-- Four-linear polarization identity for the quartic. -/
theorem three_mul_B (q0 q1 q2 q3 : E4) :
    3 * B q0 q1 q2 q3 =
      nForm q0 q1 * nForm q2 q3 +
      nForm q0 q2 * nForm q1 q3 +
      nForm q0 q3 * nForm q1 q2 := by
  simp [B]
  ring

/-- Ordered orthonormal frame. -/
def IsONFrame (q : Fin 4 → E4) : Prop :=
  ∀ i j, inner ℝ (q i) (q j) = if i = j then 1 else 0

/-- Every vector in an orthonormal frame has norm one. -/
theorem IsONFrame.norm_eq_one {q : Fin 4 → E4} (hq : IsONFrame q) (i : Fin 4) :
    ‖q i‖ = 1 := by
  have hi : inner ℝ (q i) (q i) = 1 := by simpa using hq i i
  rw [real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (q i)]

/-- The five contractions in Theorem 2. -/
def obstruction (tau : ℝ) (q : Fin 4 → E4) : E5 :=
  WithLp.toLp 2 ![A tau (q 1) (q 2) (q 3),
    A tau (q 0) (q 2) (q 3),
    A tau (q 0) (q 1) (q 3),
    A tau (q 0) (q 1) (q 2),
    B (q 0) (q 1) (q 2) (q 3)]

@[simp] theorem A_zero (x y z : E4) : A 0 x y z = A0 x y z := by
  simp [A]

/-- Evaluating the five coordinates characterizes the zero vector. -/
theorem obstruction_eq_zero_iff (tau : Real) (q : Fin 4 -> E4) :
    obstruction tau q = 0 <->
      A tau (q 1) (q 2) (q 3) = 0 /\
      A tau (q 0) (q 2) (q 3) = 0 /\
      A tau (q 0) (q 1) (q 3) = 0 /\
      A tau (q 0) (q 1) (q 2) = 0 /\
      B (q 0) (q 1) (q 2) (q 3) = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun v : E5 => v 0) h
    have h1 := congrArg (fun v : E5 => v 1) h
    have h2 := congrArg (fun v : E5 => v 2) h
    have h3 := congrArg (fun v : E5 => v 3) h
    have h4 := congrArg (fun v : E5 => v 4) h
    exact ⟨by simpa [obstruction, PiLp.toLp_apply] using h0,
      by simpa [obstruction, PiLp.toLp_apply] using h1,
      by simpa [obstruction, PiLp.toLp_apply] using h2,
      by simpa [obstruction, PiLp.toLp_apply] using h3,
      by simpa [obstruction, PiLp.toLp_apply] using h4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    ext i
    fin_cases i <;> simp [obstruction, PiLp.toLp_apply, h0, h1, h2, h3, h4]

end Tensors
end SoberonConvexBody
