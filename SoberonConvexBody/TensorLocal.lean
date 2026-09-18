import SoberonConvexBody.TensorZeroAlgebra

/-!
# Local elimination of tensor zeros

This module proves local nonvanishing by exact polynomial elimination and
quadratic inequalities. No differentiability theorem or local inverse theorem
is needed. The neighborhood is a concrete open semialgebraic set of frames.
-/

noncomputable section
namespace SoberonConvexBody.Tensors
open Set

/-- Standard coordinate vector. -/
def coordinateVector (i : Fin 4) : E4 :=
  EuclideanSpace.single i 1

/-- Standard ordered frame. -/
def standardFrame : Fin 4 -> E4 := coordinateVector

@[simp] theorem coordinateVector_apply (i j : Fin 4) :
    coordinateVector i j = if j = i then (1 : Real) else 0 := by
  simp [coordinateVector, EuclideanSpace.single_apply, eq_comm]

/-- The linear coefficients in the three equations containing column zero. -/
def localB (q : Fin 4 -> E4) (i : Fin 4) : Real := mForm (q 0) (q i)

/-- Coefficient of the perturbation after eliminating the three cubics. -/
def localD (q : Fin 4 -> E4) : Real :=
  q 0 0 * C (q 1) (q 2) (q 3) -
    q 1 0 * C (q 0) (q 2) (q 3) -
    q 2 0 * C (q 0) (q 1) (q 3) -
    q 3 0 * C (q 0) (q 1) (q 2)

/-- The perturbation term in the eliminated quartic equation. -/
def localE (q : Fin 4 -> E4) : Real :=
  (localB q 1 + q 0 0 * q 1 0) * C (q 0) (q 2) (q 3) +
  (localB q 2 + q 0 0 * q 2 0) * C (q 0) (q 1) (q 3) +
  (localB q 3 + q 0 0 * q 3 0) * C (q 0) (q 1) (q 2)

def localV1 (q : Fin 4 -> E4) : Real :=
  1 - localB q 2 * localB q 3 + (3 / 2 : Real) * (q 0 0)^2 * q 2 0 * q 3 0

def localV2 (q : Fin 4 -> E4) : Real := 1 - localB q 1 * localB q 3

def localV3 (q : Fin 4 -> E4) : Real := 1 - localB q 1 * localB q 2

def localW (q : Fin 4 -> E4) : Real :=
  (3 / 4 : Real) * q 0 0 * localD q + (3 / 2 : Real) * localE q

/-- A neighborhood on which the elementary estimates have ample slack. -/
def tensorIdentityNeighborhood : Set (Fin 4 -> E4) :=
  {q | (1 / 2 : Real) < localD q ∧
    |localB q 1 - 1| < (1 / 16 : Real) ∧
    |localB q 2 - 1| < (1 / 16 : Real) ∧
    |localB q 3 - 1| < (1 / 16 : Real) ∧
    (localV1 q)^2 < (1 / 64 : Real) ∧
    (localV2 q)^2 < (1 / 64 : Real) ∧
    (localV3 q)^2 < (1 / 64 : Real) ∧
    (localW q)^2 < 1}

 set_option maxHeartbeats 1000000

theorem isOpen_tensorIdentityNeighborhood : IsOpen tensorIdentityNeighborhood := by
  unfold tensorIdentityNeighborhood localW localV1 localV2 localV3 localE localD localB mForm C
  simp only [Set.setOf_and]
  repeat' apply IsOpen.inter
  all_goals
    apply isOpen_lt
    all_goals fun_prop

 theorem standardFrame_mem_tensorIdentityNeighborhood :
    standardFrame ∈ tensorIdentityNeighborhood := by
  norm_num [tensorIdentityNeighborhood, localB, localD, localE,
    localV1, localV2, localV3, localW, standardFrame, mForm, C,
    coordinateVector_apply]

/-- Four-term Cauchy inequality, supplied with an explicit square certificate. -/
 theorem four_term_sq_le (a b c d : Real) :
    (a + b + c + d)^2 ≤ 4 * (a^2 + b^2 + c^2 + d^2) := by
  nlinarith only [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]

/-- A mixed term controlled by a small coefficient. -/
 theorem abs_mixed_term_le (w x y k : Real) (hk : 0 ≤ k) (hw : |w| ≤ k) :
    2 * |w * x * y| ≤ k * (x^2 + y^2) := by
  have hxy : 2 * (|x| * |y|) ≤ x^2 + y^2 := by
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have h1 := mul_le_mul_of_nonneg_right hw (mul_nonneg (abs_nonneg x) (abs_nonneg y))
  have h2 := mul_le_mul_of_nonneg_left hxy hk
  rw [abs_mul, abs_mul]
  nlinarith only [h1, h2]

/-- The residual of the last cubic, after eliminating the other three. -/
 theorem tensor_zero_cubic_residual (tau : Real) (q : Fin 4 -> E4)
    (hz : obstruction tau q = 0) :
    -2 * (q 1 0 * q 2 0 * localB q 3 +
          q 1 0 * q 3 0 * localB q 2 +
          q 2 0 * q 3 0 * localB q 1) + 3 * tau * localD q = 0 := by
  obtain ⟨h123, h023, h013, h012, _⟩ := (obstruction_eq_zero_iff tau q).mp hz
  have h := perturbed_cubic_residual_elimination tau q
  rw [h123, h023, h013, h012] at h
  unfold localB localD
  linear_combination -h

/-- The exact quartic residual after the same elimination. -/
 theorem tensor_zero_quartic_residual (tau : Real) (q : Fin 4 -> E4)
    (hz : obstruction tau q = 0) :
    -2 * (localB q 2 * localB q 3 * q 1 0 +
          localB q 1 * localB q 3 * q 2 0 +
          localB q 1 * localB q 2 * q 3 0) -
      q 0 0 * (q 1 0 * q 2 0 * localB q 3 +
        q 1 0 * q 3 0 * localB q 2 + q 2 0 * q 3 0 * localB q 1) +
      3 * (q 0 0)^2 * q 1 0 * q 2 0 * q 3 0 -
      3 * tau * localE q = 0 := by
  obtain ⟨_, h023, h013, h012, hB⟩ := (obstruction_eq_zero_iff tau q).mp hz
  have hId :
      3 * q 0 0 * B (q 0) (q 1) (q 2) (q 3) =
      3 * (localB q 1 + q 0 0 * q 1 0) * A tau (q 0) (q 2) (q 3) +
      3 * (localB q 2 + q 0 0 * q 2 0) * A tau (q 0) (q 1) (q 3) +
      3 * (localB q 3 + q 0 0 * q 3 0) * A tau (q 0) (q 1) (q 2) -
      2 * (localB q 2 * localB q 3 * q 1 0 +
          localB q 1 * localB q 3 * q 2 0 +
          localB q 1 * localB q 2 * q 3 0) -
      q 0 0 * (q 1 0 * q 2 0 * localB q 3 +
        q 1 0 * q 3 0 * localB q 2 + q 2 0 * q 3 0 * localB q 1) +
      3 * (q 0 0)^2 * q 1 0 * q 2 0 * q 3 0 -
      3 * tau * localE q := by
    unfold localE localB A A0 B nForm
    ring
  rw [hB, h023, h013, h012] at hId
  linear_combination -hId

/-- A zero of the tensor map has a controlled sum of its three small
first coordinates. This is an equality, not an asymptotic hypothesis. -/
 theorem tensor_zero_coordinate_sum (tau : Real) (q : Fin 4 -> E4)
    (hz : obstruction tau q = 0) :
    q 1 0 + q 2 0 + q 3 0 =
      localV1 q * q 1 0 + localV2 q * q 2 0 + localV3 q * q 3 0 -
        tau * localW q := by
  have hQ := tensor_zero_cubic_residual tau q hz
  have hB := tensor_zero_quartic_residual tau q hz
  unfold localV1 localV2 localV3 localW
  linear_combination (-1 / 2 : Real) * hB + (q 0 0 / 4) * hQ

/-- No perturbed zero can occur in the displayed neighborhood of the
identity. This stronger local statement does not require orthonormality. -/
 theorem obstruction_ne_zero_near_standard (tau : Real) (q : Fin 4 -> E4)
    (ht : 0 < tau) (ht' : tau < 1 / 4)
    (hq : q ∈ tensorIdentityNeighborhood) : obstruction tau q ≠ 0 := by
  intro hz
  rcases hq with ⟨hD, hb1, hb2, hb3, hv1, hv2, hv3, hw⟩
  let x := q 1 0
  let y := q 2 0
  let z := q 3 0
  let R := x^2 + y^2 + z^2
  let s := x + y + z
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs := tensor_zero_coordinate_sum tau q hz
  have hQ := tensor_zero_cubic_residual tau q hz
  have hm1 := abs_mixed_term_le (localB q 1 - 1) y z (1/16) (by norm_num) hb1.le
  have hm2 := abs_mixed_term_le (localB q 2 - 1) x z (1/16) (by norm_num) hb2.le
  have hm3 := abs_mixed_term_le (localB q 3 - 1) x y (1/16) (by norm_num) hb3.le
  have hErr : 2 * ((localB q 1 - 1) * y * z +
      (localB q 2 - 1) * x * z + (localB q 3 - 1) * x * y) ≤ R / 8 := by
    dsimp [R]
    linarith [le_abs_self ((localB q 1 - 1) * y * z),
      le_abs_self ((localB q 2 - 1) * x * z),
      le_abs_self ((localB q 3 - 1) * x * y)]
  have hV1 := mul_le_mul_of_nonneg_right hv1.le (sq_nonneg x)
  have hV2 := mul_le_mul_of_nonneg_right hv2.le (sq_nonneg y)
  have hV3 := mul_le_mul_of_nonneg_right hv3.le (sq_nonneg z)
  have hW := mul_le_mul_of_nonneg_right hw.le (sq_nonneg tau)
  have hC := four_term_sq_le (localV1 q * x) (localV2 q * y)
    (localV3 q * z) (-tau * localW q)
  have hsBound : s^2 ≤ R / 16 + 4 * tau^2 := by
    change s = localV1 q * x + localV2 q * y + localV3 q * z -
      tau * localW q at hs
    rw [hs]
    dsimp [R]
    nlinarith only [hC, hV1, hV2, hV3, hW]
  have hIdentity : R + 3 * tau * localD q = s^2 +
      2 * ((localB q 1 - 1) * y * z +
        (localB q 2 - 1) * x * z + (localB q 3 - 1) * x * y) := by
    dsimp [R, s, x, y, z]
    linear_combination hQ
  have hDt : (3 / 2 : Real) * tau < 3 * tau * localD q := by
    nlinarith [mul_pos ht (sub_pos.mpr hD)]
  have htSq : 4 * tau^2 < tau := by
    nlinarith [mul_pos ht (sub_pos.mpr ht')]
  linarith only [ht, hR, hErr, hsBound, hIdentity, hDt, htSq]

end SoberonConvexBody.Tensors
