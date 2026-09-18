import SoberonConvexBody.SphereMeasure
import SoberonConvexBody.TensorParity
import SoberonConvexBody.Walsh4

/-!
# Integrating finite parity extraction

All averages in this file are literal sums over the sixteen coordinate sign
changes. Their integral preservation follows from sphere measure preservation.
-/

noncomputable section
namespace SoberonConvexBody.SphereGeometry
open Set MeasureTheory
open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 0

instance sphereVolume_finite : IsFiniteMeasure sphereVolume :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure V).toSphere))

/-- The sign convention agrees with the closed positive halfspace in Cells. -/
def closedSign (x : Real) : Real := if 0 <= x then 1 else -1

@[simp] theorem abs_closedSign (x : Real) : abs (closedSign x) = 1 := by
  unfold closedSign
  split <;> norm_num

theorem closedSign_neg (x : Real) (hx : x ≠ 0) :
    closedSign (-x) = -closedSign x := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hp : 0 <= -x := le_of_lt (neg_pos.mpr h)
    have hn : ¬ 0 <= x := not_le_of_gt h
    simp [closedSign, hp, hn]
  · have hp : 0 <= x := le_of_lt h
    have hn : ¬ 0 <= -x := by linarith
    simp [closedSign, hp, hn]

theorem closedSign_mul_self (x : Real) : closedSign x * x = abs x := by
  by_cases hx : 0 <= x
  · simp [closedSign, hx, abs_of_nonneg hx]
  · simp [closedSign, hx, abs_of_neg (lt_of_not_ge hx)]

theorem closedSign_pos_mul (r x : Real) (hr : 0 < r) :
    closedSign (r * x) = closedSign x := by
  have hiff : 0 <= r * x <-> 0 <= x := by
    constructor
    · intro h
      by_contra hn
      have hx : x < 0 := lt_of_not_ge hn
      have := mul_neg_of_pos_of_neg hr hx
      linarith
    · exact mul_nonneg (le_of_lt hr)
  simp [closedSign, hiff]

/-- Product of the four ambient coordinate signs selected by I. -/
def coordinateCharacter (I : Finset (Fin 4)) (u : UnitSphere) : Real :=
  ∏ i ∈ I, closedSign ((u : V) i)

@[simp] theorem abs_coordinateCharacter (I : Finset (Fin 4)) (u : UnitSphere) :
    abs (coordinateCharacter I u) = 1 := by
  simp [coordinateCharacter, Finset.abs_prod]

theorem measurable_coordinateCharacter (I : Finset (Fin 4)) :
    Measurable (coordinateCharacter I) := by
  unfold coordinateCharacter closedSign
  apply Finset.measurable_prod
  intro i _
  apply Measurable.ite
  · exact measurableSet_le measurable_const (Continuous.measurable (by fun_prop))
  · exact measurable_const
  · exact measurable_const

theorem integrable_coordinateCharacter (I : Finset (Fin 4)) :
    Integrable (coordinateCharacter I) sphereVolume := by
  apply (integrable_const (1 : Real)).mono'
  · exact (measurable_coordinateCharacter I).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => by
      simp only [Real.norm_eq_abs, abs_coordinateCharacter, le_refl])

theorem integrable_continuous_sphere {f : UnitSphere -> Real}
    (hf : Continuous f) : Integrable f sphereVolume := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    (hf.continuousOn.integrableOn_compact (μ := sphereVolume) isCompact_univ)

/-- Bounded measurable signs can multiply any continuous sphere function. -/
theorem integrable_sign_mul_continuous
    (s f : UnitSphere -> Real) (hs : Measurable s)
    (habs : forall u, abs (s u) = 1) (hf : Continuous f) :
    Integrable (fun u => s u * f u) sphereVolume := by
  apply (integrable_continuous_sphere hf).norm.mono'
  · exact (hs.mul hf.measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => by
      simp only [Real.norm_eq_abs, abs_mul, habs, one_mul, le_refl])

def signFactor (b : Bool) : Real := if b then 1 else -1

abbrev SignQuad := Bool × Bool × Bool × Bool

def quadPattern (s : SignQuad) : Fin 4 -> Bool :=
  ![s.1, s.2.1, s.2.2.1, s.2.2.2]

/-- Diagonal orthogonal transformation associated with four Boolean signs. -/
def signChange (s : SignQuad) : V ≃ₗᵢ[Real] V where
  toFun x := WithLp.toLp 2 (fun i => signFactor (quadPattern s i) * x i)
  invFun x := WithLp.toLp 2 (fun i => signFactor (quadPattern s i) * x i)
  left_inv := by
    intro x
    ext i
    cases h : quadPattern s i <;> simp [PiLp.toLp_apply, signFactor, h]
  right_inv := by
    intro x
    ext i
    cases h : quadPattern s i <;> simp [PiLp.toLp_apply, signFactor, h]
  map_add' := by
    intro x y
    ext i
    simp [PiLp.toLp_apply, mul_add]
  map_smul' := by
    intro a x
    ext i
    simp [PiLp.toLp_apply, mul_left_comm]
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    cases h : quadPattern s i <;> simp [PiLp.toLp_apply, signFactor, h]

@[simp] theorem signChange_apply (s : SignQuad) (x : V) (i : Fin 4) :
    signChange s x i = signFactor (quadPattern s i) * x i := rfl

/-- Real character of the finite diagonal sign-change group. -/
def cubeCharacter (I : Finset (Fin 4)) (s : SignQuad) : Real :=
  ∏ i ∈ I, signFactor (quadPattern s i)

private def cubeCharacterZ (I : Finset (Fin 4)) (s : SignQuad) : Int :=
  ∏ i ∈ I, if quadPattern s i then 1 else -1

private theorem cubeCharacter_cast (I : Finset (Fin 4)) (s : SignQuad) :
    (cubeCharacterZ I s : Real) = cubeCharacter I s := by
  simp [cubeCharacterZ, cubeCharacter, signFactor]

set_option maxRecDepth 200000 in
private theorem sum_cubeCharacterZ_nonempty :
    forall I : Finset (Fin 4), I.Nonempty ->
      (∑ s : SignQuad, cubeCharacterZ I s) = 0 := by
  decide

theorem sum_cubeCharacter_nonempty (I : Finset (Fin 4)) (hI : I.Nonempty) :
    (∑ s : SignQuad, cubeCharacter I s) = 0 := by
  have h := sum_cubeCharacterZ_nonempty I hI
  have hh : ((∑ s : SignQuad, cubeCharacterZ I s) : Real) = 0 := by
    exact_mod_cast h
  simpa only [Int.cast_sum, cubeCharacter_cast] using hh

private theorem closedSign_signFactor (b : Bool) (x : Real) (hx : x ≠ 0) :
    closedSign (signFactor b * x) = signFactor b * closedSign x := by
  cases b
  · simpa [signFactor] using closedSign_neg x hx
  · simp [signFactor]

theorem coordinateCharacter_signChange
    (I : Finset (Fin 4)) (s : SignQuad) (u : UnitSphere)
    (hu : forall i : Fin 4, (u : V) i ≠ 0) :
    coordinateCharacter I (sphereMap (signChange s) u) =
      cubeCharacter I s * coordinateCharacter I u := by
  unfold coordinateCharacter cubeCharacter
  simp only [sphereMap_coe, signChange_apply]
  simp_rw [closedSign_signFactor _ _ (hu _)]
  rw [Finset.prod_mul_distrib]

/-- Literal finite average over the sixteen orthogonal sign changes. -/
def cubeAverage (f : UnitSphere -> Real) (u : UnitSphere) : Real :=
  (1 / 16 : Real) * ∑ s : SignQuad, f (sphereMap (signChange s) u)

theorem integral_cubeAverage (f : UnitSphere -> Real)
    (hf : Integrable f sphereVolume) :
    (∫ u, cubeAverage f u ∂ sphereVolume) =
      ∫ u, f u ∂ sphereVolume := by
  have hfs (s : SignQuad) :
      Integrable (fun u => f (sphereMap (signChange s) u)) sphereVolume :=
    (sphereMap_measurePreserving (signChange s)).integrable_comp_of_integrable hf
  unfold cubeAverage
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun s _ => hfs s)]
  simp_rw [integral_comp_sphereMap]
  norm_num [SignQuad] <;> ring

/-- The finite average of a nontrivial coordinate character vanishes. -/
theorem integral_coordinateCharacter_eq_zero
    (I : Finset (Fin 4)) (hI : I.Nonempty) :
    (∫ u, coordinateCharacter I u ∂ sphereVolume) = 0 := by
  have havg : cubeAverage (coordinateCharacter I) =ᵐ[sphereVolume] (fun _ => 0) := by
    filter_upwards [ae_all_coordinates_ne_zero] with u hu
    unfold cubeAverage
    simp_rw [coordinateCharacter_signChange I _ u hu]
    rw [← Finset.sum_mul, sum_cubeCharacter_nonempty I hI]
    ring
  rw [← integral_cubeAverage _ (integrable_coordinateCharacter I)]
  calc
    (∫ u, cubeAverage (coordinateCharacter I) u ∂ sphereVolume) =
        ∫ _u : UnitSphere, (0 : Real) ∂ sphereVolume := integral_congr_ae havg
    _ = 0 := by simp

/-- The character times the matching multilinear monomial is nonnegative. -/
theorem character_mul_coordinates (I : Finset (Fin 4)) (u : UnitSphere) :
    coordinateCharacter I u * (∏ i ∈ I, (u : V) i) =
      absCoordinateProduct I u := by
  unfold coordinateCharacter absCoordinateProduct
  rw [← Finset.prod_mul_distrib]
  simp_rw [closedSign_mul_self]

/-- Convert the finite cube sum into the sixteen-term real sign average. -/
theorem cube_average_to_signAverage4
    (F : Real -> Real -> Real -> Real -> Real) :
    (1 / 16 : Real) * (∑ s : SignQuad,
      F (signFactor s.1) (signFactor s.2.1)
        (signFactor s.2.2.1) (signFactor s.2.2.2)) =
      Tensors.signAverage4 F := by
  simp [SignQuad, Fintype.sum_prod_type, Fintype.sum_bool,
    signFactor, Tensors.signAverage4, Tensors.twoSigns]

/-- The polynomial written in the coordinate system with columns q. -/
def framePolynomial (tau : Real) (q : Fin 4 -> V) (u : UnitSphere) : Real :=
  Tensors.tensorPolynomial tau
    (Tensors.linearCombination4 q ((u : V) 0) ((u : V) 1)
      ((u : V) 2) ((u : V) 3))

theorem continuous_framePolynomial (tau : Real) (q : Fin 4 -> V) :
    Continuous (framePolynomial tau q) := by
  unfold framePolynomial Tensors.tensorPolynomial Tensors.linearCombination4
    Tensors.A Tensors.A0 Tensors.C Tensors.B Tensors.nForm Tensors.mForm
  fun_prop

theorem integrable_character_framePolynomial
    (tau : Real) (q : Fin 4 -> V) (I : Finset (Fin 4)) :
    Integrable (fun u => coordinateCharacter I u * framePolynomial tau q u)
      sphereVolume :=
  integrable_sign_mul_continuous _ _ (measurable_coordinateCharacter I)
    (abs_coordinateCharacter I) (continuous_framePolynomial tau q)

/-- Averaging the signed polynomial reduces to its weighted polynomial average. -/
theorem cubeAverage_character_framePolynomial
    (tau : Real) (q : Fin 4 -> V) (I : Finset (Fin 4)) (u : UnitSphere)
    (hu : forall i : Fin 4, (u : V) i ≠ 0) :
    cubeAverage (fun v => coordinateCharacter I v * framePolynomial tau q v) u =
      coordinateCharacter I u * ((1 / 16 : Real) *
        ∑ s : SignQuad, cubeCharacter I s *
          framePolynomial tau q (sphereMap (signChange s) u)) := by
  unfold cubeAverage
  simp_rw [coordinateCharacter_signChange I _ u hu]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Algebraic parity extraction inside the sphere average: 123. -/
private theorem cube_average_framePolynomial_high123
    (tau : Real) (q : Fin 4 -> V) (u : UnitSphere) :
    (1 / 16 : Real) * (∑ s : SignQuad, cubeCharacter {1,2,3} s *
      framePolynomial tau q (sphereMap (signChange s) u)) =
      6 * (((u : V) 1) * ((u : V) 2) * ((u : V) 3)) * Tensors.A tau (q 1) (q 2) (q 3) := by
  have h := Tensors.signAverage4_high123 tau q
    ((u : V) 0) ((u : V) 1) ((u : V) 2) ((u : V) 3)
  rw [← cube_average_to_signAverage4] at h
  simpa [cubeCharacter, framePolynomial, sphereMap_coe, signChange_apply,
    quadPattern, mul_assoc] using h

/-- The exact high-character integral, retaining its concrete sphere moment. -/
theorem integral_character_framePolynomial_high123
    (tau : Real) (q : Fin 4 -> V) :
    (∫ u, coordinateCharacter {1,2,3} u * framePolynomial tau q u
      ∂ sphereVolume) =
      6 * coordinateMoment {1,2,3} * Tensors.A tau (q 1) (q 2) (q 3) := by
  have havg : cubeAverage
      (fun u => coordinateCharacter {1,2,3} u * framePolynomial tau q u)
      =ᵐ[sphereVolume] (fun u => 6 * absCoordinateProduct {1,2,3} u * Tensors.A tau (q 1) (q 2) (q 3)) := by
    filter_upwards [ae_all_coordinates_ne_zero] with u hu
    rw [cubeAverage_character_framePolynomial tau q {1,2,3} u hu,
      cube_average_framePolynomial_high123]
    have hp : coordinateCharacter {1,2,3} u * (((u : V) 1) * ((u : V) 2) * ((u : V) 3)) =
        absCoordinateProduct {1,2,3} u := by
      simpa [mul_assoc] using character_mul_coordinates {1,2,3} u
    calc
      coordinateCharacter {1,2,3} u * (6 * (((u : V) 1) * ((u : V) 2) * ((u : V) 3)) * Tensors.A tau (q 1) (q 2) (q 3)) =
          6 * (coordinateCharacter {1,2,3} u * (((u : V) 1) * ((u : V) 2) * ((u : V) 3))) * Tensors.A tau (q 1) (q 2) (q 3) := by ring
      _ = 6 * absCoordinateProduct {1,2,3} u * Tensors.A tau (q 1) (q 2) (q 3) := by rw [hp]
  calc
    (∫ u, coordinateCharacter {1,2,3} u * framePolynomial tau q u
        ∂ sphereVolume) =
        ∫ u, cubeAverage
          (fun v => coordinateCharacter {1,2,3} v * framePolynomial tau q v) u
          ∂ sphereVolume :=
      (integral_cubeAverage _ (integrable_character_framePolynomial tau q {1,2,3})).symm
    _ = ∫ u, 6 * absCoordinateProduct {1,2,3} u * Tensors.A tau (q 1) (q 2) (q 3)
          ∂ sphereVolume := integral_congr_ae havg
    _ = 6 * coordinateMoment {1,2,3} * Tensors.A tau (q 1) (q 2) (q 3) := by
      rw [integral_mul_const, integral_const_mul]
      rfl

/-- Algebraic parity extraction inside the sphere average: 023. -/
private theorem cube_average_framePolynomial_high023
    (tau : Real) (q : Fin 4 -> V) (u : UnitSphere) :
    (1 / 16 : Real) * (∑ s : SignQuad, cubeCharacter {0,2,3} s *
      framePolynomial tau q (sphereMap (signChange s) u)) =
      6 * (((u : V) 0) * ((u : V) 2) * ((u : V) 3)) * Tensors.A tau (q 0) (q 2) (q 3) := by
  have h := Tensors.signAverage4_high023 tau q
    ((u : V) 0) ((u : V) 1) ((u : V) 2) ((u : V) 3)
  rw [← cube_average_to_signAverage4] at h
  simpa [cubeCharacter, framePolynomial, sphereMap_coe, signChange_apply,
    quadPattern, mul_assoc] using h

/-- The exact high-character integral, retaining its concrete sphere moment. -/
theorem integral_character_framePolynomial_high023
    (tau : Real) (q : Fin 4 -> V) :
    (∫ u, coordinateCharacter {0,2,3} u * framePolynomial tau q u
      ∂ sphereVolume) =
      6 * coordinateMoment {0,2,3} * Tensors.A tau (q 0) (q 2) (q 3) := by
  have havg : cubeAverage
      (fun u => coordinateCharacter {0,2,3} u * framePolynomial tau q u)
      =ᵐ[sphereVolume] (fun u => 6 * absCoordinateProduct {0,2,3} u * Tensors.A tau (q 0) (q 2) (q 3)) := by
    filter_upwards [ae_all_coordinates_ne_zero] with u hu
    rw [cubeAverage_character_framePolynomial tau q {0,2,3} u hu,
      cube_average_framePolynomial_high023]
    have hp : coordinateCharacter {0,2,3} u * (((u : V) 0) * ((u : V) 2) * ((u : V) 3)) =
        absCoordinateProduct {0,2,3} u := by
      simpa [mul_assoc] using character_mul_coordinates {0,2,3} u
    calc
      coordinateCharacter {0,2,3} u * (6 * (((u : V) 0) * ((u : V) 2) * ((u : V) 3)) * Tensors.A tau (q 0) (q 2) (q 3)) =
          6 * (coordinateCharacter {0,2,3} u * (((u : V) 0) * ((u : V) 2) * ((u : V) 3))) * Tensors.A tau (q 0) (q 2) (q 3) := by ring
      _ = 6 * absCoordinateProduct {0,2,3} u * Tensors.A tau (q 0) (q 2) (q 3) := by rw [hp]
  calc
    (∫ u, coordinateCharacter {0,2,3} u * framePolynomial tau q u
        ∂ sphereVolume) =
        ∫ u, cubeAverage
          (fun v => coordinateCharacter {0,2,3} v * framePolynomial tau q v) u
          ∂ sphereVolume :=
      (integral_cubeAverage _ (integrable_character_framePolynomial tau q {0,2,3})).symm
    _ = ∫ u, 6 * absCoordinateProduct {0,2,3} u * Tensors.A tau (q 0) (q 2) (q 3)
          ∂ sphereVolume := integral_congr_ae havg
    _ = 6 * coordinateMoment {0,2,3} * Tensors.A tau (q 0) (q 2) (q 3) := by
      rw [integral_mul_const, integral_const_mul]
      rfl

/-- Algebraic parity extraction inside the sphere average: 013. -/
private theorem cube_average_framePolynomial_high013
    (tau : Real) (q : Fin 4 -> V) (u : UnitSphere) :
    (1 / 16 : Real) * (∑ s : SignQuad, cubeCharacter {0,1,3} s *
      framePolynomial tau q (sphereMap (signChange s) u)) =
      6 * (((u : V) 0) * ((u : V) 1) * ((u : V) 3)) * Tensors.A tau (q 0) (q 1) (q 3) := by
  have h := Tensors.signAverage4_high013 tau q
    ((u : V) 0) ((u : V) 1) ((u : V) 2) ((u : V) 3)
  rw [← cube_average_to_signAverage4] at h
  simpa [cubeCharacter, framePolynomial, sphereMap_coe, signChange_apply,
    quadPattern, mul_assoc] using h

/-- The exact high-character integral, retaining its concrete sphere moment. -/
theorem integral_character_framePolynomial_high013
    (tau : Real) (q : Fin 4 -> V) :
    (∫ u, coordinateCharacter {0,1,3} u * framePolynomial tau q u
      ∂ sphereVolume) =
      6 * coordinateMoment {0,1,3} * Tensors.A tau (q 0) (q 1) (q 3) := by
  have havg : cubeAverage
      (fun u => coordinateCharacter {0,1,3} u * framePolynomial tau q u)
      =ᵐ[sphereVolume] (fun u => 6 * absCoordinateProduct {0,1,3} u * Tensors.A tau (q 0) (q 1) (q 3)) := by
    filter_upwards [ae_all_coordinates_ne_zero] with u hu
    rw [cubeAverage_character_framePolynomial tau q {0,1,3} u hu,
      cube_average_framePolynomial_high013]
    have hp : coordinateCharacter {0,1,3} u * (((u : V) 0) * ((u : V) 1) * ((u : V) 3)) =
        absCoordinateProduct {0,1,3} u := by
      simpa [mul_assoc] using character_mul_coordinates {0,1,3} u
    calc
      coordinateCharacter {0,1,3} u * (6 * (((u : V) 0) * ((u : V) 1) * ((u : V) 3)) * Tensors.A tau (q 0) (q 1) (q 3)) =
          6 * (coordinateCharacter {0,1,3} u * (((u : V) 0) * ((u : V) 1) * ((u : V) 3))) * Tensors.A tau (q 0) (q 1) (q 3) := by ring
      _ = 6 * absCoordinateProduct {0,1,3} u * Tensors.A tau (q 0) (q 1) (q 3) := by rw [hp]
  calc
    (∫ u, coordinateCharacter {0,1,3} u * framePolynomial tau q u
        ∂ sphereVolume) =
        ∫ u, cubeAverage
          (fun v => coordinateCharacter {0,1,3} v * framePolynomial tau q v) u
          ∂ sphereVolume :=
      (integral_cubeAverage _ (integrable_character_framePolynomial tau q {0,1,3})).symm
    _ = ∫ u, 6 * absCoordinateProduct {0,1,3} u * Tensors.A tau (q 0) (q 1) (q 3)
          ∂ sphereVolume := integral_congr_ae havg
    _ = 6 * coordinateMoment {0,1,3} * Tensors.A tau (q 0) (q 1) (q 3) := by
      rw [integral_mul_const, integral_const_mul]
      rfl

/-- Algebraic parity extraction inside the sphere average: 012. -/
private theorem cube_average_framePolynomial_high012
    (tau : Real) (q : Fin 4 -> V) (u : UnitSphere) :
    (1 / 16 : Real) * (∑ s : SignQuad, cubeCharacter {0,1,2} s *
      framePolynomial tau q (sphereMap (signChange s) u)) =
      6 * (((u : V) 0) * ((u : V) 1) * ((u : V) 2)) * Tensors.A tau (q 0) (q 1) (q 2) := by
  have h := Tensors.signAverage4_high012 tau q
    ((u : V) 0) ((u : V) 1) ((u : V) 2) ((u : V) 3)
  rw [← cube_average_to_signAverage4] at h
  simpa [cubeCharacter, framePolynomial, sphereMap_coe, signChange_apply,
    quadPattern, mul_assoc] using h

/-- The exact high-character integral, retaining its concrete sphere moment. -/
theorem integral_character_framePolynomial_high012
    (tau : Real) (q : Fin 4 -> V) :
    (∫ u, coordinateCharacter {0,1,2} u * framePolynomial tau q u
      ∂ sphereVolume) =
      6 * coordinateMoment {0,1,2} * Tensors.A tau (q 0) (q 1) (q 2) := by
  have havg : cubeAverage
      (fun u => coordinateCharacter {0,1,2} u * framePolynomial tau q u)
      =ᵐ[sphereVolume] (fun u => 6 * absCoordinateProduct {0,1,2} u * Tensors.A tau (q 0) (q 1) (q 2)) := by
    filter_upwards [ae_all_coordinates_ne_zero] with u hu
    rw [cubeAverage_character_framePolynomial tau q {0,1,2} u hu,
      cube_average_framePolynomial_high012]
    have hp : coordinateCharacter {0,1,2} u * (((u : V) 0) * ((u : V) 1) * ((u : V) 2)) =
        absCoordinateProduct {0,1,2} u := by
      simpa [mul_assoc] using character_mul_coordinates {0,1,2} u
    calc
      coordinateCharacter {0,1,2} u * (6 * (((u : V) 0) * ((u : V) 1) * ((u : V) 2)) * Tensors.A tau (q 0) (q 1) (q 2)) =
          6 * (coordinateCharacter {0,1,2} u * (((u : V) 0) * ((u : V) 1) * ((u : V) 2))) * Tensors.A tau (q 0) (q 1) (q 2) := by ring
      _ = 6 * absCoordinateProduct {0,1,2} u * Tensors.A tau (q 0) (q 1) (q 2) := by rw [hp]
  calc
    (∫ u, coordinateCharacter {0,1,2} u * framePolynomial tau q u
        ∂ sphereVolume) =
        ∫ u, cubeAverage
          (fun v => coordinateCharacter {0,1,2} v * framePolynomial tau q v) u
          ∂ sphereVolume :=
      (integral_cubeAverage _ (integrable_character_framePolynomial tau q {0,1,2})).symm
    _ = ∫ u, 6 * absCoordinateProduct {0,1,2} u * Tensors.A tau (q 0) (q 1) (q 2)
          ∂ sphereVolume := integral_congr_ae havg
    _ = 6 * coordinateMoment {0,1,2} * Tensors.A tau (q 0) (q 1) (q 2) := by
      rw [integral_mul_const, integral_const_mul]
      rfl

/-- Algebraic parity extraction inside the sphere average: 0123. -/
private theorem cube_average_framePolynomial_high0123
    (tau : Real) (q : Fin 4 -> V) (u : UnitSphere) :
    (1 / 16 : Real) * (∑ s : SignQuad, cubeCharacter {0,1,2,3} s *
      framePolynomial tau q (sphereMap (signChange s) u)) =
      24 * (((u : V) 0) * ((u : V) 1) * ((u : V) 2) * ((u : V) 3)) * Tensors.B (q 0) (q 1) (q 2) (q 3) := by
  have h := Tensors.signAverage4_high0123 tau q
    ((u : V) 0) ((u : V) 1) ((u : V) 2) ((u : V) 3)
  rw [← cube_average_to_signAverage4] at h
  simpa [cubeCharacter, framePolynomial, sphereMap_coe, signChange_apply,
    quadPattern, mul_assoc] using h

/-- The exact high-character integral, retaining its concrete sphere moment. -/
theorem integral_character_framePolynomial_high0123
    (tau : Real) (q : Fin 4 -> V) :
    (∫ u, coordinateCharacter {0,1,2,3} u * framePolynomial tau q u
      ∂ sphereVolume) =
      24 * coordinateMoment {0,1,2,3} * Tensors.B (q 0) (q 1) (q 2) (q 3) := by
  have havg : cubeAverage
      (fun u => coordinateCharacter {0,1,2,3} u * framePolynomial tau q u)
      =ᵐ[sphereVolume] (fun u => 24 * absCoordinateProduct {0,1,2,3} u * Tensors.B (q 0) (q 1) (q 2) (q 3)) := by
    filter_upwards [ae_all_coordinates_ne_zero] with u hu
    rw [cubeAverage_character_framePolynomial tau q {0,1,2,3} u hu,
      cube_average_framePolynomial_high0123]
    have hp : coordinateCharacter {0,1,2,3} u * (((u : V) 0) * ((u : V) 1) * ((u : V) 2) * ((u : V) 3)) =
        absCoordinateProduct {0,1,2,3} u := by
      simpa [mul_assoc] using character_mul_coordinates {0,1,2,3} u
    calc
      coordinateCharacter {0,1,2,3} u * (24 * (((u : V) 0) * ((u : V) 1) * ((u : V) 2) * ((u : V) 3)) * Tensors.B (q 0) (q 1) (q 2) (q 3)) =
          24 * (coordinateCharacter {0,1,2,3} u * (((u : V) 0) * ((u : V) 1) * ((u : V) 2) * ((u : V) 3))) * Tensors.B (q 0) (q 1) (q 2) (q 3) := by ring
      _ = 24 * absCoordinateProduct {0,1,2,3} u * Tensors.B (q 0) (q 1) (q 2) (q 3) := by rw [hp]
  calc
    (∫ u, coordinateCharacter {0,1,2,3} u * framePolynomial tau q u
        ∂ sphereVolume) =
        ∫ u, cubeAverage
          (fun v => coordinateCharacter {0,1,2,3} v * framePolynomial tau q v) u
          ∂ sphereVolume :=
      (integral_cubeAverage _ (integrable_character_framePolynomial tau q {0,1,2,3})).symm
    _ = ∫ u, 24 * absCoordinateProduct {0,1,2,3} u * Tensors.B (q 0) (q 1) (q 2) (q 3)
          ∂ sphereVolume := integral_congr_ae havg
    _ = 24 * coordinateMoment {0,1,2,3} * Tensors.B (q 0) (q 1) (q 2) (q 3) := by
      rw [integral_mul_const, integral_const_mul]
      rfl

end SoberonConvexBody.SphereGeometry
