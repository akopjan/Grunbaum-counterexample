import SoberonConvexBody.EllipsoidExpansion
import SoberonConvexBody.PolarGeneral

/-!
# Walsh integrals after straightening four affine hyperplanes

The affine map changes the body, not the signs. The transformed ball has the
explicit positive quadratic root developed in `EllipsoidExpansion`.
-/
noncomputable section
namespace SoberonConvexBody.Ellipsoid
open Set MeasureTheory
open scoped BigOperators
open Tensors SphereGeometry NearIdentity

def ambientCharacter (I : Walsh4.Index) (x : E4) : Real :=
  ∏ i ∈ I, closedSign (x i)

theorem measurable_ambientCharacter (I : Walsh4.Index) : Measurable (ambientCharacter I) := by
  unfold ambientCharacter closedSign
  apply Finset.measurable_prod
  intro i _
  apply Measurable.ite
  · exact measurableSet_le measurable_const (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 4 => ℝ) i).measurable
  · exact measurable_const
  · exact measurable_const

@[simp] theorem ambientCharacter_sphere (I : Walsh4.Index) (u : UnitSphere) :
    ambientCharacter I (u : E4) = coordinateCharacter I u := rfl

theorem ambientCharacter_angular (I : Walsh4.Index) (r : Real) (hr : 0 < r)
    (x : E4) : ambientCharacter I (r • x) = ambientCharacter I x := by
  unfold ambientCharacter
  apply Finset.prod_congr rfl
  intro i _
  exact closedSign_pos_mul r (x i) hr

theorem measurableSet_region (e : E4 ≃ₗ[Real] E4) (t : E4) :
    MeasurableSet (region e t) := by
  apply measurableSet_le
  · exact (e.symm.continuous.comp (continuous_id.add continuous_const)).norm.measurable
  · exact measurable_const

theorem integral_region_character (e : E4 ≃ₗ[Real] E4) (t : E4)
    (ht : coeffC e t < 1) (I : Walsh4.Index) :
    (∫ x in region e t, ambientCharacter I x) =
      (1/4 : Real) * ∫ u : UnitSphere, coordinateCharacter I u * radius e t u ^ 4
        ∂sphereVolume := by
  exact angular_setIntegral (region e t) (measurableSet_region e t)
    (fun u => radius e t u ^ 4) ((continuous_radius e t).pow 4).measurable
    (fun _ => pow_nonneg (radius_pos e t ht _).le _)
    (radial_mem_iff e t ht) (ambientCharacter I) (measurable_ambientCharacter I)
    (fun r hr x _ => ambientCharacter_angular I r hr x)

theorem map_affine_coordinates (e : E4 ≃ₗ[Real] E4) (t : E4) :
    Measure.map (fun x => e x-t) (volume : Measure E4) =
      ENNReal.ofReal (jacobian e) • volume := by
  have he : Measurable (fun x : E4 => e x) := e.continuous.measurable
  have hs : Measurable (fun x : E4 => x-t) := by fun_prop
  rw [show (fun x : E4 => e x-t) = (fun x : E4 => x-t) ∘ e by rfl,
    ← Measure.map_map hs he]
  change Measure.map (fun x => x - t) (Measure.map (e : E4 →ₗ[Real] E4) volume) = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (LinearEquiv.isUnit_det' e).ne_zero,
    Measure.map_smul _ hs.aemeasurable, map_sub_right_eq_self]
  rfl

/-- Exact affine straightening of the ball integral. -/
theorem walsh_ball_eq_sphere (c : HyperplaneCfg) (q : Fin 4 -> E4)
    (hq : IsONFrame q) (e : E4 ≃ₗ[Real] E4)
    (he : forall x, e x = normalMap hq c.normal x)
    (t : E4) (ht : forall i, t i = c.offset i) (hc : coeffC e t < 1)
    (I : Walsh4.Index) :
    walsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c I =
      (jacobian e / 4) *
        ∫ u : UnitSphere, coordinateCharacter I u * radius e t u ^ 4 ∂sphereVolume := by
  let B : Set E4 := Metric.closedBall 0 1
  let f : E4 -> Real := (region e t).indicator (ambientCharacter I)
  have hf : Measurable f := (measurable_ambientCharacter I).indicator (measurableSet_region e t)
  have hsign (x : E4) : Cells.signCharacter c I (hq.toIsometry x) =
      ambientCharacter I (e x-t) := by
    rw [Cells.signCharacter_eq_prod]
    unfold ambientCharacter
    apply Finset.prod_congr rfl
    intro i _
    simp only [PiLp.sub_apply,he,normalMap_apply,ht,closedSign,sub_nonneg]
  have hid (x : E4) : B.indicator (Cells.signCharacter c I) (hq.toIsometry x) = f (e x-t) := by
    have hm : hq.toIsometry x ∈ B ↔ e x-t ∈ region e t := by
      simp [B,Metric.mem_closedBall,dist_zero_right,region]
    by_cases hx : hq.toIsometry x ∈ B
    · rw [Set.indicator_of_mem hx]
      change _ = (region e t).indicator (ambientCharacter I) (e x-t)
      rw [Set.indicator_of_mem (hm.mp hx),hsign]
    · rw [Set.indicator_of_notMem hx]
      change _ = (region e t).indicator (ambientCharacter I) (e x-t)
      rw [Set.indicator_of_notMem (mt hm.mpr hx)]
  have hrot := hq.toIsometry.measurePreserving.integral_comp
    hq.toIsometry.toHomeomorph.measurableEmbedding (B.indicator (Cells.signCharacter c I))
  calc
    walsh (volume.restrict B) c I = ∫ x, B.indicator (Cells.signCharacter c I) x := by
      rw [integral_indicator measurableSet_closedBall]
      rfl
    _ = ∫ x, B.indicator (Cells.signCharacter c I) (hq.toIsometry x) := hrot.symm
    _ = ∫ x, f (e x-t) := by apply integral_congr_ae; exact Filter.Eventually.of_forall hid
    _ = ∫ y, f y ∂Measure.map (fun x => e x-t) volume :=
      (integral_map_of_stronglyMeasurable (e.continuous.sub continuous_const).measurable hf.stronglyMeasurable).symm
    _ = jacobian e * ∫ y, f y := by
      rw [map_affine_coordinates,integral_smul_measure]
      simp [ENNReal.toReal_ofReal (jacobian_pos e).le,smul_eq_mul]
    _ = jacobian e * ∫ y in region e t, ambientCharacter I y := by
      rw [show f = (region e t).indicator (ambientCharacter I) by rfl,
        integral_indicator (measurableSet_region e t)]
    _ = (jacobian e/4) * ∫ u : UnitSphere,
        coordinateCharacter I u * radius e t u ^ 4 ∂sphereVolume := by
      rw [integral_region_character e t hc I]
      ring

/-- Matrix of the error relative to the standard orthonormal basis. -/
def errorMatrix (e : E4 ≃ₗ[Real] E4) (i j : Fin 4) : Real :=
  e (coordinateVector j) i - if i=j then 1 else 0

theorem vector_decomposition (x : E4) :
    x = ∑ j : Fin 4, x j • coordinateVector j := by
  ext i
  fin_cases i <;> simp [coordinateVector_apply, Fin.sum_univ_succ]

theorem errorMatrix_mul (e : E4 ≃ₗ[Real] E4) (x : E4) (i : Fin 4) :
    (e x-x) i = ∑ j : Fin 4, errorMatrix e i j*x j := by
  have hex : e x = ∑ j : Fin 4, x j • e (coordinateVector j) := by
    conv_lhs => rw [vector_decomposition x]
    simp only [map_sum, map_smul]
  rw [hex]
  have h_left : (∑ j : Fin 4, x j • e (coordinateVector j) - x) i =
      (∑ j : Fin 4, x j • e (coordinateVector j)) i - x i := rfl
  rw [h_left]
  fin_cases i <;> (
    simp [errorMatrix, Fin.sum_univ_succ, coordinateVector_apply]
    ring
  )

theorem inner_error_polynomial (e : E4 ≃ₗ[Real] E4) (x : E4) :
    inner Real x (e x-x) =
      ∑ i : Fin 4, ∑ j : Fin 4, errorMatrix e i j * (x i*x j) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct,errorMatrix_mul,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def firstPolynomial (e : E4 ≃ₗ[Real] E4) (t : E4) : UnitSphere -> Real :=
  quadraticSphere 1 (fun i => -4*t i) (fun i j => 4*errorMatrix e i j)

theorem firstPolynomial_eq (e : E4 ≃ₗ[Real] E4) (t : E4) (u : UnitSphere) :
    firstPolynomial e t u =
      1+4*inner Real (u : E4) (e (u : E4)-(u : E4))-4*inner Real (u : E4) t := by
  rw [inner_error_polynomial,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [firstPolynomial,quadraticSphere,star_trivial,dotProduct,Fin.sum_univ_succ]
  ring

/-- Uniform bound on the difference of the sphere integrals. -/
theorem integral_radius_remainder (e : E4 ≃ₗ[Real] E4) (t : E4) (beta : Real)
    (hb0 : 0 ≤ beta) (hb : beta ≤ 1/800)
    (he : forall x, norm (e x-x) ≤ beta*norm x) (ht : norm t ≤ beta)
    (I : Walsh4.Index) :
    |(∫ u : UnitSphere, coordinateCharacter I u * radius e t u ^ 4 ∂sphereVolume)-
      (∫ u : UnitSphere, coordinateCharacter I u * firstPolynomial e t u ∂sphereVolume)|
      ≤ sphereVolume.real Set.univ * (13000*beta^2) := by
  have hi := integrable_sign_mul_continuous (coordinateCharacter I)
    (fun u => radius e t u ^ 4) (measurable_coordinateCharacter I)
    (abs_coordinateCharacter I) ((continuous_radius e t).pow 4)
  have hj := integrable_sign_mul_continuous (coordinateCharacter I)
    (firstPolynomial e t) (measurable_coordinateCharacter I)
    (abs_coordinateCharacter I) (continuous_quadraticSphere 1 (fun i => -4*t i) (fun i j => 4*errorMatrix e i j))
  rw [← integral_sub hi hj]
  apply abs_integral_le_integral_abs.trans
  calc
    (∫ u : UnitSphere,
      |coordinateCharacter I u * radius e t u ^ 4-coordinateCharacter I u * firstPolynomial e t u|
        ∂sphereVolume)
      ≤ ∫ _u : UnitSphere, (13000*beta^2 : Real) ∂sphereVolume := by
        apply integral_mono (hi.sub hj).abs (integrable_const _)
        intro u
        change |coordinateCharacter I u * radius e t u ^ 4 - coordinateCharacter I u * firstPolynomial e t u| ≤ _
        rw [← mul_sub,abs_mul,abs_coordinateCharacter,one_mul,firstPolynomial_eq]
        exact radius_fourth_expansion e t beta hb0 hb he ht u
    _ = sphereVolume.real Set.univ * (13000*beta^2) := by simp [integral_const,smul_eq_mul]

end SoberonConvexBody.Ellipsoid
