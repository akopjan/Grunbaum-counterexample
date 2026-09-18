import SoberonConvexBody.FrameBasics
import SoberonConvexBody.SphereParity
import SoberonConvexBody.Cells

/-!
# Orthonormal-frame coordinates

Convert the unbundled frame used by the original project into a bundled
linear isometric equivalence. This avoids postulating any rotation lemma.
-/

noncomputable section
namespace SoberonConvexBody
open Set MeasureTheory
open scoped BigOperators


namespace Cells

/-- Product formula with the project's original boundary convention. -/
theorem signCharacter_eq_prod (c : HyperplaneCfg) (I : Walsh4.Index) (x : E4) :
    signCharacter c I x =
      ∏ i ∈ I, if c.offset i <= inner Real x (c.normal i)
        then (1 : Real) else -1 := by
  unfold signCharacter Walsh4.char Walsh4.charZ
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : c.offset i <= inner Real x (c.normal i)
  · simp [pattern, not_lt.mpr h, h]
  · have hh : inner Real x (c.normal i) < c.offset i := lt_of_not_ge h
    simp [pattern, hh, h]

theorem measurable_signCharacter (c : HyperplaneCfg) (I : Walsh4.Index) :
    Measurable (signCharacter c I) := by
  have heq : signCharacter c I = fun x =>
      ∏ i ∈ I, if c.offset i <= inner Real x (c.normal i)
        then (1 : Real) else -1 := funext (signCharacter_eq_prod c I)
  rw [heq]
  apply Finset.measurable_prod
  intro i _
  apply Measurable.ite
  · exact measurableSet_le measurable_const (by fun_prop)
  · exact measurable_const
  · exact measurable_const

/-- Positive dilations preserve the signs of centered hyperplanes. -/
theorem centered_signCharacter_pos_smul (q : Fin 4 -> E4)
    (I : Walsh4.Index) (r : Real) (hr : 0 < r) (x : E4) :
    signCharacter ⟨ q, fun _ => 0 ⟩ I (r • x) =
      signCharacter ⟨ q, fun _ => 0 ⟩ I x := by
  simp only [signCharacter_eq_prod, real_inner_smul_left]
  apply Finset.prod_congr rfl
  intro i _
  change SphereGeometry.closedSign (r * inner Real x (q i)) =
    SphereGeometry.closedSign (inner Real x (q i))
  exact SphereGeometry.closedSign_pos_mul r _ hr

theorem signCharacter_on_frame (q : Fin 4 -> E4) (hq : Tensors.IsONFrame q)
    (I : Walsh4.Index) (u : SphereGeometry.UnitSphere) :
    signCharacter ⟨ q, fun _ => 0 ⟩ I
        (hq.toIsometry (u : E4)) = SphereGeometry.coordinateCharacter I u := by
  simp only [signCharacter_eq_prod, Tensors.IsONFrame.inner_toIsometry]
  rfl

end Cells

namespace SphereGeometry

/-- The sphere integral of a nonempty centered character vanishes. -/
theorem integral_centered_character (q : Fin 4 -> V) (hq : Tensors.IsONFrame q)
    (I : Walsh4.Index) (hI : I.Nonempty) :
    (∫ u : UnitSphere, Cells.signCharacter ⟨ q, fun _ => 0 ⟩ I (u : V)
      ∂ sphereVolume) = 0 := by
  rw [← integral_comp_sphereMap hq.toIsometry]
  simp_rw [sphereMap_coe, Cells.signCharacter_on_frame]
  exact integral_coordinateCharacter_eq_zero I hI

/-- Integrability for the product before rotation. -/
theorem integrable_centered_character_mul_polynomial
    (tau : Real) (q : Fin 4 -> V) (I : Walsh4.Index) :
    Integrable (fun u : UnitSphere =>
      Cells.signCharacter ⟨ q, fun _ => 0 ⟩ I (u : V) *
        Tensors.tensorPolynomial tau (u : V)) sphereVolume := by
  apply integrable_sign_mul_continuous
  · exact (Cells.measurable_signCharacter _ I).comp measurable_subtype_coe
  · intro u
    exact Walsh4.abs_char I (Cells.pattern ⟨ q, fun _ => 0 ⟩ (u : V))
  · unfold Tensors.tensorPolynomial Tensors.A Tensors.A0 Tensors.C
      Tensors.B Tensors.nForm Tensors.mForm
    fun_prop

/-- Exact rotated sphere integral for high character 123. -/
theorem integral_centered_polynomial_high123
    (tau : Real) (q : Fin 4 -> V) (hq : Tensors.IsONFrame q) :
    (∫ u : UnitSphere,
      Cells.signCharacter ⟨ q, fun _ => 0 ⟩ {1,2,3} (u : V) *
        Tensors.tensorPolynomial tau (u : V) ∂ sphereVolume) =
      6 * coordinateMoment {1,2,3} * Tensors.A tau (q 1) (q 2) (q 3) := by
  rw [← integral_comp_sphereMap hq.toIsometry]
  simp_rw [sphereMap_coe, Cells.signCharacter_on_frame,
    Tensors.IsONFrame.toIsometry_apply]
  exact integral_character_framePolynomial_high123 tau q

/-- Exact rotated sphere integral for high character 023. -/
theorem integral_centered_polynomial_high023
    (tau : Real) (q : Fin 4 -> V) (hq : Tensors.IsONFrame q) :
    (∫ u : UnitSphere,
      Cells.signCharacter ⟨ q, fun _ => 0 ⟩ {0,2,3} (u : V) *
        Tensors.tensorPolynomial tau (u : V) ∂ sphereVolume) =
      6 * coordinateMoment {0,2,3} * Tensors.A tau (q 0) (q 2) (q 3) := by
  rw [← integral_comp_sphereMap hq.toIsometry]
  simp_rw [sphereMap_coe, Cells.signCharacter_on_frame,
    Tensors.IsONFrame.toIsometry_apply]
  exact integral_character_framePolynomial_high023 tau q

/-- Exact rotated sphere integral for high character 013. -/
theorem integral_centered_polynomial_high013
    (tau : Real) (q : Fin 4 -> V) (hq : Tensors.IsONFrame q) :
    (∫ u : UnitSphere,
      Cells.signCharacter ⟨ q, fun _ => 0 ⟩ {0,1,3} (u : V) *
        Tensors.tensorPolynomial tau (u : V) ∂ sphereVolume) =
      6 * coordinateMoment {0,1,3} * Tensors.A tau (q 0) (q 1) (q 3) := by
  rw [← integral_comp_sphereMap hq.toIsometry]
  simp_rw [sphereMap_coe, Cells.signCharacter_on_frame,
    Tensors.IsONFrame.toIsometry_apply]
  exact integral_character_framePolynomial_high013 tau q

/-- Exact rotated sphere integral for high character 012. -/
theorem integral_centered_polynomial_high012
    (tau : Real) (q : Fin 4 -> V) (hq : Tensors.IsONFrame q) :
    (∫ u : UnitSphere,
      Cells.signCharacter ⟨ q, fun _ => 0 ⟩ {0,1,2} (u : V) *
        Tensors.tensorPolynomial tau (u : V) ∂ sphereVolume) =
      6 * coordinateMoment {0,1,2} * Tensors.A tau (q 0) (q 1) (q 2) := by
  rw [← integral_comp_sphereMap hq.toIsometry]
  simp_rw [sphereMap_coe, Cells.signCharacter_on_frame,
    Tensors.IsONFrame.toIsometry_apply]
  exact integral_character_framePolynomial_high012 tau q

/-- Exact rotated sphere integral for high character 0123. -/
theorem integral_centered_polynomial_high0123
    (tau : Real) (q : Fin 4 -> V) (hq : Tensors.IsONFrame q) :
    (∫ u : UnitSphere,
      Cells.signCharacter ⟨ q, fun _ => 0 ⟩ {0,1,2,3} (u : V) *
        Tensors.tensorPolynomial tau (u : V) ∂ sphereVolume) =
      24 * coordinateMoment {0,1,2,3} * Tensors.B (q 0) (q 1) (q 2) (q 3) := by
  rw [← integral_comp_sphereMap hq.toIsometry]
  simp_rw [sphereMap_coe, Cells.signCharacter_on_frame,
    Tensors.IsONFrame.toIsometry_apply]
  exact integral_character_framePolynomial_high0123 tau q

end SphereGeometry
end SoberonConvexBody
