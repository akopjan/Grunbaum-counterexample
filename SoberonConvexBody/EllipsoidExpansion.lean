import Mathlib
import SoberonConvexBody.NearIdentity
import SoberonConvexBody.EllipsoidScalar
import SoberonConvexBody.SphereQuadratic

/-!
# A uniform quadratic radial expansion for an affine image of the unit ball

All constants are deliberately coarse. No differentiability of a sign
character, and no regularity hypothesis about cell volumes, is used.
-/
noncomputable section
namespace SoberonConvexBody.Ellipsoid
open scoped BigOperators
open Tensors SphereGeometry NearIdentity

private theorem abs_sub (a b : Real) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  have h := abs_add_le a (-b)
  rwa [abs_neg] at h

theorem _root_.LinearEquiv.continuous (e : E4 ≃ₗ[Real] E4) : Continuous e :=
  e.toLinearMap.continuous_of_finiteDimensional

def coeffA (e : E4 ≃ₗ[Real] E4) (u : UnitSphere) : Real := norm (e.symm (u : E4))^2

def coeffB (e : E4 ≃ₗ[Real] E4) (t : E4) (u : UnitSphere) : Real :=
  inner Real (e.symm (u : E4)) (e.symm t)

def coeffC (e : E4 ≃ₗ[Real] E4) (t : E4) : Real := norm (e.symm t)^2

def radius (e : E4 ≃ₗ[Real] E4) (t : E4) (u : UnitSphere) : Real :=
  EllipsoidScalar.positiveRoot (coeffA e u) (coeffB e t u) (coeffC e t)

def region (e : E4 ≃ₗ[Real] E4) (t : E4) : Set E4 :=
  {y | norm (e.symm (y+t)) ≤ 1}

theorem norm_add_sq (x y : E4) :
    norm (x+y)^2 = norm x^2 + 2*inner Real x y + norm y^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_comm y x]
  ring

theorem coeffA_pos (e : E4 ≃ₗ[Real] E4) (u : UnitSphere) : 0 < coeffA e u := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  have hzu : (u : E4) = 0 := by
    have h := congrArg e hz
    simpa using h
  have hn := SphereGeometry.norm_coe u
  rw [hzu, norm_zero] at hn
  norm_num at hn

theorem continuous_coeffA (e : E4 ≃ₗ[Real] E4) : Continuous (coeffA e) :=
  (e.symm.continuous.comp continuous_subtype_val).norm.pow 2

theorem continuous_coeffB (e : E4 ≃ₗ[Real] E4) (t : E4) : Continuous (coeffB e t) :=
  (e.symm.continuous.comp continuous_subtype_val).inner continuous_const

theorem continuous_radius (e : E4 ≃ₗ[Real] E4) (t : E4) : Continuous (radius e t) := by
  unfold radius EllipsoidScalar.positiveRoot
  refine Continuous.div ?_ (continuous_coeffA e) (fun u => (coeffA_pos e u).ne')
  exact (((continuous_coeffB e t).pow 2).add ((continuous_coeffA e).mul continuous_const)).sqrt.sub (continuous_coeffB e t)

theorem radius_pos (e : E4 ≃ₗ[Real] E4) (t : E4)
    (ht : coeffC e t < 1) (u : UnitSphere) : 0 < radius e t u :=
  EllipsoidScalar.positiveRoot_pos _ _ _ (coeffA_pos e u) ht

theorem radial_equation (e : E4 ≃ₗ[Real] E4) (t : E4) (u : UnitSphere) (r : Real) :
    norm (e.symm (r • (u : E4)+t))^2 =
      coeffA e u*r^2+2*coeffB e t u*r+coeffC e t := by
  rw [map_add, map_smul, norm_add_sq, norm_smul, Real.norm_eq_abs,
    real_inner_smul_left]
  dsimp [coeffA,coeffB,coeffC]
  rw [mul_pow, sq_abs]
  ring

theorem radial_mem_iff (e : E4 ≃ₗ[Real] E4) (t : E4)
    (ht : coeffC e t < 1) (u : UnitSphere) (r : Set.Ioi (0 : Real)) :
    (r : Real) • (u : E4) ∈ region e t ↔ (r : Real)^4 ≤ radius e t u ^ 4 := by
  have hr : 0 ≤ (r : Real) := r.property.le
  have hp := (radius_pos e t ht u).le
  have hpow := pow_le_pow_iff_left₀ hr hp (by norm_num : (4 : Nat) ≠ 0)
  rw [hpow]
  change norm (e.symm ((r : Real) • (u : E4)+t)) ≤ 1 ↔ _
  have hsq : norm (e.symm ((r : Real) • (u : E4)+t)) ≤ 1 ↔
      norm (e.symm ((r : Real) • (u : E4)+t))^2 ≤ 1 := by
    constructor <;> intro h <;> nlinarith [norm_nonneg (e.symm ((r : Real) • (u : E4)+t))]
  rw [hsq,radial_equation]
  exact EllipsoidScalar.quadratic_le_iff _ _ _ _ (coeffA_pos e u) ht hr

theorem coefficient_bounds (e : E4 ≃ₗ[Real] E4) (t : E4) (beta : Real)
    (hb0 : 0 ≤ beta) (hb : beta ≤ 1/800)
    (he : forall x, norm (e x-x) ≤ beta*norm x) (ht : norm t ≤ beta)
    (u : UnitSphere) :
    |coeffA e u-1| ≤ 8*beta ∧ |coeffB e t u| ≤ 8*beta ∧
      0 ≤ coeffC e t ∧ coeffC e t ≤ (8*beta)^2 := by
  have hbhalf : beta ≤ 1/2 := by linarith
  have hu : norm (u : E4) = 1 := SphereGeometry.norm_coe u
  have hv := inverse_error e beta hb0 hbhalf he (u : E4)
  rw [hu,mul_one] at hv
  have hbu := inverse_norm_le e beta hbhalf he (u : E4)
  rw [hu,mul_one] at hbu
  have hbt : norm (e.symm t) ≤ 2*beta :=
    (inverse_norm_le e beta hbhalf he t).trans (by linarith)
  have hid : coeffA e u - 1 =
      2*inner Real (u : E4) (e.symm (u : E4)-(u : E4))+
        norm (e.symm (u : E4)-(u : E4))^2 := by
    have h := norm_add_sq (u : E4) (e.symm (u : E4)-(u : E4))
    rw [add_sub_cancel,hu] at h
    dsimp [coeffA]
    nlinarith
  have hi : |inner Real (u : E4) (e.symm (u : E4)-(u : E4))| ≤ 2*beta := by
    have h := abs_real_inner_le_norm (u : E4) (e.symm (u : E4)-(u : E4))
    rw [hu,one_mul] at h
    exact h.trans hv
  have hv2 : norm (e.symm (u : E4)-(u : E4))^2 ≤ 4*beta^2 := by
    nlinarith [norm_nonneg (e.symm (u : E4)-(u : E4))]
  have hc2 : coeffC e t ≤ 4*beta^2 := by
    dsimp [coeffC]
    nlinarith [norm_nonneg (e.symm t)]
  refine ⟨?_,?_,sq_nonneg _,?_⟩
  · rw [hid]
    calc
      |2*inner Real (u : E4) (e.symm (u : E4)-(u : E4))+
          norm (e.symm (u : E4)-(u : E4))^2|
          ≤ |2*inner Real (u : E4) (e.symm (u : E4)-(u : E4))|+
            |norm (e.symm (u : E4)-(u : E4))^2| := abs_add_le _ _
      _ ≤ 8*beta := by
        simp only [abs_mul, abs_sq, abs_of_pos (by norm_num : (0 : Real) < 2)]
        nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb)]
  · unfold coeffB
    have h := abs_real_inner_le_norm (e.symm (u : E4)) (e.symm t)
    have hp := mul_le_mul hbu hbt (norm_nonneg _) (by norm_num : (0 : Real) ≤ 2)
    nlinarith
  · nlinarith [sq_nonneg beta]

theorem coefficient_linear_errors (e : E4 ≃ₗ[Real] E4) (t : E4) (beta : Real)
    (hb0 : 0 ≤ beta) (hb : beta ≤ 1/800)
    (he : forall x, norm (e x-x) ≤ beta*norm x) (ht : norm t ≤ beta)
    (u : UnitSphere) :
    |coeffA e u-1+2*inner Real (u : E4) (e (u : E4)-(u : E4))| ≤ 8*beta^2 ∧
    |coeffB e t u-inner Real (u : E4) t| ≤ 6*beta^2 := by
  have hbhalf : beta ≤ 1/2 := by linarith
  have hu : norm (u : E4) = 1 := SphereGeometry.norm_coe u
  have hv := inverse_error e beta hb0 hbhalf he (u : E4)
  rw [hu,mul_one] at hv
  have h2 := inverse_second_error e beta hb0 hbhalf he (u : E4)
  rw [hu,mul_one] at h2
  have hbt : norm (e.symm t) ≤ 2*beta :=
    (inverse_norm_le e beta hbhalf he t).trans (by linarith)
  have hbt' : norm (e.symm t-t) ≤ 2*beta^2 := by
    have hh := inverse_error e beta hb0 hbhalf he t
    have hm := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2*beta)
    nlinarith
  constructor
  · have hid : coeffA e u-1+2*inner Real (u : E4) (e (u : E4)-(u : E4)) =
        2*inner Real (u : E4) (e.symm (u : E4)-(u : E4)+(e (u : E4)-(u : E4)))+
          norm (e.symm (u : E4)-(u : E4))^2 := by
      have hn := norm_add_sq (u : E4) (e.symm (u : E4)-(u : E4))
      rw [add_sub_cancel,hu] at hn
      simp only [inner_add_right]
      dsimp [coeffA]
      nlinarith
    have hi := abs_real_inner_le_norm (u : E4)
      (e.symm (u : E4)-(u : E4)+(e (u : E4)-(u : E4)))
    rw [hu,one_mul] at hi
    have hv2 : norm (e.symm (u : E4)-(u : E4))^2 ≤ 4*beta^2 := by
      nlinarith [norm_nonneg (e.symm (u : E4)-(u : E4))]
    rw [hid]
    calc
      _ ≤ |2*inner Real (u : E4)
          (e.symm (u : E4)-(u : E4)+(e (u : E4)-(u : E4)))|+
          |norm (e.symm (u : E4)-(u : E4))^2| := abs_add_le _ _
      _ ≤ 8*beta^2 := by
        simp only [abs_mul, abs_sq, abs_of_pos (by norm_num : (0 : Real) < 2)]
        nlinarith
  · have hid : coeffB e t u-inner Real (u : E4) t =
        inner Real (e.symm (u : E4)-(u : E4)) (e.symm t)+
        inner Real (u : E4) (e.symm t-t) := by
      simp [coeffB,inner_sub_left,inner_sub_right]
    rw [hid]
    have h1 := abs_real_inner_le_norm (e.symm (u : E4)-(u : E4)) (e.symm t)
    have hp := mul_le_mul hv hbt (norm_nonneg _) (by positivity : 0 ≤ 2*beta)
    have hi := abs_real_inner_le_norm (u : E4) (e.symm t-t)
    rw [hu,one_mul] at hi
    calc
      _ ≤ |inner Real (e.symm (u : E4)-(u : E4)) (e.symm t)|+
          |inner Real (u : E4) (e.symm t-t)| := abs_add_le _ _
      _ ≤ 6*beta^2 := by nlinarith

/-- The complete pointwise expansion, uniform over the sphere. -/
theorem radius_fourth_expansion (e : E4 ≃ₗ[Real] E4) (t : E4) (beta : Real)
    (hb0 : 0 ≤ beta) (hb : beta ≤ 1/800)
    (he : forall x, norm (e x-x) ≤ beta*norm x) (ht : norm t ≤ beta)
    (u : UnitSphere) :
    |radius e t u ^ 4 -
      (1+4*inner Real (u : E4) (e (u : E4)-(u : E4))-4*inner Real (u : E4) t)|
      ≤ 13000*beta^2 := by
  obtain ⟨ha,hb',hc0,hc⟩ := coefficient_bounds e t beta hb0 hb he ht u
  have hroot := EllipsoidScalar.fourth_power_expansion
    (coeffA e u) (coeffB e t u) (coeffC e t) (8*beta) (by positivity)
    (by linarith) ha hb' hc0 hc
  change |radius e t u ^ 4-(3-2*coeffA e u-4*coeffB e t u)| ≤ 200*(8*beta)^2 at hroot
  obtain ⟨h1,h2⟩ := coefficient_linear_errors e t beta hb0 hb he ht u
  have hid : radius e t u ^ 4 -
      (1+4*inner Real (u : E4) (e (u : E4)-(u : E4))-4*inner Real (u : E4) t) =
      (radius e t u ^ 4-(3-2*coeffA e u-4*coeffB e t u))-
        2*(coeffA e u-1+2*inner Real (u : E4) (e (u : E4)-(u : E4)))-
        4*(coeffB e t u-inner Real (u : E4) t) := by ring
  rw [hid]
  calc
    _ ≤ |radius e t u ^ 4-(3-2*coeffA e u-4*coeffB e t u)|+
        |2*(coeffA e u-1+2*inner Real (u : E4) (e (u : E4)-(u : E4)))|+
        |4*(coeffB e t u-inner Real (u : E4) t)| := by
      have h1 := abs_sub (radius e t u ^ 4 - (3 - 2 * coeffA e u - 4 * coeffB e t u) -
        2 * (coeffA e u - 1 + 2 * inner Real (u : E4) (e (u : E4) - (u : E4))))
        (4 * (coeffB e t u - inner Real (u : E4) t))
      have h2 := abs_sub (radius e t u ^ 4 - (3 - 2 * coeffA e u - 4 * coeffB e t u))
        (2 * (coeffA e u - 1 + 2 * inner Real (u : E4) (e (u : E4) - (u : E4))))
      linarith
    _ ≤ 13000*beta^2 := by
      simp only [abs_mul,show |(2 : Real)|=2 by norm_num,show |(4 : Real)|=4 by norm_num]
      nlinarith [sq_nonneg beta]

end SoberonConvexBody.Ellipsoid
