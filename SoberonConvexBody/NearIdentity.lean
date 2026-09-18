import SoberonConvexBody.FrameBasics

/-!
# Elementary inverse estimates near the identity

The inverse is constructed by finite-dimensional injectivity. The second-order
estimate follows from the exact resolvent identity, not a matrix power series.
-/
noncomputable section
namespace SoberonConvexBody
open scoped BigOperators
open Tensors

namespace NearIdentity

theorem norm_four_le (x : E4) (a : Real) (ha : 0 ≤ a)
    (h : forall i : Fin 4, |x i| ≤ a) : norm x ≤ 4*a := by
  have hs : forall i : Fin 4, (x i)^2 ≤ a^2 := by
    intro i
    have hi := abs_le.mp (h i)
    nlinarith [sq_abs (x i)]
  have hsum : (∑ i : Fin 4, (x i)^2) ≤ 4*a^2 := by
    calc
      (∑ i : Fin 4, (x i)^2) ≤ ∑ _i : Fin 4, a^2 :=
        Finset.sum_le_sum (fun i _ => hs i)
      _ = 4*a^2 := by simp
  have hn : (norm x)^2 ≤ (4*a)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    nlinarith [sq_nonneg a]
  nlinarith [norm_nonneg x]

def normalMap {q : Fin 4 -> E4} (hq : IsONFrame q) (n : Fin 4 -> E4) :
    E4 →ₗ[Real] E4 where
  toFun x := WithLp.toLp 2 (fun i => inner Real (hq.toIsometry x) (n i))
  map_add' x y := by
    ext i
    simp [inner_add_left]
  map_smul' a x := by
    ext i
    simp [real_inner_smul_left]

@[simp] theorem normalMap_apply {q : Fin 4 -> E4} (hq : IsONFrame q)
    (n : Fin 4 -> E4) (x : E4) (i : Fin 4) :
    normalMap hq n x i = inner Real (hq.toIsometry x) (n i) := rfl

theorem normalMap_error {q : Fin 4 -> E4} (hq : IsONFrame q)
    (n : Fin 4 -> E4) (d : Real) (hd : 0 ≤ d)
    (h : forall i, norm (n i-q i) ≤ d) (x : E4) :
    norm (normalMap hq n x-x) ≤ 4*d*norm x := by
  have hcoord : forall i : Fin 4, |(normalMap hq n x-x) i| ≤ d*norm x := by
    intro i
    have heq : (normalMap hq n x-x) i = inner Real (hq.toIsometry x) (n i-q i) := by
      simp [inner_sub_right, IsONFrame.inner_toIsometry]
    rw [heq]
    calc
      |inner Real (hq.toIsometry x) (n i-q i)| ≤ norm (hq.toIsometry x)*norm (n i-q i) :=
        abs_real_inner_le_norm _ _
      _ = norm x * norm (n i-q i) := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ d*norm x := by
        have hm := mul_le_mul_of_nonneg_left (h i) (norm_nonneg x)
        nlinarith
  have hn := norm_four_le (normalMap hq n x-x) (d*norm x) (by positivity) hcoord
  nlinarith only [hn]

theorem injective (A : E4 →ₗ[Real] E4) (k : Real) (hk : k < 1)
    (hA : forall x, norm (A x-x) ≤ k*norm x) : Function.Injective A := by
  intro x y hxy
  have he : A (x-y) = 0 := by simp [map_sub, hxy]
  have hn := hA (x-y)
  rw [he, zero_sub, norm_neg] at hn
  have hz : norm (x-y) = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

def equivalence (A : E4 →ₗ[Real] E4) (k : Real) (hk : k < 1)
    (hA : forall x, norm (A x-x) ≤ k*norm x) : E4 ≃ₗ[Real] E4 :=
  LinearEquiv.ofInjectiveEndo A (injective A k hk hA)

@[simp] theorem equivalence_apply (A : E4 →ₗ[Real] E4) (k : Real) (hk : k < 1)
    (hA : forall x, norm (A x-x) ≤ k*norm x) (x : E4) :
    equivalence A k hk hA x = A x := rfl

theorem map_norm_le (A : E4 →ₗ[Real] E4) (k : Real)
    (hA : forall x, norm (A x-x) ≤ k*norm x) (x : E4) :
    norm (A x) ≤ (1+k)*norm x := by
  have h : A x = (A x - x) + x := by abel
  rw [h]
  have ht := norm_add_le (A x - x) x
  nlinarith [hA x]

theorem inverse_norm_le (e : E4 ≃ₗ[Real] E4) (k : Real) (hk : k ≤ 1/2)
    (he : forall x, norm (e x-x) ≤ k*norm x) (x : E4) :
    norm (e.symm x) ≤ 2*norm x := by
  have h := he (e.symm x)
  rw [e.apply_symm_apply, norm_sub_rev] at h
  have ht : norm (e.symm x) ≤ norm (e.symm x - x) + norm x := by
    have : e.symm x = (e.symm x - x) + x := by abel
    nth_rw 1 [this]
    exact norm_add_le _ _
  nlinarith [norm_nonneg (e.symm x)]

theorem inverse_error (e : E4 ≃ₗ[Real] E4) (k : Real) (hk0 : 0 ≤ k)
    (hk : k ≤ 1/2) (he : forall x, norm (e x-x) ≤ k*norm x) (x : E4) :
    norm (e.symm x-x) ≤ 2*k*norm x := by
  have h := he (e.symm x)
  rw [e.apply_symm_apply, norm_sub_rev] at h
  have hn := inverse_norm_le e k hk he x
  have hm := mul_le_mul_of_nonneg_left hn hk0
  nlinarith

theorem inverse_second_error (e : E4 ≃ₗ[Real] E4) (k : Real) (hk0 : 0 ≤ k)
    (hk : k ≤ 1/2) (he : forall x, norm (e x-x) ≤ k*norm x) (x : E4) :
    norm (e.symm x-x+(e x-x)) ≤ 2*k^2*norm x := by
  have hid : e.symm x-x+(e x-x) = e (x-e.symm x)-(x-e.symm x) := by
    rw [map_sub, e.apply_symm_apply]
    abel
  rw [hid]
  have h := he (x-e.symm x)
  have hi := inverse_error e k hk0 hk he x
  rw [norm_sub_rev] at hi
  have hm := mul_le_mul_of_nonneg_left hi hk0
  nlinarith

def jacobian (e : E4 ≃ₗ[Real] E4) : Real := |(LinearMap.det e.toLinearMap)⁻¹|

theorem jacobian_pos (e : E4 ≃ₗ[Real] E4) : 0 < jacobian e := by
  exact abs_pos.mpr (inv_ne_zero ((LinearEquiv.isUnit_det' e).ne_zero))

/-- One neighborhood of the identity controls the determinant uniformly. -/
theorem exists_jacobian_neighborhood :
    ∃ eta : Real, 0 < eta ∧
      forall e : E4 ≃ₗ[Real] E4,
        norm (e.toContinuousLinearEquiv.toContinuousLinearMap -
          ContinuousLinearMap.id Real E4) < eta ->
        1/2 ≤ jacobian e ∧ jacobian e ≤ 2 := by
  have hc : ContinuousAt (fun f : E4 →L[Real] E4 => f.det)
      (ContinuousLinearMap.id Real E4) := ContinuousLinearMap.continuous_det.continuousAt
  obtain ⟨eta, heta, hclose⟩ :=
    (Metric.continuousAt_iff.mp hc) (1/2) (by norm_num)
  refine ⟨eta, heta, ?_⟩
  intro e he
  have hd : |LinearMap.det e.toLinearMap - 1| < 1/2 := by
    have h := hclose (x := e.toContinuousLinearEquiv.toContinuousLinearMap)
      (by simpa only [dist_eq_norm] using he)
    rw [Real.dist_eq] at h
    have hid : (ContinuousLinearMap.id Real E4).det = 1 := LinearMap.det_id
    have hcoe : (e.toContinuousLinearEquiv.toContinuousLinearMap).det = LinearMap.det e.toLinearMap := rfl
    rw [hid, hcoe] at h
    exact h
  have hdl : 0 < LinearMap.det e.toLinearMap := by have h := abs_lt.mp hd; linarith
  have hdu : LinearMap.det e.toLinearMap < 2 := by have h := abs_lt.mp hd; linarith
  have hdl2 : 1/2 < LinearMap.det e.toLinearMap := by have h := abs_lt.mp hd; linarith
  rw [jacobian, abs_of_pos (inv_pos.mpr hdl)]
  constructor
  · rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num]
    exact (inv_le_inv₀ (by norm_num) hdl).mpr (by linarith)
  · rw [show (2 : Real) = (1 / 2 : Real)⁻¹ by norm_num]
    exact (inv_le_inv₀ hdl (by norm_num)).mpr (by linarith)

theorem opNorm_error (e : E4 ≃ₗ[Real] E4) (k : Real) (hk0 : 0 ≤ k)
    (he : forall x, norm (e x-x) ≤ k*norm x) :
    norm (e.toContinuousLinearEquiv.toContinuousLinearMap -
      ContinuousLinearMap.id Real E4) ≤ k := by
  apply ContinuousLinearMap.opNorm_le_bound _ hk0
  intro x
  exact he x

end NearIdentity
end SoberonConvexBody
