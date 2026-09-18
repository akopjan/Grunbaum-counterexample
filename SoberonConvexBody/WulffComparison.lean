import Mathlib
import SoberonConvexBody.Geometry

/-!
# Quantitative comparison of the Wulff body with its radial first-order model

This file isolates the elementary estimate behind the convex-body replacement.
The support function is `1 + eps * f / 4`.  If `f` is bounded and Lipschitz on
`S^3`, then the radial function differs from `1 + eps * f / 4` by `O(eps^2)`.
-/

noncomputable section

namespace SoberonConvexBody

open Set Real MeasureTheory

/-- Scalar inequality used in the Wulff/radial comparison.  It is just the
identity `d^2 = 2(1-t)` on the unit sphere followed by Young's inequality. -/
theorem wulff_scalar_gap
    {eps L M D t d a : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hD : L^2 / 8 ≤ D)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hd0 : 0 ≤ d) (hd2 : d^2 = 2 * (1 - t))
    (ha : |a| ≤ L * d + M * (1 - t))
    (heM : |eps| * M ≤ 1)
    (heL : |eps| * L ≤ 1 / 8) :
    0 ≤ (1 - t) + (eps / 4) * a + D * eps^2 * t := by
  have h1mt : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hD0 : 0 ≤ D := by
    have hsq : 0 ≤ L^2 := sq_nonneg L
    nlinarith
  have ha' : -(L * d + M * (1 - t)) ≤ a := (neg_le_of_abs_le ha)
  have habse : 0 ≤ |eps| := abs_nonneg eps
  have hLd0 : 0 ≤ L * d := mul_nonneg hL hd0
  have hMa0 : 0 ≤ M * (1 - t) := mul_nonneg hM h1mt
  have heterm :
      (eps / 4) * a ≥ -(|eps| / 4) * (L * d + M * (1 - t)) := by
    by_cases he : 0 ≤ eps
    · rw [abs_of_nonneg he]
      have hscale : 0 ≤ eps / 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left ha' hscale]
    · have he' : eps < 0 := lt_of_not_ge he
      rw [abs_of_neg he']
      have haupper : a ≤ L * d + M * (1 - t) := le_of_abs_le ha
      have hscale : eps / 4 ≤ 0 := by linarith
      have := mul_le_mul_of_nonpos_left haupper hscale
      nlinarith
  have hMpart : (|eps| / 4) * (M * (1 - t)) ≤ (1 - t) / 4 := by
    have := mul_le_mul_of_nonneg_right heM h1mt
    nlinarith
  have hYoung :
      (|eps| / 4) * (L * d) ≤ (1 - t) / 2 + eps^2 * L^2 / 16 := by
    have hs : 0 ≤ (d / 2 - |eps| * L / 4)^2 := sq_nonneg _
    have hepssq : (|eps| * L / 4)^2 = eps^2 * L^2 / 16 := by
      calc
        (|eps| * L / 4)^2 = |eps|^2 * L^2 / 16 := by ring
        _ = eps^2 * L^2 / 16 := by rw [sq_abs]
    nlinarith
  by_cases ht : (1 / 2 : ℝ) ≤ t
  · have hDt : L^2 / 16 ≤ D * t := by
      have hleft : L^2 / 16 ≤ (L^2 / 8) * t := by
        have := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ L^2 / 8)
        nlinarith
      have hright : (L^2 / 8) * t ≤ D * t :=
        mul_le_mul_of_nonneg_right hD (le_of_lt ht0)
      exact hleft.trans hright
    have hDt' : eps^2 * L^2 / 16 ≤ D * eps^2 * t := by
      have he2 : 0 ≤ eps^2 := sq_nonneg eps
      nlinarith [mul_le_mul_of_nonneg_left hDt he2]
    nlinarith
  · have htlt : t < 1 / 2 := lt_of_not_ge ht
    have h1mt2 : 1 / 2 < 1 - t := by linarith
    have hd2lt : d^2 < 2 := by nlinarith
    have hdlt2 : d < 2 := by nlinarith [sq_nonneg (d - 2), sq_nonneg d]
    have hLpart : (|eps| / 4) * (L * d) ≤ 1 / 16 := by
      have hprod1 : |eps| * L * d ≤ (1 / 8 : ℝ) * d :=
        mul_le_mul_of_nonneg_right heL hd0
      have hprod2 : (1 / 8 : ℝ) * d < 1 / 4 := by
        have := mul_lt_mul_of_pos_left hdlt2 (by norm_num : (0 : ℝ) < 1 / 8)
        nlinarith
      nlinarith
    have hDterm : 0 ≤ D * eps^2 * t := by positivity
    nlinarith


/-- A Lipschitz bound for `f` and a sup-norm bound for `f` control the mixed
quantity `f(v) - <u,v> f(u)`. -/
theorem angular_mixed_bound
    {tau L M : ℝ} (_hL : 0 ≤ L) (_hM : 0 ≤ M)
    (hlip : ∀ u v : E4, ‖u‖ = 1 → ‖v‖ = 1 →
      |angularPerturbation tau v - angularPerturbation tau u| ≤ L * ‖v - u‖)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    {u v : E4} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |angularPerturbation tau v -
        inner ℝ u v * angularPerturbation tau u| ≤
      L * ‖v - u‖ + M * (1 - inner ℝ u v) := by
  have ht : inner ℝ u v ≤ 1 := by
    have h := real_inner_le_norm u v
    simpa [hu, hv] using h
  have h1mt : 0 ≤ 1 - inner ℝ u v := sub_nonneg.mpr ht
  have hdiff := hlip u v hu hv
  have hfu := hbound u hu
  calc
    |angularPerturbation tau v -
        inner ℝ u v * angularPerturbation tau u|
        = |(angularPerturbation tau v - angularPerturbation tau u) +
            (1 - inner ℝ u v) * angularPerturbation tau u| := by ring_nf
    _ ≤ |angularPerturbation tau v - angularPerturbation tau u| +
          |(1 - inner ℝ u v) * angularPerturbation tau u| := abs_add_le _ _
    _ ≤ L * ‖v - u‖ + (1 - inner ℝ u v) * M := by
      rw [abs_mul, abs_of_nonneg h1mt]
      exact add_le_add hdiff (mul_le_mul_of_nonneg_left hfu h1mt)
    _ = L * ‖v - u‖ + M * (1 - inner ℝ u v) := by ring

/-- Quantitative inner inclusion.  It is the key point at which convexity and
first-order radial behavior of the Wulff body are connected. -/
theorem shrunkenLinearRadialSet_subset_supportBody
    {tau eps L M D : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hlip : ∀ u v : E4, ‖u‖ = 1 → ‖v‖ = 1 →
      |angularPerturbation tau v - angularPerturbation tau u| ≤ L * ‖v - u‖)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (hD : L^2 / 8 ≤ D)
    (heM : |eps| * M ≤ 1)
    (heL : |eps| * L ≤ 1 / 8) :
    shrunkenLinearRadialSet tau eps D ⊆ supportBody tau eps := by
  intro x hx v hv
  have hsupportPos : 0 ≤ 1 + (eps / 4) * angularPerturbation tau v := by
    have hf := hbound v hv
    have he : |eps| * |angularPerturbation tau v| ≤ 1 :=
      (mul_le_mul_of_nonneg_left hf (abs_nonneg eps)).trans heM
    have habs : |(eps / 4) * angularPerturbation tau v| ≤ 1 / 4 := by
      rw [abs_mul, abs_div]
      have : |(4 : ℝ)| = 4 := by norm_num
      rw [this]
      nlinarith
    nlinarith [neg_le_of_abs_le habs]
  by_cases hx0 : x = 0
  · subst x
    simpa using hsupportPos
  · let u : E4 := direction x
    have hu : ‖u‖ = 1 := norm_direction hx0
    have hr : ‖x‖ ≤
        1 + (eps / 4) * angularPerturbation tau u - D * eps^2 := by
      exact hx
    have hrepr : x = ‖x‖ • u := by
      symm
      exact norm_smul_direction hx0
    let t : ℝ := inner ℝ u v
    have ht1 : t ≤ 1 := by
      have h := real_inner_le_norm u v
      simpa [t, hu, hv] using h
    by_cases htpos : 0 < t
    · let d : ℝ := ‖v - u‖
      have hd0 : 0 ≤ d := norm_nonneg _
      have hd2 : d^2 = 2 * (1 - t) := by
        have h := norm_sub_sq_real v u
        rw [hv, hu] at h
        dsimp [d, t]
        nlinarith [real_inner_comm u v]
      have ha :
          |angularPerturbation tau v - t * angularPerturbation tau u| ≤
            L * d + M * (1 - t) := by
        simpa [t, d] using
          angular_mixed_bound hL hM hlip hbound hu hv
      have hgap := wulff_scalar_gap hL hM hD htpos ht1 hd0 hd2 ha heM heL
      have hrt : ‖x‖ * t ≤
          (1 + (eps / 4) * angularPerturbation tau u - D * eps^2) * t :=
        mul_le_mul_of_nonneg_right hr (le_of_lt htpos)
      rw [hrepr, real_inner_smul_left]
      dsimp [t] at hrt ⊢
      nlinarith
    · have ht : t ≤ 0 := le_of_not_gt htpos
      have hleft : inner ℝ x v ≤ 0 := by
        rw [hrepr, real_inner_smul_left]
        dsimp [t] at ht ⊢
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg x) ht
      exact hleft.trans hsupportPos


/-- Concrete real Lipschitz constant on the sphere, extracted from the compact
`C¹` theorem used in `Geometry.lean`. -/
theorem angularPerturbation_lipschitz_on_sphere (tau : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ u v : E4, ‖u‖ = 1 → ‖v‖ = 1 →
        |angularPerturbation tau v - angularPerturbation tau u| ≤
          L * ‖v - u‖ := by
  rcases angularPerturbation_lipschitzOn_unitBall tau with ⟨K, hK⟩
  refine ⟨(K : ℝ), NNReal.coe_nonneg K, ?_⟩
  intro u v hu hv
  have huB : u ∈ Metric.closedBall (0 : E4) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, hu]
  have hvB : v ∈ Metric.closedBall (0 : E4) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, hv]
  have h := hK.dist_le_mul v hvB u huB
  rw [Real.dist_eq, dist_eq_norm] at h
  exact h

/-- Uniform Wulff/radial set sandwich.  The outer inclusion is exact and the
inner inclusion loses only `D * eps^2` in radial distance. -/
theorem supportBody_radial_sandwich (tau : ℝ) :
    ∃ eps0 D : ℝ, 0 < eps0 ∧ 0 ≤ D ∧
      ∀ eps, |eps| < eps0 →
        shrunkenLinearRadialSet tau eps D ⊆ supportBody tau eps ∧
        supportBody tau eps ⊆ linearRadialSet tau eps := by
  rcases angularPerturbation_bounded_on_sphere tau with ⟨M, hM, hbound⟩
  rcases angularPerturbation_lipschitz_on_sphere tau with ⟨L, hL, hlip⟩
  let D : ℝ := L^2 / 8
  let eps0 : ℝ := min (1 / M) (1 / (8 * (L + 1)))
  have hLp : 0 < L + 1 := by linarith
  have hepsM : 0 < 1 / M := by positivity
  have hepsL : 0 < 1 / (8 * (L + 1)) := by positivity
  have heps0 : 0 < eps0 := by
    dsimp [eps0]
    exact lt_min hepsM hepsL
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨eps0, D, heps0, hD0, ?_⟩
  intro eps heps
  have heMlt : |eps| * M < 1 := by
    have hsmall : |eps| < 1 / M :=
      lt_of_lt_of_le heps (by dsimp [eps0]; exact min_le_left _ _)
    have := mul_lt_mul_of_pos_right hsmall hM
    field_simp [ne_of_gt hM] at this
    exact this
  have heLlt : |eps| * L < 1 / 8 := by
    have hsmall : |eps| < 1 / (8 * (L + 1)) :=
      lt_of_lt_of_le heps (by dsimp [eps0]; exact min_le_right _ _)
    have hprod : |eps| * (L + 1) < 1 / 8 := by
      have := mul_lt_mul_of_pos_right hsmall hLp
      have hden : 8 * (L + 1) ≠ 0 := by positivity
      field_simp [hden] at this
      nlinarith
    have hmono : |eps| * L ≤ |eps| * (L + 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg eps)
    exact lt_of_le_of_lt hmono hprod
  constructor
  · apply shrunkenLinearRadialSet_subset_supportBody hL (le_of_lt hM)
      hlip hbound
    · dsimp [D]
      exact le_rfl
    · exact le_of_lt heMlt
    · exact le_of_lt heLlt
  · exact supportBody_subset_linearRadialSet tau eps

end SoberonConvexBody
