import Mathlib
import SoberonConvexBody.WulffVolume

/-!
# Comparing Soberon's exact radial model with the linear radial model

For `a = eps * f(u)`, the exact model has radial radius `(1+a)^(1/4)`,
whereas the linear model has radius `1+a/4`.  The elementary estimate

  0 <= (1+a/4)^4 - (1+a) <= a^2/2       (|a| <= 1)

shows that the two bodies differ only to second order.  We use the same
homothetic sandwich from `WulffVolume.lean`, so no additional polar-coordinate
formula is needed for this comparison.
-/

noncomputable section

namespace SoberonConvexBody

open Set Real MeasureTheory

/-- The fourth power of the first-order radius exceeds the exact radial
right-hand side by a nonnegative quadratic error. -/
theorem linear_fourth_gap {a : ℝ} (ha : |a| ≤ 1) :
    0 ≤ (1 + a / 4)^4 - (1 + a) ∧
      (1 + a / 4)^4 - (1 + a) ≤ a^2 / 2 := by
  have halow : -1 ≤ a := neg_le_of_abs_le ha
  have haup : a ≤ 1 := le_of_abs_le ha
  have ha2 : a^2 ≤ 1 := by
    calc
      a^2 = |a|^2 := by rw [sq_abs]
      _ ≤ (1 : ℝ)^2 := pow_le_pow_left₀ (abs_nonneg a) ha 2
      _ = 1 := by norm_num
  have hnum0 : 0 ≤ 96 + 16 * a + a^2 := by
    nlinarith
  have hnum128 : 96 + 16 * a + a^2 ≤ 128 := by
    nlinarith
  have hid :
      (1 + a / 4)^4 - (1 + a) =
        a^2 * (96 + 16 * a + a^2) / 256 := by
    ring
  rw [hid]
  constructor
  · positivity
  · have hmul := mul_le_mul_of_nonneg_left hnum128 (sq_nonneg a)
    nlinarith

/-- If the linear radius is additionally decreased by `d`, with `d` at least
the quadratic Taylor error, then its fourth power lies below the exact radial
right-hand side. -/
theorem shrunken_linear_fourth_le
    {a d : ℝ} (ha : |a| ≤ 1) (hd0 : 0 ≤ d)
    (ha2d : a^2 ≤ d) (hdsmall : d ≤ 1 / 4) :
    (1 + a / 4 - d)^4 ≤ 1 + a := by
  let R : ℝ := 1 + a / 4
  let s : ℝ := R - d
  have halow : -1 ≤ a := neg_le_of_abs_le ha
  have hR34 : (3 / 4 : ℝ) ≤ R := by
    dsimp [R]
    linarith
  have hRhalf : (1 / 2 : ℝ) ≤ R := by linarith
  have hshalf : (1 / 2 : ℝ) ≤ s := by
    dsimp [s]
    linarith
  have hR2 : (1 / 4 : ℝ) ≤ R^2 := by
    nlinarith
  have hs2 : (1 / 4 : ℝ) ≤ s^2 := by
    nlinarith
  have hsum : (1 : ℝ) ≤ R + s := by linarith
  have hsqsum : (1 / 2 : ℝ) ≤ R^2 + s^2 := by linarith
  have hsum0 : 0 ≤ R + s := le_trans (by norm_num) hsum
  have hdsum0 : 0 ≤ d * (R + s) := mul_nonneg hd0 hsum0
  have hfirst : d / 2 ≤ d * (R + s) / 2 := by
    have h := mul_le_mul_of_nonneg_left hsum hd0
    nlinarith
  have hsecond : d * (R + s) / 2 ≤ d * (R + s) * (R^2 + s^2) := by
    have h := mul_le_mul_of_nonneg_left hsqsum hdsum0
    nlinarith
  have hfactor :
      R^4 - s^4 = d * (R + s) * (R^2 + s^2) := by
    dsimp [s]
    ring
  have hloss : d / 2 ≤ R^4 - s^4 := by
    rw [hfactor]
    exact hfirst.trans hsecond
  have hgap := (linear_fourth_gap ha).2
  have hgapd : R^4 - (1 + a) ≤ d / 2 := by
    dsimp [R]
    linarith
  have hs : s^4 ≤ 1 + a := by
    linarith
  simpa [s, R] using hs

/-- The exact radial body is contained in the first-order linear radial body. -/
theorem radialSet_subset_linearRadialSet
    {tau eps M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 1) :
    radialSet tau eps ⊆ linearRadialSet tau eps := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp [linearRadialSet, angularPerturbation_zero]
  · have hu : ‖direction x‖ = 1 := norm_direction hx0
    have hf := hbound (direction x) hu
    let a : ℝ := eps * angularPerturbation tau (direction x)
    have ha : |a| ≤ 1 := by
      dsimp [a]
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hf (abs_nonneg eps)).trans heM
    have hR0 : 0 ≤ 1 + a / 4 := by
      have := neg_le_of_abs_le ha
      linarith
    have hpow : ‖x‖^4 ≤ (1 + a / 4)^4 := by
      have hgap := (linear_fourth_gap ha).1
      change ‖x‖^4 ≤ 1 + a at hx
      exact hx.trans (by linarith)
    have hnorm : ‖x‖ ≤ 1 + a / 4 :=
      le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hR0 hpow
    change ‖x‖ ≤ 1 + (eps / 4) * angularPerturbation tau (direction x)
    dsimp [a] at hnorm
    convert hnorm using 1; ring

/-- A quadratic uniform shrink of the linear radial model lies inside the exact
radial model. -/
theorem shrunkenLinearRadialSet_subset_radialSet
    {tau eps M D : ℝ} (_hM : 0 ≤ M)
    (hD : M^2 ≤ D)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 1)
    (hsmallD : D * eps^2 ≤ 1 / 4) :
    shrunkenLinearRadialSet tau eps D ⊆ radialSet tau eps := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp [radialSet, angularPerturbation_zero]
  · have hu : ‖direction x‖ = 1 := norm_direction hx0
    have hf := hbound (direction x) hu
    let a : ℝ := eps * angularPerturbation tau (direction x)
    let d : ℝ := D * eps^2
    have ha : |a| ≤ 1 := by
      dsimp [a]
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hf (abs_nonneg eps)).trans heM
    have habs : |a| ≤ |eps| * M := by
      dsimp [a]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hf (abs_nonneg eps)
    have ha2 : a^2 ≤ eps^2 * M^2 := by
      calc
        a^2 = |a|^2 := by rw [sq_abs]
        _ ≤ (|eps| * M)^2 :=
          pow_le_pow_left₀ (abs_nonneg a) habs 2
        _ = eps^2 * M^2 := by rw [mul_pow, sq_abs]
    have hd0 : 0 ≤ d := by
      dsimp [d]
      have hD0 : 0 ≤ D := le_trans (sq_nonneg M) hD
      positivity
    have ha2d : a^2 ≤ d := by
      have hmul := mul_le_mul_of_nonneg_left hD (sq_nonneg eps)
      dsimp [d]
      nlinarith
    have hdsmall : d ≤ 1 / 4 := by simpa [d] using hsmallD
    have hs4 : (1 + a / 4 - d)^4 ≤ 1 + a :=
      shrunken_linear_fourth_le ha hd0 ha2d hdsmall
    have hnorm : ‖x‖ ≤ 1 + a / 4 - d := by
      change ‖x‖ ≤ 1 + (eps / 4) * angularPerturbation tau (direction x) - D * eps^2 at hx
      dsimp [a, d]
      convert hx using 1; ring
    have hpow : ‖x‖^4 ≤ (1 + a / 4 - d)^4 :=
      pow_le_pow_left₀ (norm_nonneg x) hnorm 4
    change ‖x‖^4 ≤ 1 + eps * angularPerturbation tau (direction x)
    dsimp [a] at hs4 ⊢
    exact hpow.trans (by simpa [d] using hs4)

/-- The exact radial body differs from the linear radial model by `O(eps^2)`
in four-dimensional volume. -/
theorem radialSet_symmDiff_linearRadialSet_le
    {tau eps M D : ℝ} (hM : 0 ≤ M) (hD0 : 0 ≤ D) (hDM : M^2 ≤ D)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 1)
    (hsmallD : D * eps^2 ≤ 1 / 4)
    (hdelta : 2 * D * eps^2 < 1) :
    volume.real (symmDiff (radialSet tau eps) (linearRadialSet tau eps)) ≤
      8 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by
  apply sandwichedSet_symmDiff_linearRadialSet_le hM hD0 hbound
    (heM.trans (by norm_num)) hdelta
  · exact shrunkenLinearRadialSet_subset_radialSet hM hDM hbound heM hsmallD
  · exact radialSet_subset_linearRadialSet hM hbound heM

/-- Every Walsh coefficient of the exact radial body differs from that of the
linear radial model by `O(eps^2)`. -/
theorem radialSet_walsh_linearRadialSet_le
    {tau eps M D : ℝ} (hM : 0 ≤ M) (hD0 : 0 ≤ D) (hDM : M^2 ≤ D)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 1)
    (hsmallD : D * eps^2 ≤ 1 / 4)
    (hdelta : 2 * D * eps^2 < 1)
    (c : HyperplaneCfg) (I : Walsh4.Index) :
    |walsh (radialMeasure tau eps) c I -
      walsh (volume.restrict (linearRadialSet tau eps)) c I| ≤
      128 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by
  have houter := radialSet_subset_linearRadialSet hM hbound heM
  have hlin_ball := linearRadialSet_subset_closedBall_three_halves hM hbound
    (heM.trans (by norm_num))
  have hballfin : volume (Metric.closedBall (0 : E4) (3 / 2)) ≠ ⊤ :=
    (isCompact_closedBall (0 : E4) (3 / 2)).measure_ne_top
  have hlinfin : volume (linearRadialSet tau eps) ≠ ⊤ :=
    measure_ne_top_of_subset hlin_ball hballfin
  have hradfin : volume (radialSet tau eps) ≠ ⊤ :=
    measure_ne_top_of_subset houter hlinfin
  have hsymfin : volume (symmDiff (radialSet tau eps)
      (linearRadialSet tau eps)) ≠ ⊤ := by
    have hsub : symmDiff (radialSet tau eps) (linearRadialSet tau eps) ⊆
        linearRadialSet tau eps := by
      rw [symmDiff_comm, symmDiff_eq_sdiff_of_subset houter]
      exact sdiff_subset
    exact measure_ne_top_of_subset hsub hlinfin
  have hstable := abs_walsh_restrict_sub_le_symmDiff
    (A := radialSet tau eps) (B := linearRadialSet tau eps) c I
    hradfin hlinfin hsymfin
  have hvol := radialSet_symmDiff_linearRadialSet_le
    hM hD0 hDM hbound heM hsmallD hdelta
  unfold radialMeasure
  calc
    |walsh (volume.restrict (radialSet tau eps)) c I -
      walsh (volume.restrict (linearRadialSet tau eps)) c I|
        ≤ 16 * volume.real (symmDiff (radialSet tau eps)
            (linearRadialSet tau eps)) := hstable
    _ ≤ 16 *
        (8 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2) :=
          mul_le_mul_of_nonneg_left hvol (by norm_num)
    _ = 128 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by ring



/-- A crude but convenient Euclidean norm bound in five coordinates. -/
theorem E5_norm_le_five_mul_of_coord_abs_le
    {v : E5} {a : ℝ} (ha : 0 ≤ a) (hcoord : ∀ i, |v i| ≤ a) :
    ‖v‖ ≤ 5 * a := by
  have hsqcoord : ∀ i : Fin 5, (v i)^2 ≤ a^2 := by
    intro i
    calc
      (v i)^2 = |v i|^2 := by rw [sq_abs]
      _ ≤ a^2 := pow_le_pow_left₀ (abs_nonneg (v i)) (hcoord i) 2
  have hsum : (∑ i : Fin 5, (v i)^2) ≤ 5 * a^2 := by
    calc
      (∑ i : Fin 5, (v i)^2) ≤ ∑ _i : Fin 5, a^2 :=
        Finset.sum_le_sum (fun i _ => hsqcoord i)
      _ = 5 * a^2 := by simp
  have hnormsq : ‖v‖^2 ≤ 5 * a^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact hsum
  have htargetsq : ‖v‖^2 ≤ (5 * a)^2 := by
    nlinarith [sq_nonneg a]
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
    (mul_nonneg (by norm_num) ha) htargetsq

/-- Under common quantitative bounds, every Walsh coefficient of the Wulff
body and of Soberon's exact radial body differs by `O(eps^2)`.  Thus all
first-order calculations may be performed on the exact radial model and then
transported to the convex Wulff body. -/
theorem supportBody_walsh_radialSet_le
    {tau eps L M D : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hD0 : 0 ≤ D)
    (hDL : L^2 / 8 ≤ D) (hDM : M^2 ≤ D)
    (hlip : ∀ u v : E4, ‖u‖ = 1 → ‖v‖ = 1 →
      |angularPerturbation tau v - angularPerturbation tau u| ≤ L * ‖v - u‖)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 1)
    (heL : |eps| * L ≤ 1 / 8)
    (hsmallD : D * eps^2 ≤ 1 / 4)
    (hdelta : 2 * D * eps^2 < 1)
    (c : HyperplaneCfg) (I : Walsh4.Index) :
    |walsh (supportMeasure tau eps) c I -
      walsh (radialMeasure tau eps) c I| ≤
      256 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by
  have hinnerSupport :
      shrunkenLinearRadialSet tau eps D ⊆ supportBody tau eps :=
    shrunkenLinearRadialSet_subset_supportBody hL hM hlip hbound hDL heM heL
  have houterSupport :
      supportBody tau eps ⊆ linearRadialSet tau eps :=
    supportBody_subset_linearRadialSet tau eps
  have hsup := supportBody_walsh_linearRadialSet_le
    hM hD0 hbound (heM.trans (by norm_num)) hdelta
    hinnerSupport houterSupport c I
  have hrad := radialSet_walsh_linearRadialSet_le
    hM hD0 hDM hbound heM hsmallD hdelta c I
  have htri :
      |walsh (supportMeasure tau eps) c I - walsh (radialMeasure tau eps) c I| ≤
        |walsh (supportMeasure tau eps) c I -
          walsh (volume.restrict (linearRadialSet tau eps)) c I| +
        |walsh (radialMeasure tau eps) c I -
          walsh (volume.restrict (linearRadialSet tau eps)) c I| := by
    have h := abs_sub_le
      (walsh (supportMeasure tau eps) c I)
      (walsh (volume.restrict (linearRadialSet tau eps)) c I)
      (walsh (radialMeasure tau eps) c I)
    simpa [abs_sub_comm (walsh (volume.restrict (linearRadialSet tau eps)) c I)
      (walsh (radialMeasure tau eps) c I)] using h
  calc
    |walsh (supportMeasure tau eps) c I - walsh (radialMeasure tau eps) c I|
        ≤ |walsh (supportMeasure tau eps) c I -
            walsh (volume.restrict (linearRadialSet tau eps)) c I| +
          |walsh (radialMeasure tau eps) c I -
            walsh (volume.restrict (linearRadialSet tau eps)) c I| := htri
    _ ≤ (128 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2) +
          (128 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2) :=
      add_le_add hsup hrad
    _ = 256 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by ring


/-- Vector form of `supportBody_walsh_radialSet_le` for the five high Walsh
coefficients. -/
theorem highWalsh_supportBody_radialSet_le
    {tau eps L M D : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hD0 : 0 ≤ D)
    (hDL : L^2 / 8 ≤ D) (hDM : M^2 ≤ D)
    (hlip : ∀ u v : E4, ‖u‖ = 1 → ‖v‖ = 1 →
      |angularPerturbation tau v - angularPerturbation tau u| ≤ L * ‖v - u‖)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 1)
    (heL : |eps| * L ≤ 1 / 8)
    (hsmallD : D * eps^2 ≤ 1 / 4)
    (hdelta : 2 * D * eps^2 < 1)
    (c : HyperplaneCfg) :
    ‖highWalsh (supportMeasure tau eps) c -
      highWalsh (radialMeasure tau eps) c‖ ≤
      1280 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by
  let a : ℝ :=
    256 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hcoords : ∀ i : Fin 5,
      |(highWalsh (supportMeasure tau eps) c -
        highWalsh (radialMeasure tau eps) c) i| ≤ a := by
    intro i
    have hcoord := supportBody_walsh_radialSet_le
      hL hM hD0 hDL hDM hlip hbound heM heL hsmallD hdelta c
    fin_cases i
    · simpa [highWalsh, a] using
        (hcoord ({1,2,3} : Walsh4.Index) :
          |walsh (supportMeasure tau eps) c {1,2,3} -
            walsh (radialMeasure tau eps) c {1,2,3}| ≤ a)
    · simpa [highWalsh, a] using
        (hcoord ({0,2,3} : Walsh4.Index) :
          |walsh (supportMeasure tau eps) c {0,2,3} -
            walsh (radialMeasure tau eps) c {0,2,3}| ≤ a)
    · simpa [highWalsh, a] using
        (hcoord ({0,1,3} : Walsh4.Index) :
          |walsh (supportMeasure tau eps) c {0,1,3} -
            walsh (radialMeasure tau eps) c {0,1,3}| ≤ a)
    · simpa [highWalsh, a] using
        (hcoord ({0,1,2} : Walsh4.Index) :
          |walsh (supportMeasure tau eps) c {0,1,2} -
            walsh (radialMeasure tau eps) c {0,1,2}| ≤ a)
    · simpa [highWalsh, a] using
        (hcoord ({0,1,2,3} : Walsh4.Index) :
          |walsh (supportMeasure tau eps) c {0,1,2,3} -
            walsh (radialMeasure tau eps) c {0,1,2,3}| ≤ a)
  calc
    ‖highWalsh (supportMeasure tau eps) c -
      highWalsh (radialMeasure tau eps) c‖
        ≤ 5 * a := E5_norm_le_five_mul_of_coord_abs_le ha hcoords
    _ = 1280 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by
      dsimp [a]
      ring


/-- Uniform version of the Wulff/exact-radial comparison.  All quantitative
constants are chosen once for a fixed tensor parameter `tau`. -/
theorem supportBody_radialSet_walsh_quadratic (tau : ℝ) :
    ∃ eps0 C : ℝ, 0 < eps0 ∧ 0 < C ∧
      ∀ eps, |eps| < eps0 → ∀ c I,
        |walsh (supportMeasure tau eps) c I -
          walsh (radialMeasure tau eps) c I| ≤ C * eps^2 := by
  rcases angularPerturbation_bounded_on_sphere tau with ⟨M, hM, hbound⟩
  rcases angularPerturbation_lipschitz_on_sphere tau with ⟨L, hL, hlip⟩
  let D : ℝ := L^2 / 8 + M^2 + 1
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hDL : L^2 / 8 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg M]
  have hDM : M^2 ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg L]
  let eM : ℝ := 1 / M
  let eL : ℝ := 1 / (8 * (L + 1))
  let eD : ℝ := 1 / (4 * (D + 1))
  let eps0 : ℝ := min eM (min eL eD)
  let V : ℝ := volume.real (Metric.closedBall (0 : E4) (3 / 2))
  let C : ℝ := 256 * D * V + 1
  have heMpos : 0 < eM := by
    dsimp [eM]
    positivity
  have hLp : 0 < L + 1 := by linarith
  have heLpos : 0 < eL := by
    dsimp [eL]
    positivity
  have hDp : 0 < D + 1 := by linarith
  have heDpos : 0 < eD := by
    dsimp [eD]
    positivity
  have heps0 : 0 < eps0 := by
    dsimp [eps0]
    exact lt_min heMpos (lt_min heLpos heDpos)
  have hV : 0 ≤ V := by
    dsimp [V]
    exact measureReal_nonneg
  have hC : 0 < C := by
    dsimp [C]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 256)
      (le_of_lt hD)) hV]
  refine ⟨eps0, C, heps0, hC, ?_⟩
  intro eps heps c I
  have heMsmall : |eps| < eM :=
    lt_of_lt_of_le heps (by dsimp [eps0]; exact min_le_left _ _)
  have heLsmall : |eps| < eL :=
    lt_of_lt_of_le heps (by
      dsimp [eps0]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have heDsmall : |eps| < eD :=
    lt_of_lt_of_le heps (by
      dsimp [eps0]
      exact (min_le_right _ _).trans (min_le_right _ _))
  have h_eps_M : |eps| * M ≤ 1 := by
    have hmul := mul_lt_mul_of_pos_right heMsmall hM
    have hM0 : M ≠ 0 := ne_of_gt hM
    dsimp [eM] at hmul
    field_simp [hM0] at hmul
    exact le_of_lt hmul
  have h_eps_L : |eps| * L ≤ 1 / 8 := by
    have hprod : |eps| * (L + 1) < 1 / 8 := by
      have hmul := mul_lt_mul_of_pos_right heLsmall hLp
      have hden : 8 * (L + 1) ≠ 0 := by positivity
      dsimp [eL] at hmul
      field_simp [hden] at hmul
      nlinarith
    have hmono : |eps| * L ≤ |eps| * (L + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg eps)
    exact le_of_lt (hmono.trans_lt hprod)
  have hprodD : |eps| * (D + 1) < 1 / 4 := by
    have hmul := mul_lt_mul_of_pos_right heDsmall hDp
    have hden : 4 * (D + 1) ≠ 0 := by positivity
    dsimp [eD] at hmul
    field_simp [hden] at hmul
    nlinarith
  have hequarter : |eps| < 1 / 4 := by
    have hmono : |eps| ≤ |eps| * (D + 1) := by
      have hD1 : (1 : ℝ) ≤ D + 1 := by linarith
      simpa using mul_le_mul_of_nonneg_left hD1 (abs_nonneg eps)
    exact hmono.trans_lt hprodD
  have heDquarter : |eps| * D < 1 / 4 := by
    have hmono : |eps| * D ≤ |eps| * (D + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg eps)
    exact hmono.trans_lt hprodD
  have hDeps : D * eps^2 < 1 / 16 := by
    rw [← sq_abs]
    calc
      D * |eps|^2 = (|eps| * D) * |eps| := by ring
      _ ≤ (1 / 4) * |eps| :=
        mul_le_mul_of_nonneg_right (le_of_lt heDquarter) (abs_nonneg eps)
      _ < (1 / 4) * (1 / 4) :=
        mul_lt_mul_of_pos_left hequarter (by norm_num)
      _ = 1 / 16 := by norm_num
  have hsmallD : D * eps^2 ≤ 1 / 4 := by linarith
  have hdelta : 2 * D * eps^2 < 1 := by nlinarith
  have hraw := supportBody_walsh_radialSet_le
    hL (le_of_lt hM) (le_of_lt hD) hDL hDM hlip hbound
    h_eps_M h_eps_L hsmallD hdelta c I
  have hcoef : 256 * D * V ≤ C := by
    dsimp [C]
    linarith
  have heps2 : 0 ≤ eps^2 := sq_nonneg eps
  calc
    |walsh (supportMeasure tau eps) c I - walsh (radialMeasure tau eps) c I|
        ≤ 256 * D * V * eps^2 := by simpa [V] using hraw
    _ ≤ C * eps^2 := mul_le_mul_of_nonneg_right hcoef heps2

/-- Uniform vector version for the five high Walsh coefficients. -/
theorem highWalsh_supportBody_radialSet_quadratic (tau : ℝ) :
    ∃ eps0 C : ℝ, 0 < eps0 ∧ 0 < C ∧
      ∀ eps, |eps| < eps0 → ∀ c,
        ‖highWalsh (supportMeasure tau eps) c -
          highWalsh (radialMeasure tau eps) c‖ ≤ C * eps^2 := by
  rcases supportBody_radialSet_walsh_quadratic tau with
    ⟨eps0, C0, heps0, hC0, hcoord⟩
  let C : ℝ := 5 * C0
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨eps0, C, heps0, hC, ?_⟩
  intro eps heps c
  have ha : 0 ≤ C0 * eps^2 := mul_nonneg (le_of_lt hC0) (sq_nonneg eps)
  have hcoords : ∀ i : Fin 5,
      |(highWalsh (supportMeasure tau eps) c -
        highWalsh (radialMeasure tau eps) c) i| ≤ C0 * eps^2 := by
    intro i
    have hc := hcoord eps heps c
    fin_cases i
    · simpa [highWalsh] using hc ({1,2,3} : Walsh4.Index)
    · simpa [highWalsh] using hc ({0,2,3} : Walsh4.Index)
    · simpa [highWalsh] using hc ({0,1,3} : Walsh4.Index)
    · simpa [highWalsh] using hc ({0,1,2} : Walsh4.Index)
    · simpa [highWalsh] using hc ({0,1,2,3} : Walsh4.Index)
  calc
    ‖highWalsh (supportMeasure tau eps) c -
      highWalsh (radialMeasure tau eps) c‖
        ≤ 5 * (C0 * eps^2) :=
          E5_norm_le_five_mul_of_coord_abs_le ha hcoords
    _ = C * eps^2 := by dsimp [C]; ring

end SoberonConvexBody
