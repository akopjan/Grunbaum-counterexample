import Mathlib
import SoberonConvexBody.RadialComparison

/-!
# Quadratic obstruction expansion for the convex Wulff body

This module transfers the robust expansion proved for Soberon's exact radial
model to the genuinely convex Wulff body.  The transfer uses only the
`O(eps^2)` symmetric-difference/Walsh comparison from `RadialComparison.lean`.
-/

noncomputable section

namespace SoberonConvexBody

open Set Real MeasureTheory

/-- If the ten low Walsh coefficients of the Wulff body vanish, then its five
high Walsh coefficients have the same first-order obstruction as the exact
radial model, with a uniform quadratic remainder. -/
theorem highWalsh_support_quadratic_expansion (tau : ℝ) :
    ∃ eps0 C : ℝ, 0 < eps0 ∧ 0 < C ∧
      ∀ eps c,
        |eps| < eps0 → UnitCfg c →
        (∀ I : Walsh4.Index, I.Nonempty → I.card ≤ 2 →
          walsh (supportMeasure tau eps) c I = 0) →
        ∃ q : Fin 4 → E4,
          Tensors.IsONFrame q ∧
          ‖highWalsh (supportMeasure tau eps) c -
            eps • scaledObstruction tau q‖ ≤ C * eps^2 := by
  rcases supportBody_radialSet_walsh_quadratic tau with
    ⟨epsT, CT, hepsT, hCT, htransferLow⟩
  rcases highWalsh_supportBody_radialSet_quadratic tau with
    ⟨epsV, CV, hepsV, hCV, htransferHigh⟩
  rcases highWalsh_quadratic_expansion_robust tau CT (le_of_lt hCT) with
    ⟨epsR, CR, hepsR, hCR, hradial⟩
  let eps0 : ℝ := min epsT (min epsV epsR)
  let C : ℝ := CV + CR
  have heps0 : 0 < eps0 := by
    dsimp [eps0]
    exact lt_min hepsT (lt_min hepsV hepsR)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨eps0, C, heps0, hC, ?_⟩
  intro eps c heps hunit hlowSupport
  have hepsT' : |eps| < epsT :=
    lt_of_lt_of_le heps (by dsimp [eps0]; exact min_le_left _ _)
  have hepsV' : |eps| < epsV :=
    lt_of_lt_of_le heps (by
      dsimp [eps0]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hepsR' : |eps| < epsR :=
    lt_of_lt_of_le heps (by
      dsimp [eps0]
      exact (min_le_right _ _).trans (min_le_right _ _))
  have hlowRadial : ∀ I : Walsh4.Index, I.Nonempty → I.card ≤ 2 →
      |walsh (radialMeasure tau eps) c I| ≤ CT * eps^2 := by
    intro I hI hcard
    have hcomp := htransferLow eps hepsT' c I
    rw [hlowSupport I hI hcard, zero_sub, abs_neg] at hcomp
    exact hcomp
  rcases hradial eps c hepsR' hunit hlowRadial with ⟨q, hq, hrad⟩
  have htrans := htransferHigh eps hepsV' c
  refine ⟨q, hq, ?_⟩
  have hdecomp :
      highWalsh (supportMeasure tau eps) c - eps • scaledObstruction tau q =
        (highWalsh (supportMeasure tau eps) c -
          highWalsh (radialMeasure tau eps) c) +
        (highWalsh (radialMeasure tau eps) c -
          eps • scaledObstruction tau q) := by
    module
  rw [hdecomp]
  calc
    ‖(highWalsh (supportMeasure tau eps) c -
          highWalsh (radialMeasure tau eps) c) +
        (highWalsh (radialMeasure tau eps) c -
          eps • scaledObstruction tau q)‖
        ≤ ‖highWalsh (supportMeasure tau eps) c -
              highWalsh (radialMeasure tau eps) c‖ +
            ‖highWalsh (radialMeasure tau eps) c -
              eps • scaledObstruction tau q‖ := norm_add_le _ _
    _ ≤ CV * eps^2 + CR * eps^2 := add_le_add htrans hrad
    _ = C * eps^2 := by
      dsimp [C]
      ring

end SoberonConvexBody
