import SoberonConvexBody.GeometryCore
import SoberonConvexBody.ShellStability
import SoberonConvexBody.RadialLocalization

noncomputable section
namespace SoberonConvexBody
open Set Real MeasureTheory
open scoped BigOperators

/-- Robust localization by the ten singleton/pair equations.  An
`O(eps^2)` error in those equations still forces the hyperplanes to be
`O(|eps|)` from a centered orthonormal frame.  This robust form is what is
needed after replacing the exact radial model by the convex Wulff body. -/
theorem low_walsh_localization_robust
    (tau A : ℝ) (hA : 0 ≤ A) :
    ∃ eps0 C : ℝ, 0 < eps0 ∧ 0 < C ∧
      ∀ eps c,
        |eps| < eps0 → UnitCfg c →
        (∀ I : Walsh4.Index, I.Nonempty → I.card ≤ 2 →
          |walsh (radialMeasure tau eps) c I| ≤ A * eps^2) →
        ∃ q : Fin 4 → E4,
          Tensors.IsONFrame q ∧
          (∀ i, |c.offset i| ≤ C * |eps|) ∧
          (∀ i, ‖c.normal i - q i‖ ≤ C * |eps|) := by
  exact RadialLocalization.robust_localization tau A hA

/-- Exact localization is the zero-error special case of the robust theorem. -/
theorem low_walsh_localization
    (tau : ℝ) :
    ∃ eps0 C : ℝ, 0 < eps0 ∧ 0 < C ∧
      ∀ eps c,
        |eps| < eps0 → UnitCfg c →
        (∀ I : Walsh4.Index, I.Nonempty → I.card ≤ 2 →
          walsh (radialMeasure tau eps) c I = 0) →
        ∃ q : Fin 4 → E4,
          Tensors.IsONFrame q ∧
          (∀ i, |c.offset i| ≤ C * |eps|) ∧
          (∀ i, ‖c.normal i - q i‖ ≤ C * |eps|) := by
  rcases low_walsh_localization_robust tau 0 (le_refl 0) with
    ⟨eps0, C, heps0, hC, hloc⟩
  refine ⟨eps0, C, heps0, hC, ?_⟩
  intro eps c heps hunit hzero
  apply hloc eps c heps hunit
  intro I hI hcard
  rw [hzero I hI hcard, abs_zero, zero_mul]

/-- Uniform quadratic flatness of high Walsh coefficients for the unit ball. -/
theorem ball_high_quadratic_flatness :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ d c q,
        0 ≤ d → d < delta →
        UnitCfg c → Tensors.IsONFrame q →
        (∀ i, |c.offset i| ≤ d) →
        (∀ i, ‖c.normal i - q i‖ ≤ d) →
        ‖highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c‖
          ≤ C * d ^ 2 := by
  exact BallLocal.high_quadratic_flatness

/-- Moving the hyperplanes by `O(eps)` changes the shell contribution by
`O(eps^2)`. -/
theorem radial_shell_stability
    (tau M : ℝ) (hM : 0 < M) :
    ∃ eps0 C : ℝ, 0 < eps0 ∧ 0 < C ∧
      ∀ eps c q,
        |eps| < eps0 → UnitCfg c → Tensors.IsONFrame q →
        (∀ i, |c.offset i| ≤ M * |eps|) →
        (∀ i, ‖c.normal i - q i‖ ≤ M * |eps|) →
        ‖(highWalsh (radialMeasure tau eps) c -
            highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c) -
          (highWalsh (radialMeasure tau eps) ⟨q, fun _ => 0⟩ -
            highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1))
              ⟨q, fun _ => 0⟩)‖
          ≤ C * eps^2 := by
  exact ShellBounds.high_shell_stability tau M hM

/-- Compactness turns pointwise nonvanishing on the orthogonal group into a
uniform positive lower bound.  We state it directly on frames to avoid choosing
between matrix and column representations in the rest of the development. -/
theorem uniform_scaled_obstruction_lower_bound
    {tau : ℝ}
    (hnz : ∀ q : Fin 4 → E4,
      Tensors.IsONFrame q → Tensors.obstruction tau q ≠ 0) :
    ∃ m : ℝ, 0 < m ∧
      ∀ q : Fin 4 → E4, Tensors.IsONFrame q →
        m ≤ ‖scaledObstruction tau q‖ := by
  let S : Set (Fin 4 → E4) := {q | Tensors.IsONFrame q}
  let P : Set (Fin 4 → E4) :=
    Set.univ.pi (fun _ : Fin 4 => Metric.sphere (0 : E4) 1)
  have hP : IsCompact P := by
    dsimp [P]
    exact isCompact_univ_pi (fun _ => isCompact_sphere (0 : E4) 1)
  have hSclosed : IsClosed S := by
    dsimp [S, Tensors.IsONFrame]
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hSP : S ⊆ P := by
    intro q hq
    dsimp [S] at hq
    dsimp [P]
    rw [Set.mem_pi]
    intro i _
    have hnorm := hq.norm_eq_one i
    simpa [Metric.mem_sphere, dist_zero_right] using hnorm
  have hS : IsCompact S := hP.of_isClosed_subset hSclosed hSP
  have hcontScaled : Continuous (fun q : Fin 4 → E4 => ‖scaledObstruction tau q‖) := by
    unfold scaledObstruction Tensors.obstruction Tensors.A Tensors.A0 Tensors.C Tensors.B Tensors.nForm Tensors.mForm
    fun_prop
  have hpos : ∀ q ∈ S, 0 < ‖scaledObstruction tau q‖ := by
    intro q hq
    apply norm_pos_iff.mpr
    apply scaledObstruction_ne_zero
    exact hnz q hq
  rcases hS.exists_forall_le' hcontScaled.continuousOn hpos with
    ⟨m, hm, hmin⟩
  refine ⟨m, hm, ?_⟩
  intro q hq
  exact hmin q hq

/-- Robust analytic reduction: if the ten low Walsh coefficients are only
`O(eps^2)` rather than exactly zero, the same `eps * L(q) + O(eps^2)` expansion
holds for the five high coefficients. -/
theorem highWalsh_quadratic_expansion_robust
    (tau A : ℝ) (hA : 0 ≤ A) :
    ∃ eps0 C : ℝ, 0 < eps0 ∧ 0 < C ∧
      ∀ eps c,
        |eps| < eps0 → UnitCfg c →
        (∀ I : Walsh4.Index, I.Nonempty → I.card ≤ 2 →
          |walsh (radialMeasure tau eps) c I| ≤ A * eps^2) →
        ∃ q : Fin 4 → E4,
          Tensors.IsONFrame q ∧
          ‖highWalsh (radialMeasure tau eps) c -
            eps • scaledObstruction tau q‖ ≤ C * eps^2 := by
  rcases low_walsh_localization_robust tau A hA with
    ⟨epsL, CL, hepsL, hCL, hloc⟩
  rcases ball_high_quadratic_flatness with
    ⟨delta, CB, hdelta, hCB, hball⟩
  rcases radial_shell_stability tau CL hCL with
    ⟨epsS, CS, hepsS, hCS, hshell⟩
  rcases radial_rhs_positive_small tau with ⟨epsP, hepsP, hpos⟩
  let eps0 : ℝ := min (min (min epsL epsS) (delta / CL)) epsP
  let C : ℝ := CB * CL^2 + CS
  have heps0 : 0 < eps0 := by
    dsimp [eps0]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨eps0, C, heps0, hC, ?_⟩
  intro eps c heps hunit hlow
  have hepsL' : |eps| < epsL := lt_of_lt_of_le heps (by
    dsimp [eps0]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  rcases hloc eps c hepsL' hunit hlow with
    ⟨q, hq, hoff, hnormal⟩
  have hepsS' : |eps| < epsS := lt_of_lt_of_le heps (by
    dsimp [eps0]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hd : CL * |eps| < delta := by
    have hratio : |eps| < delta / CL := lt_of_lt_of_le heps (by
      dsimp [eps0]
      exact (min_le_left _ _).trans (min_le_right _ _))
    calc
      CL * |eps| < CL * (delta / CL) :=
        mul_lt_mul_of_pos_left hratio hCL
      _ = delta := by field_simp [ne_of_gt hCL]
  have hballBound := hball (CL * |eps|) c q
    (mul_nonneg (le_of_lt hCL) (abs_nonneg eps)) hd hunit hq hoff hnormal
  have hshellBound := hshell eps c q hepsS' hunit hq hoff hnormal
  have hepsP' : |eps| < epsP := lt_of_lt_of_le heps (by
    dsimp [eps0]
    exact min_le_right _ _)
  have hcenter :
      highWalsh (radialMeasure tau eps) ⟨q, fun _ => 0⟩ =
        eps • scaledObstruction tau q := by
    apply highWalsh_centered_onFrame tau eps q hq
    intro u hu
    exact (hpos eps hepsP' u hu).le
  have hqUnit : UnitCfg ⟨q, fun _ => 0⟩ := fun i => hq.norm_eq_one i
  have hballCenterBound := hball 0 ⟨q, fun _ => 0⟩ q
    (le_refl 0) hdelta hqUnit hq (by simp) (by simp)
  have hballCenter :
      highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1))
        ⟨q, fun _ => 0⟩ = 0 := by
    have h : ‖highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) ⟨q, fun _ => 0⟩‖ ≤ 0 := by
      simpa using hballCenterBound
    exact norm_le_zero_iff.mp h
  refine ⟨q, hq, ?_⟩
  have hdecomp :
      highWalsh (radialMeasure tau eps) c - eps • scaledObstruction tau q =
        highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c +
        ((highWalsh (radialMeasure tau eps) c -
            highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c) -
          (highWalsh (radialMeasure tau eps) ⟨q, fun _ => 0⟩ -
            highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1))
              ⟨q, fun _ => 0⟩)) := by
    rw [hcenter, hballCenter]
    module
  rw [hdecomp]
  calc
    ‖highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c +
        ((highWalsh (radialMeasure tau eps) c -
            highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c) -
          (highWalsh (radialMeasure tau eps) ⟨q, fun _ => 0⟩ -
            highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1))
              ⟨q, fun _ => 0⟩))‖
        ≤ ‖highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c‖ +
          ‖(highWalsh (radialMeasure tau eps) c -
              highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c) -
            (highWalsh (radialMeasure tau eps) ⟨q, fun _ => 0⟩ -
              highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1))
                ⟨q, fun _ => 0⟩)‖ := norm_add_le _ _
    _ ≤ CB * (CL * |eps|)^2 + CS * eps^2 := add_le_add hballBound hshellBound
    _ = C * eps^2 := by
      dsimp [C]
      rw [mul_pow, sq_abs]
      ring

/-- Exact low equations are the zero-error special case. -/
theorem highWalsh_quadratic_expansion
    (tau : ℝ) :
    ∃ eps0 C : ℝ, 0 < eps0 ∧ 0 < C ∧
      ∀ eps c,
        |eps| < eps0 → UnitCfg c →
        (∀ I : Walsh4.Index, I.Nonempty → I.card ≤ 2 →
          walsh (radialMeasure tau eps) c I = 0) →
        ∃ q : Fin 4 → E4,
          Tensors.IsONFrame q ∧
          ‖highWalsh (radialMeasure tau eps) c -
            eps • scaledObstruction tau q‖ ≤ C * eps^2 := by
  rcases highWalsh_quadratic_expansion_robust tau 0 (le_refl 0) with
    ⟨eps0, C, heps0, hC, hexp⟩
  refine ⟨eps0, C, heps0, hC, ?_⟩
  intro eps c heps hunit hlow
  apply hexp eps c heps hunit
  intro I hI hcard
  rw [hlow I hI hcard, abs_zero, zero_mul]

end SoberonConvexBody
