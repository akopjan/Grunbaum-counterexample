import Mathlib
import SoberonConvexBody.SupportExpansion
import SoberonConvexBody.Cells

noncomputable section

namespace SoberonConvexBody

open Set Real MeasureTheory

/-- All 15 non-trivial Walsh coefficients vanish. -/
def EquipartitionWalsh (μ : Measure E4) (c : HyperplaneCfg) : Prop :=
  ∀ I : Walsh4.Index, I.Nonempty → walsh μ c I = 0

/-- Equal masses of the sixteen actual sign cells imply all fifteen Walsh
conditions.  This is exactly the finite Fourier calculation in `Cells.lean`. -/
theorem equipartitionWalsh_of_equalCellMasses
    (μ : Measure E4) [IsFiniteMeasure μ] (c : HyperplaneCfg)
    (h : Cells.EqualCellMasses μ c) : EquipartitionWalsh μ c := by
  have hcell : ∀ I : Walsh4.Index, I.Nonempty → Cells.cellWalsh μ c I = 0 :=
    (Cells.equalCellMasses_iff_cellWalsh_zero μ c).mp h
  intro I hI
  rw [walsh, Cells.integral_signCharacter_eq_cellWalsh]
  exact hcell I hI

/-- The original geometric statement: no four unit-normal affine hyperplanes
cut the body into sixteen equal-volume sign cells. -/
def NoEquipartition (K : Set E4) : Prop :=
  ∀ c, UnitCfg c → ¬ Cells.EqualCellMasses (volume.restrict K) c

/-- Final quantitative contradiction, abstracted from the particular measure.
Only the first-order obstruction and a quadratic remainder enter here. -/
theorem no_equipartitionWalsh_of_expansion
    {μ : Measure E4} {tau eps C m : ℝ}
    (heps : eps ≠ 0)
    (_hC : 0 < C) (_hm : 0 < m)
    (hbound : ∀ q : Fin 4 → E4, Tensors.IsONFrame q →
      m ≤ ‖scaledObstruction tau q‖)
    (hexp : ∀ c,
      UnitCfg c →
      (∀ I : Walsh4.Index, I.Nonempty → I.card ≤ 2 →
        walsh μ c I = 0) →
      ∃ q : Fin 4 → E4,
        Tensors.IsONFrame q ∧
        ‖highWalsh μ c - eps • scaledObstruction tau q‖ ≤ C * eps^2)
    (hnum : C * |eps| < m) :
    ∀ c, UnitCfg c → ¬ EquipartitionWalsh μ c := by
  intro c hunit heq
  have hlow : ∀ I : Walsh4.Index, I.Nonempty → I.card ≤ 2 →
      walsh μ c I = 0 := by
    intro I hI _
    exact heq I hI
  rcases hexp c hunit hlow with ⟨q, hq, hrem⟩
  have hhighzero : highWalsh μ c = 0 := by
    ext i
    fin_cases i
    · simp only [highWalsh, PiLp.toLp_apply]
      exact heq {1, 2, 3} (by decide)
    · simp only [highWalsh, PiLp.toLp_apply]
      exact heq {0, 2, 3} (by decide)
    · simp only [highWalsh, PiLp.toLp_apply]
      exact heq {0, 1, 3} (by decide)
    · simp only [highWalsh, PiLp.toLp_apply]
      exact heq {0, 1, 2} (by decide)
    · simp only [highWalsh, PiLp.toLp_apply]
      exact heq {0, 1, 2, 3} (by decide)
  rw [hhighzero, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs] at hrem
  have hmain : |eps| * m ≤ C * eps^2 :=
    (mul_le_mul_of_nonneg_left (hbound q hq) (abs_nonneg eps)).trans hrem
  have hepspos : 0 < |eps| := abs_pos.mpr heps
  have hsquare : eps^2 = |eps|^2 := by nlinarith [sq_abs eps]
  rw [hsquare] at hmain
  have : m ≤ C * |eps| := by nlinarith
  linarith

/-- Convex-body consequence of Soberon's tensor obstruction, stated for
literal equality of the sixteen cell volumes.  The body used in this theorem
is the Wulff body `supportBody tau eps`, hence convex by construction. -/
theorem exists_convex_body_counterexample :
    ∃ K : ConvexBody E4,
      (interior (K : Set E4)).Nonempty ∧ NoEquipartition (K : Set E4) := by
  rcases Tensors.exists_tau_obstruction_nonzero with ⟨tau, htau, hnz⟩
  rcases uniform_scaled_obstruction_lower_bound hnz with ⟨m, hm, hbound⟩
  rcases highWalsh_support_quadratic_expansion tau with
    ⟨epsA, C, hepsA, hC, hexp⟩
  rcases supportBody_is_convexBody tau with ⟨epsK, hepsK, hK⟩
  let eps : ℝ := min (min (epsA / 2) (epsK / 2)) (m / (2 * C))
  have heps_pos : 0 < eps := by
    dsimp [eps]
    positivity
  have heps_ne : eps ≠ 0 := ne_of_gt heps_pos
  have habs : |eps| = eps := abs_of_pos heps_pos
  have hA : |eps| < epsA := by
    rw [habs]
    dsimp [eps]
    have hle1 : min (min (epsA / 2) (epsK / 2)) (m / (2 * C)) ≤
        min (epsA / 2) (epsK / 2) := min_le_left _ _
    have hle2 : min (epsA / 2) (epsK / 2) ≤ epsA / 2 := min_le_left _ _
    linarith
  have hKsmall : |eps| < epsK := by
    rw [habs]
    dsimp [eps]
    have hle1 : min (min (epsA / 2) (epsK / 2)) (m / (2 * C)) ≤
        min (epsA / 2) (epsK / 2) := min_le_left _ _
    have hle2 : min (epsA / 2) (epsK / 2) ≤ epsK / 2 := min_le_right _ _
    linarith
  have hnum : C * |eps| < m := by
    rw [habs]
    dsimp [eps]
    have hle : min (min (epsA / 2) (epsK / 2)) (m / (2 * C)) ≤
        m / (2 * C) := min_le_right _ _
    have hC0 : C ≠ 0 := ne_of_gt hC
    calc
      C * min (min (epsA / 2) (epsK / 2)) (m / (2 * C))
          ≤ C * (m / (2 * C)) := mul_le_mul_of_nonneg_left hle (le_of_lt hC)
      _ = m / 2 := by field_simp [hC0]
      _ < m := by linarith
  rcases hK eps hKsmall with ⟨K, hKset, hinterior⟩
  refine ⟨K, hinterior, ?_⟩
  intro c hunit hcells
  have hKfinite : volume (K : Set E4) < ⊤ := K.isCompact.measure_lt_top
  let : Fact (volume (K : Set E4) < ⊤) := ⟨hKfinite⟩
  let : IsFiniteMeasure (volume.restrict (K : Set E4)) :=
    MeasureTheory.Restrict.isFiniteMeasure volume
  have hwalshK : EquipartitionWalsh (volume.restrict (K : Set E4)) c :=
    equipartitionWalsh_of_equalCellMasses _ c hcells
  have hNo := no_equipartitionWalsh_of_expansion
    (μ := supportMeasure tau eps) (tau := tau) (eps := eps) (C := C) (m := m)
    heps_ne hC hm hbound
    (by
      intro c' hu hl
      exact hexp eps c' hA hu hl)
    hnum c hunit
  apply hNo
  simpa [supportMeasure, hKset] using hwalshK

end SoberonConvexBody
