import Mathlib
import SoberonConvexBody.WulffComparison
import SoberonConvexBody.Stability

/-!
# Second-order volume comparison for the Wulff body

The key observation is that no polar integration is needed to compare the
Wulff body with its first-order radial model.  If

  R(u) = 1 + eps * f(u) / 4

is bounded below by `1/2`, then shrinking the whole radial model by the
homothety factor `1 - 2 D eps^2` lowers every radial radius by at least
`D eps^2`.  Thus

  (1 - 2 D eps^2) • L_eps ⊆ L_eps^- ⊆ K_eps ⊆ L_eps.

Lebesgue measure scales exactly by the fourth power under homotheties, which
immediately gives an `O(eps^2)` symmetric-difference estimate.
-/

noncomputable section

namespace SoberonConvexBody

open Set Real MeasureTheory
open scoped Pointwise

@[simp] theorem direction_zero : direction (0 : E4) = 0 := by
  simp [direction]

@[simp] theorem angularPerturbation_zero (tau : ℝ) :
    angularPerturbation tau (0 : E4) = 0 := by
  simp [angularPerturbation, Tensors.A, Tensors.A0, Tensors.C, Tensors.B,
    Tensors.nForm, Tensors.mForm]

/-- `direction` is Borel measurable.  It is discontinuous only at the origin,
but measurability is all that is needed for the radial sets. -/
theorem measurable_direction : Measurable (direction : E4 → E4) := by
  unfold direction
  fun_prop

/-- The linear first-order radial model is measurable. -/
theorem measurableSet_linearRadialSet (tau eps : ℝ) :
    MeasurableSet (linearRadialSet tau eps) := by
  unfold linearRadialSet
  apply measurableSet_le
  · fun_prop
  · have hf : Measurable (fun x : E4 =>
        angularPerturbation tau (direction x)) :=
      (continuous_angularPerturbation tau).measurable.comp measurable_direction
    fun_prop

/-- The shrunken radial model is measurable. -/
theorem measurableSet_shrunkenLinearRadialSet (tau eps D : ℝ) :
    MeasurableSet (shrunkenLinearRadialSet tau eps D) := by
  unfold shrunkenLinearRadialSet
  apply measurableSet_le
  · fun_prop
  · have hf : Measurable (fun x : E4 =>
        angularPerturbation tau (direction x)) :=
      (continuous_angularPerturbation tau).measurable.comp measurable_direction
    fun_prop

/-- Positive scalar multiplication does not change the radial direction. -/
theorem direction_pos_smul {r : ℝ} (hr : 0 < r) {x : E4} (_hx : x ≠ 0) :
    direction (r • x) = direction x := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  simp [direction, norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul, hr0]

/-- Under a sup-norm bound for the perturbation, every radial radius is at
least `1/2`. -/
theorem linearRadius_ge_half
    {tau eps M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 2) (x : E4) :
    (1 / 2 : ℝ) ≤
      1 + (eps / 4) * angularPerturbation tau (direction x) := by
  by_cases hx : x = 0
  · subst x
    simp only [direction_zero, angularPerturbation_zero, mul_zero, add_zero]
    norm_num
  · have hu : ‖direction x‖ = 1 := norm_direction hx
    have hf := hbound (direction x) hu
    have habs : |eps * angularPerturbation tau (direction x)| ≤ 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hf (abs_nonneg eps)).trans heM
    have hlo : -2 ≤ eps * angularPerturbation tau (direction x) :=
      neg_le_of_abs_le habs
    nlinarith
    
/-- The linear radial model lies in the ball of radius `3/2` under the same
smallness hypothesis. -/
theorem linearRadialSet_subset_closedBall_three_halves
    {tau eps M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 2) :
    linearRadialSet tau eps ⊆ Metric.closedBall (0 : E4) (3 / 2) := by
  intro x hx
  have hRupper :
      1 + (eps / 4) * angularPerturbation tau (direction x) ≤ (3 / 2 : ℝ) := by
    by_cases hx0 : x = 0
    · subst x
      simp only [direction_zero, angularPerturbation_zero, mul_zero, add_zero]
      norm_num
    · have hu : ‖direction x‖ = 1 := norm_direction hx0
      have hf := hbound (direction x) hu
      have habs : |eps * angularPerturbation tau (direction x)| ≤ 2 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hf (abs_nonneg eps)).trans heM
      have hup : eps * angularPerturbation tau (direction x) ≤ 2 :=
        le_of_abs_le habs
      nlinarith
  have hnorm : ‖x‖ ≤ 3 / 2 := hx.trans hRupper
  simpa [Metric.mem_closedBall, dist_zero_right] using hnorm

/-- A global homothety of factor `1 - 2 D eps^2` fits inside the radially
shrunken model.  This is the step that replaces a variable-radius polar volume
calculation. -/
theorem smul_linearRadialSet_subset_shrunken
    {tau eps M D : ℝ} (_hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 2)
    (hdelta : 2 * D * eps^2 < 1) :
    (1 - 2 * D * eps^2) • linearRadialSet tau eps ⊆
      shrunkenLinearRadialSet tau eps D := by
  let r : ℝ := 1 - 2 * D * eps^2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hr1 : r ≤ 1 := by
    dsimp [r]
    nlinarith [sq_nonneg eps]
  intro y hy
  rcases (Set.mem_smul_set).mp hy with ⟨x, hx, rfl⟩
  by_cases hx0 : x = 0
  · subst x
    simp [shrunkenLinearRadialSet, direction_zero, angularPerturbation_zero]
    nlinarith [sq_nonneg eps]
  · have hdir : direction (r • x) = direction x := direction_pos_smul hr hx0
    have hscale : ‖r • x‖ ≤ r * (1 + (eps / 4) * angularPerturbation tau (direction x)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hx (le_of_lt hr)
    have hRhalf := linearRadius_ge_half (M := M) (by positivity) hbound heM x
    have hdrop :
        r * (1 + (eps / 4) * angularPerturbation tau (direction x)) ≤
          1 + (eps / 4) * angularPerturbation tau (direction x) - D * eps^2 := by
      dsimp [r]
      have :
          (1 - 2 * D * eps^2) * (1 + (eps / 4) * angularPerturbation tau (direction x)) =
            (1 + (eps / 4) * angularPerturbation tau (direction x)) -
              2 * D * eps^2 * (1 + (eps / 4) * angularPerturbation tau (direction x)) := by ring
      rw [this]
      have : D * eps^2 ≤ 2 * D * eps^2 * (1 + (eps / 4) * angularPerturbation tau (direction x)) := by
        calc
          D * eps^2 = 2 * D * eps^2 * (1 / 2) := by ring
          _ ≤ 2 * D * eps^2 * (1 + (eps / 4) * angularPerturbation tau (direction x)) := by
            have hcoeff : 0 ≤ 2 * D * eps^2 := by positivity
            exact mul_le_mul_of_nonneg_left hRhalf hcoeff
      linarith
    show ‖r • x‖ ≤
      1 + (eps / 4) * angularPerturbation tau (direction (r • x)) - D * eps^2
    rw [hdir]
    exact hscale.trans hdrop

/-- Real-valued form of Haar scaling in dimension four. -/
theorem volumeReal_smul_E4
    {r : ℝ} (hr : 0 ≤ r) (A : Set E4) (_hA : volume A ≠ ⊤) :
    volume.real (r • A) = r^4 * volume.real A := by
  have hdim : Module.finrank ℝ E4 = 4 := by
    simp [E4]
  dsimp [Measure.real]
  rw [volume.addHaar_smul_of_nonneg hr A, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), hdim]

/-- A simple polynomial estimate for the loss of four-dimensional volume under
`(1-delta)`-homothety. -/
theorem one_sub_one_sub_pow_four_le
    {delta : ℝ} (_h0 : 0 ≤ delta) (_h1 : delta ≤ 1) :
    1 - (1 - delta)^4 ≤ 4 * delta := by
  have hq : 0 ≤ delta^2 * (6 - 4 * delta + delta^2) := by
    have hpoly : 0 ≤ 6 - 4 * delta + delta^2 := by
      nlinarith [sq_nonneg (delta - 2)]
    exact mul_nonneg (sq_nonneg delta) hpoly
  nlinarith

/-- If `B ⊆ A`, their symmetric difference is simply `A \ B`. -/
theorem symmDiff_eq_sdiff_of_subset {A B : Set E4} (hBA : B ⊆ A) :
    symmDiff A B = A \ B := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_symmDiff] at hx
    rcases hx with hx | hx
    · exact hx
    · exact False.elim (hx.2 (hBA hx.1))
  · intro hx
    rw [Set.mem_symmDiff]
    exact Or.inl hx

/-- Any set lying between the shrunken and unshrunk linear radial models
has `O(eps^2)` symmetric difference from the latter.  This is the generic
homothety lemma used both for the Wulff body and for Soberon's exact radial
model. -/
theorem sandwichedSet_symmDiff_linearRadialSet_le
    {B : Set E4} {tau eps M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 2)
    (hdelta : 2 * D * eps^2 < 1)
    (hinner : shrunkenLinearRadialSet tau eps D ⊆ B)
    (houter : B ⊆ linearRadialSet tau eps) :
    volume.real (symmDiff B (linearRadialSet tau eps)) ≤
      8 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by
  let A : Set E4 := linearRadialSet tau eps
  let r : ℝ := 1 - 2 * D * eps^2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hr0 : 0 ≤ r := le_of_lt hr
  have hr1 : r ≤ 1 := by
    dsimp [r]
    nlinarith [mul_nonneg hD (sq_nonneg eps)]
  have hscale_inner : r • A ⊆ B := by
    dsimp [A, r]
    exact (smul_linearRadialSet_subset_shrunken hM hD hbound heM hdelta).trans hinner
  have hscaleA : r • A ⊆ A := hscale_inner.trans houter
  have hAmeas : MeasurableSet A := measurableSet_linearRadialSet tau eps
  have hscaleMeas : MeasurableSet (r • A) :=
    hAmeas.const_smul_of_ne_zero (ne_of_gt hr)
  have hball : A ⊆ Metric.closedBall (0 : E4) (3 / 2) :=
    linearRadialSet_subset_closedBall_three_halves hM hbound heM
  have hballfin : volume (Metric.closedBall (0 : E4) (3 / 2)) ≠ ⊤ :=
    (isCompact_closedBall (0 : E4) (3 / 2)).measure_ne_top
  have hAfin : volume A ≠ ⊤ :=
    measure_ne_top_of_subset hball hballfin
  have hsdiff_subset : A \ B ⊆ A \ (r • A) := by
    intro x hx
    exact ⟨hx.1, fun hs => hx.2 (hscale_inner hs)⟩
  have hsdiffFin : volume (A \ (r • A)) ≠ ⊤ :=
    measure_ne_top_of_subset sdiff_subset hAfin
  have hmeasure_sdiff :
      volume.real (A \ (r • A)) =
        (1 - r^4) * volume.real A := by
    have hadd := measureReal_inter_add_sdiff
      (μ := volume) (s := A) (t := r • A) hscaleMeas hAfin
    have hinter : A ∩ (r • A) = r • A := inter_eq_right.mpr hscaleA
    rw [hinter, volumeReal_smul_E4 hr0 A hAfin] at hadd
    nlinarith
  have hdelta0 : 0 ≤ 2 * D * eps^2 := by positivity
  have hdelta1 : 2 * D * eps^2 ≤ 1 := le_of_lt hdelta
  have hpoly : 1 - r^4 ≤ 8 * D * eps^2 := by
    dsimp [r]
    have := one_sub_one_sub_pow_four_le hdelta0 hdelta1
    nlinarith
  have hAvol : volume.real A ≤
      volume.real (Metric.closedBall (0 : E4) (3 / 2)) :=
    measureReal_mono hball hballfin
  have hnonneg : 0 ≤ 1 - r^4 := by
    have hrpow : r^4 ≤ 1 := pow_le_one₀ (le_of_lt hr) hr1
    linarith
  have hvolbound : volume.real (A \ (r • A)) ≤
      8 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by
    rw [hmeasure_sdiff]
    have h2 := mul_le_mul_of_nonneg_left hAvol hnonneg
    calc
      (1 - r^4) * volume.real A
          ≤ (1 - r^4) * volume.real (Metric.closedBall (0 : E4) (3 / 2)) := h2
      _ ≤ (8 * D * eps^2) *
          volume.real (Metric.closedBall (0 : E4) (3 / 2)) :=
            mul_le_mul_of_nonneg_right hpoly measureReal_nonneg
      _ = 8 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by ring
  rw [symmDiff_comm, symmDiff_eq_sdiff_of_subset houter]
  exact (measureReal_mono hsdiff_subset hsdiffFin).trans hvolbound

/-- The Wulff body differs from the first-order radial model by only
`O(eps^2)` volume. -/
theorem supportBody_symmDiff_linearRadialSet_le
    {tau eps M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 2)
    (hdelta : 2 * D * eps^2 < 1)
    (hinner : shrunkenLinearRadialSet tau eps D ⊆ supportBody tau eps)
    (houter : supportBody tau eps ⊆ linearRadialSet tau eps) :
    volume.real (symmDiff (supportBody tau eps) (linearRadialSet tau eps)) ≤
      8 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 :=
  sandwichedSet_symmDiff_linearRadialSet_le
    hM hD hbound heM hdelta hinner houter

/-- Consequently every Walsh coefficient of the Wulff body differs from that
of the first-order radial model by `O(eps^2)`. -/
theorem supportBody_walsh_linearRadialSet_le
    {tau eps M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    (heM : |eps| * M ≤ 2)
    (hdelta : 2 * D * eps^2 < 1)
    (hinner : shrunkenLinearRadialSet tau eps D ⊆ supportBody tau eps)
    (houter : supportBody tau eps ⊆ linearRadialSet tau eps)
    (c : HyperplaneCfg) (I : Walsh4.Index) :
    |walsh (supportMeasure tau eps) c I -
      walsh (volume.restrict (linearRadialSet tau eps)) c I| ≤
      128 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by
  have hlin_ball := linearRadialSet_subset_closedBall_three_halves hM hbound heM
  have hballfin : volume (Metric.closedBall (0 : E4) (3 / 2)) ≠ ⊤ :=
    (isCompact_closedBall (0 : E4) (3 / 2)).measure_ne_top
  have hlinfin : volume (linearRadialSet tau eps) ≠ ⊤ :=
    measure_ne_top_of_subset hlin_ball hballfin
  have hsupfin : volume (supportBody tau eps) ≠ ⊤ :=
    measure_ne_top_of_subset houter hlinfin
  have hsymfin : volume (symmDiff (supportBody tau eps)
      (linearRadialSet tau eps)) ≠ ⊤ := by
    have hsub : symmDiff (supportBody tau eps) (linearRadialSet tau eps) ⊆
        linearRadialSet tau eps := by
      rw [symmDiff_comm, symmDiff_eq_sdiff_of_subset houter]
      exact sdiff_subset
    exact measure_ne_top_of_subset hsub hlinfin
  have hstable := abs_walsh_restrict_sub_le_symmDiff
    (A := supportBody tau eps) (B := linearRadialSet tau eps) c I
    hsupfin hlinfin hsymfin
  have hvol := supportBody_symmDiff_linearRadialSet_le
    hM hD hbound heM hdelta hinner houter
  unfold supportMeasure
  calc
    |walsh (volume.restrict (supportBody tau eps)) c I -
      walsh (volume.restrict (linearRadialSet tau eps)) c I|
        ≤ 16 * volume.real (symmDiff (supportBody tau eps)
            (linearRadialSet tau eps)) := hstable
    _ ≤ 16 *
        (8 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2) :=
          mul_le_mul_of_nonneg_left hvol (by norm_num)
    _ = 128 * D * volume.real (Metric.closedBall (0 : E4) (3 / 2)) * eps^2 := by ring

end SoberonConvexBody
