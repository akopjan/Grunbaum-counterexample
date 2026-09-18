import SoberonConvexBody.Main

/-!
# Bridge from the internal unit-normal theorem to the literal statement

The main development parametrizes affine hyperplanes by unit normals. The
literal statement deliberately quantifies over arbitrary vectors. If one of
those vectors is zero, one of the two associated halfspaces is empty. If all
are nonzero, positive rescaling normalizes every normal without changing any
of the sixteen cells.
-/

noncomputable section

namespace SoberonConvexBody

open Set Real MeasureTheory

private def rawCell
    (u : Fin 4 → E4) (t : Fin 4 → ℝ) (s : Fin 4 → Bool) : Set E4 :=
  {x : E4 |
    ∀ i,
      if s i then
        t i ≤ inner ℝ x (u i)
      else
        inner ℝ x (u i) < t i}

private def normalizedCfg (u : Fin 4 → E4) (t : Fin 4 → ℝ) : HyperplaneCfg where
  normal i := (‖u i‖)⁻¹ • u i
  offset i := t i / ‖u i‖

private theorem normalizedCfg_unit
    (u : Fin 4 → E4) (t : Fin 4 → ℝ) (hu : ∀ i, u i ≠ 0) :
    UnitCfg (normalizedCfg u t) := by
  intro i
  have hn : 0 < ‖u i‖ := norm_pos_iff.mpr (hu i)
  change ‖(‖u i‖)⁻¹ • u i‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  field_simp [hn.ne']

private theorem normalized_positive_iff
    (u : Fin 4 → E4) (t : Fin 4 → ℝ) (hu : ∀ i, u i ≠ 0)
    (i : Fin 4) (x : E4) :
    (normalizedCfg u t).offset i ≤ inner ℝ x ((normalizedCfg u t).normal i) ↔
      t i ≤ inner ℝ x (u i) := by
  have hn : 0 < ‖u i‖ := norm_pos_iff.mpr (hu i)
  change t i / ‖u i‖ ≤ inner ℝ x ((‖u i‖)⁻¹ • u i) ↔ _
  rw [real_inner_smul_right]
  rw [show (‖u i‖)⁻¹ * inner ℝ x (u i) = inner ℝ x (u i) / ‖u i‖ by
    rw [div_eq_mul_inv]
    ring]
  exact div_le_div_iff_of_pos_right hn

private theorem normalized_negative_iff
    (u : Fin 4 → E4) (t : Fin 4 → ℝ) (hu : ∀ i, u i ≠ 0)
    (i : Fin 4) (x : E4) :
    inner ℝ x ((normalizedCfg u t).normal i) < (normalizedCfg u t).offset i ↔
      inner ℝ x (u i) < t i := by
  have hn : 0 < ‖u i‖ := norm_pos_iff.mpr (hu i)
  change inner ℝ x ((‖u i‖)⁻¹ • u i) < t i / ‖u i‖ ↔ _
  rw [real_inner_smul_right]
  rw [show (‖u i‖)⁻¹ * inner ℝ x (u i) = inner ℝ x (u i) / ‖u i‖ by
    rw [div_eq_mul_inv]
    ring]
  exact div_lt_div_iff_of_pos_right hn

private theorem normalized_cell_eq
    (u : Fin 4 → E4) (t : Fin 4 → ℝ) (hu : ∀ i, u i ≠ 0)
    (s : Fin 4 → Bool) :
    Cells.cell (normalizedCfg u t) s = rawCell u t s := by
  ext x
  simp only [Cells.cell, rawCell, Set.mem_ofPred_eq]
  constructor
  · intro hx i
    have hi := congrFun hx i
    cases hsi : s i with
    | false =>
        have hlt :
            inner ℝ x ((normalizedCfg u t).normal i) <
              (normalizedCfg u t).offset i := by
          simpa [Cells.pattern, hsi] using hi
        simpa [hsi] using (normalized_negative_iff u t hu i x).mp hlt
    | true =>
        have hle :
            (normalizedCfg u t).offset i ≤
              inner ℝ x ((normalizedCfg u t).normal i) := by
          simpa [Cells.pattern, hsi] using hi
        simpa [hsi] using (normalized_positive_iff u t hu i x).mp hle
  · intro hx
    ext i
    cases hsi : s i with
    | false =>
        have hlt := (hx i)
        rw [hsi] at hlt
        dsimp at hlt
        have hlt' := (normalized_negative_iff u t hu i x).mpr hlt
        simpa [Cells.pattern, hsi] using hlt'
    | true =>
        have hle := (hx i)
        rw [hsi] at hle
        dsimp at hle
        have hle' := (normalized_positive_iff u t hu i x).mpr hle
        simpa [Cells.pattern, hsi] using hle'

private theorem volume_real_pos_of_interior_nonempty
    (K : ConvexBody E4) (hK : (interior (K : Set E4)).Nonempty) :
    0 < volume.real (K : Set E4) := by
  have hinterior : 0 < volume (interior (K : Set E4)) :=
    isOpen_interior.measure_pos volume hK
  have hpositive : 0 < volume (K : Set E4) :=
    lt_of_lt_of_le hinterior (measure_mono interior_subset)
  have hfinite : volume (K : Set E4) ≠ ⊤ :=
    ne_of_lt K.isCompact.measure_lt_top
  exact ENNReal.toReal_pos hpositive.ne' hfinite

theorem noEquipartition_of_convex_body_counterexample
    (K : ConvexBody E4) (hKint : (interior (K : Set E4)).Nonempty)
    (hno : NoEquipartition (K : Set E4))
    (u : Fin 4 → E4) (t : Fin 4 → ℝ) :
    ¬ (∀ s : Fin 4 → Bool,
        volume.real ((K : Set E4) ∩
          {x | ∀ i, if s i = true then t i ≤ inner ℝ x (u i)
                    else inner ℝ x (u i) < t i}) =
          volume.real (K : Set E4) / 16) := by
  intro hcells
  have hcells' : ∀ s,
      volume.real ((K : Set E4) ∩ rawCell u t s) =
        volume.real (K : Set E4) / 16 := by
    intro s
    simpa [rawCell] using hcells s
  by_cases hu : ∀ i, u i ≠ 0
  · let c : HyperplaneCfg := normalizedCfg u t
    have hc : UnitCfg c := by
      simpa [c] using normalizedCfg_unit u t hu
    apply hno c hc
    intro s
    have hcell : Cells.cell c s = rawCell u t s := by
      simpa [c] using normalized_cell_eq u t hu s
    have hmeas : MeasurableSet (rawCell u t s) := by
      rw [← hcell]
      exact Cells.measurableSet_cell c s
    calc
      Cells.cellMass (volume.restrict (K : Set E4)) c s
          = volume.real ((K : Set E4) ∩ rawCell u t s) := by
              rw [Cells.cellMass, hcell, measureReal_restrict_apply hmeas, Set.inter_comm]
      _ = volume.real (K : Set E4) / 16 := hcells' s
      _ = (volume.restrict (K : Set E4)).real Set.univ / 16 := by
            simp [Measure.real, Measure.restrict_apply]
  · push Not at hu
    rcases hu with ⟨i, hi⟩
    have hvol : 0 < volume.real (K : Set E4) :=
      volume_real_pos_of_interior_nonempty K hKint
    by_cases ht : t i ≤ 0
    · let s : Fin 4 → Bool := fun _ => false
      have hempty : rawCell u t s = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxi := hx i
        have hlt : (0 : ℝ) < t i := by
          simpa [rawCell, s, hi] using hxi
        exact (not_lt_of_ge ht) hlt
      have hs := hcells' s
      rw [hempty] at hs
      simp at hs
      nlinarith
    · have htpos : 0 < t i := lt_of_not_ge ht
      let s : Fin 4 → Bool := fun _ => true
      have hempty : rawCell u t s = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxi := hx i
        have hle : t i ≤ (0 : ℝ) := by
          simpa [rawCell, s, hi] using hxi
        exact (not_le_of_gt htpos) hle
      have hs := hcells' s
      rw [hempty] at hs
      simp at hs
      nlinarith

end SoberonConvexBody
