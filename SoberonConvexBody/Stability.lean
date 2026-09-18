import Mathlib
import SoberonConvexBody.GeometryCore

/-!
# Stability of Walsh coefficients under symmetric difference

For uniform measures on two finite-volume sets, every Walsh coefficient changes
by at most a universal constant times the volume of the symmetric difference.
The proof is reduced to the finite 16-point Walsh transform from `Walsh4.lean`.
-/

noncomputable section

namespace SoberonConvexBody

open Set Real MeasureTheory
open scoped BigOperators

/-- Intersecting two sets with a common test set cannot make their mass
difference larger than the mass of the symmetric difference. -/
theorem abs_measureReal_inter_sub_le_symmDiff
    (μ : Measure E4) {A B C : Set E4}
    (hA : μ A ≠ ⊤) (hB : μ B ≠ ⊤)
    (hSD : μ (symmDiff A B) ≠ ⊤) :
    |μ.real (C ∩ A) - μ.real (C ∩ B)| ≤ μ.real (symmDiff A B) := by
  have hCA : μ (C ∩ A) ≠ ⊤ := by
    have hle : μ (C ∩ A) ≤ μ A := measure_mono inter_subset_right
    exact ne_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hA))
  have hCB : μ (C ∩ B) ≠ ⊤ := by
    have hle : μ (C ∩ B) ≤ μ B := measure_mono inter_subset_right
    exact ne_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hB))
  have hAB : (C ∩ A) \ (C ∩ B) ⊆ symmDiff A B := by
    intro x hx
    rw [Set.mem_symmDiff]
    exact Or.inl ⟨hx.1.2, fun hxB => hx.2 ⟨hx.1.1, hxB⟩⟩
  have hBA : (C ∩ B) \ (C ∩ A) ⊆ symmDiff A B := by
    intro x hx
    rw [Set.mem_symmDiff]
    exact Or.inr ⟨hx.1.2, fun hxA => hx.2 ⟨hx.1.1, hxA⟩⟩
  have hup : μ.real (C ∩ A) - μ.real (C ∩ B) ≤ μ.real (symmDiff A B) :=
    (le_measureReal_sdiff (s₁ := C ∩ A) (s₂ := C ∩ B) hCB).trans
      (measureReal_mono hAB hSD)
  have hlo : μ.real (C ∩ B) - μ.real (C ∩ A) ≤ μ.real (symmDiff A B) :=
    (le_measureReal_sdiff (s₁ := C ∩ B) (s₂ := C ∩ A) hCA).trans
      (measureReal_mono hBA hSD)
  rw [abs_le]
  constructor <;> linarith

/-- Cell masses for restrictions to `A` and `B` differ by at most the volume
of `A ∆ B`. -/
theorem abs_cellMass_restrict_sub_le_symmDiff
    {A B : Set E4} (c : HyperplaneCfg) (s : Walsh4.Pattern)
    (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤)
    (hSD : volume (symmDiff A B) ≠ ⊤) :
    |Cells.cellMass (volume.restrict A) c s -
      Cells.cellMass (volume.restrict B) c s| ≤
      volume.real (symmDiff A B) := by
  have h := abs_measureReal_inter_sub_le_symmDiff volume
    (A := A) (B := B) (C := Cells.cell c s) hA hB hSD
  have h1 : Cells.cellMass (volume.restrict A) c s = volume.real (Cells.cell c s ∩ A) := by
    simp [Cells.cellMass, Measure.real, Measure.restrict_apply (Cells.measurableSet_cell c s)]
  have h2 : Cells.cellMass (volume.restrict B) c s = volume.real (Cells.cell c s ∩ B) := by
    simp [Cells.cellMass, Measure.real, Measure.restrict_apply (Cells.measurableSet_cell c s)]
  rwa [h1, h2]

/-- Stability of the finite Walsh transform.  The factor 16 is intentionally
crude; its value is irrelevant for an `O(eps^2)` argument. -/
theorem abs_cellWalsh_restrict_sub_le_symmDiff
    {A B : Set E4} (c : HyperplaneCfg) (I : Walsh4.Index)
    (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤)
    (hSD : volume (symmDiff A B) ≠ ⊤) :
    |Cells.cellWalsh (volume.restrict A) c I -
      Cells.cellWalsh (volume.restrict B) c I| ≤
      16 * volume.real (symmDiff A B) := by
  classical
  let δ : ℝ := volume.real (symmDiff A B)
  have hδ0 : 0 ≤ δ := by positivity
  have hterm : ∀ s : Walsh4.Pattern,
      |Walsh4.char I s *
        (Cells.cellMass (volume.restrict A) c s -
          Cells.cellMass (volume.restrict B) c s)| ≤ δ := by
    intro s
    rw [abs_mul, Walsh4.abs_char, one_mul]
    exact abs_cellMass_restrict_sub_le_symmDiff c s hA hB hSD
  have hcard : Fintype.card Walsh4.Pattern = 16 := by decide
  unfold Cells.cellWalsh Walsh4.transform
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ s : Walsh4.Pattern,
        (Walsh4.char I s * Cells.cellMass (volume.restrict A) c s -
         Walsh4.char I s * Cells.cellMass (volume.restrict B) c s)|
        = |∑ s : Walsh4.Pattern,
            Walsh4.char I s *
              (Cells.cellMass (volume.restrict A) c s -
               Cells.cellMass (volume.restrict B) c s)| := by
            congr 1
            apply Finset.sum_congr rfl
            intro s _
            ring
    _ ≤ ∑ s : Walsh4.Pattern,
          |Walsh4.char I s *
            (Cells.cellMass (volume.restrict A) c s -
             Cells.cellMass (volume.restrict B) c s)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : Walsh4.Pattern, δ := by
          apply Finset.sum_le_sum
          intro s _
          exact hterm s
    _ = 16 * δ := by
          simp [hcard]
    _ = 16 * volume.real (symmDiff A B) := rfl

/-- Integral Walsh coefficients obey the same symmetric-difference estimate. -/
theorem abs_walsh_restrict_sub_le_symmDiff
    {A B : Set E4} (c : HyperplaneCfg) (I : Walsh4.Index)
    (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤)
    (hSD : volume (symmDiff A B) ≠ ⊤) :
    |walsh (volume.restrict A) c I - walsh (volume.restrict B) c I| ≤
      16 * volume.real (symmDiff A B) := by
  have hAlt : volume A < ⊤ := lt_top_iff_ne_top.mpr hA
  have hBlt : volume B < ⊤ := lt_top_iff_ne_top.mpr hB
  have : Fact (volume A < ⊤) := ⟨hAlt⟩
  have : Fact (volume B < ⊤) := ⟨hBlt⟩
  have : IsFiniteMeasure (volume.restrict A) :=
    MeasureTheory.Restrict.isFiniteMeasure volume
  have : IsFiniteMeasure (volume.restrict B) :=
    MeasureTheory.Restrict.isFiniteMeasure volume
  simp only [walsh]
  rw [Cells.integral_signCharacter_eq_cellWalsh,
    Cells.integral_signCharacter_eq_cellWalsh]
  exact abs_cellWalsh_restrict_sub_le_symmDiff c I hA hB hSD

end SoberonConvexBody
