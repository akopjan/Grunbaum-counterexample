import Mathlib
import SoberonConvexBody.Walsh4

/-!
# Sign cells and the finite Walsh criterion

This module separates the combinatorial meaning of the fifteen Walsh equations
from all geometry.  A boundary point is assigned to the positive side of each
oriented hyperplane, so the sixteen sign cells are literally disjoint and cover
all of space; no null-boundary hypothesis is needed for the partition itself.
-/

noncomputable section

namespace SoberonConvexBody
namespace Cells

open Set MeasureTheory
open scoped BigOperators

abbrev E4 := EuclideanSpace ℝ (Fin 4)

structure HyperplaneCfg where
  normal : Fin 4 → E4
  offset : Fin 4 → ℝ

/-- Boolean sign pattern. `true` means the closed positive side. -/
def pattern (c : HyperplaneCfg) (x : E4) : Walsh4.Pattern :=
  fun i => decide (¬ inner ℝ x (c.normal i) < c.offset i)

/-- The cell with prescribed sign pattern. -/
def cell (c : HyperplaneCfg) (s : Walsh4.Pattern) : Set E4 :=
  {x | pattern c x = s}

/-- Real mass of a cell. -/
def cellMass (μ : Measure E4) (c : HyperplaneCfg) (s : Walsh4.Pattern) : ℝ :=
  μ.real (cell c s)

/-- The geometric equipartition statement: every one of the sixteen sign cells
has one sixteenth of the total mass. -/
def EqualCellMasses (μ : Measure E4) (c : HyperplaneCfg) : Prop :=
  ∀ s : Walsh4.Pattern, cellMass μ c s = μ.real Set.univ / 16

/-- The cells are pairwise disjoint because `pattern c x` is a function. -/
theorem cell_disjoint {c : HyperplaneCfg} {s t : Walsh4.Pattern} (hst : s ≠ t) :
    Disjoint (cell c s) (cell c t) := by
  rw [Set.disjoint_left]
  intro x hxs hxt
  exact hst (hxs.symm.trans hxt)

/-- Every point belongs to the cell indexed by its own sign pattern. -/
theorem mem_cell_pattern (c : HyperplaneCfg) (x : E4) :
    x ∈ cell c (pattern c x) := rfl

/-- The sixteen cells cover the ambient space. -/
theorem iUnion_cell (c : HyperplaneCfg) :
    (⋃ s : Walsh4.Pattern, cell c s) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨pattern c x, rfl⟩

/-- Each cell is a finite intersection of measurable halfspaces. -/
theorem measurableSet_cell (c : HyperplaneCfg) (s : Walsh4.Pattern) :
    MeasurableSet (cell c s) := by
  classical
  have heq : cell c s = ⋂ i : Fin 4, {x : E4 | pattern c x i = s i} := by
    ext x
    simp only [cell, Set.mem_setOf_eq, Set.mem_iInter, funext_iff]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  cases h : s i with
  | false =>
      simpa [pattern, h] using
        (isOpen_lt (show Continuous (fun x : E4 => inner Real x (c.normal i)) by
          fun_prop) continuous_const).measurableSet
  | true =>
      simpa [pattern, h, not_lt] using
        (isClosed_le continuous_const
          (show Continuous (fun x : E4 => inner Real x (c.normal i)) by
            fun_prop)).measurableSet

/-- Character attached to the sign pattern of a point. -/
def signCharacter (c : HyperplaneCfg) (I : Walsh4.Index) (x : E4) : ℝ :=
  Walsh4.char I (pattern c x)

/-- The Walsh coefficient computed from the sixteen cell masses. -/
def cellWalsh (μ : Measure E4) (c : HyperplaneCfg) (I : Walsh4.Index) : ℝ :=
  Walsh4.transform (cellMass μ c) I

/-- Finite additivity obtained by integrating the indicator partition. -/
theorem sum_cellMass
    (mu : Measure E4) [IsFiniteMeasure mu] (c : HyperplaneCfg) :
    (∑ s : Walsh4.Pattern, cellMass mu c s) = mu.real Set.univ := by
  classical
  let F : Walsh4.Pattern -> E4 -> Real := fun s =>
    (cell c s).indicator (fun _ => 1)
  have hF (s : Walsh4.Pattern) : Integrable (F s) mu :=
    (integrable_const (1 : Real)).indicator (measurableSet_cell c s)
  have hpartition : (fun x => ∑ s : Walsh4.Pattern, F s x) = fun _ => 1 := by
    funext x
    calc
      (∑ s : Walsh4.Pattern, F s x) = F (pattern c x) x := by
        apply Finset.sum_eq_single
        · intro s _ hs
          simp [F, cell, Ne.symm hs]
        · simp
      _ = 1 := by simp [F, cell]
  calc
    (∑ s : Walsh4.Pattern, cellMass mu c s) =
        ∑ s : Walsh4.Pattern, ∫ x, F s x ∂ mu := by
      apply Finset.sum_congr rfl
      intro s _
      simp [F, integral_indicator (measurableSet_cell c s), cellMass]
    _ = ∫ x, (∑ s : Walsh4.Pattern, F s x) ∂ mu :=
      (integral_finsetSum Finset.univ (fun s _ => hF s)).symm
    _ = ∫ _x : E4, (1 : Real) ∂ mu := by rw [hpartition]
    _ = mu.real Set.univ := by simp

/-- Integrating the pointwise sign character equals the finite Walsh transform
of the sixteen cell masses.  This is a finite simple-function integral. -/
theorem integral_signCharacter_eq_cellWalsh
    (μ : Measure E4) [IsFiniteMeasure μ] (c : HyperplaneCfg) (I : Walsh4.Index) :
    (∫ x, signCharacter c I x ∂μ) = cellWalsh μ c I := by
  classical
  let F : Walsh4.Pattern → E4 → ℝ := fun s =>
    (cell c s).indicator (fun _ => Walsh4.char I s)
  have hpoint : (fun x => signCharacter c I x) = fun x => ∑ s, F s x := by
    funext x
    rw [Finset.sum_eq_single (pattern c x)]
    · simp [F, signCharacter, cell]
    · intro s _ hne
      simp [F, cell, hne.symm]
    · simp
  rw [hpoint]
  rw [MeasureTheory.integral_finsetSum]
  · simp only [F, MeasureTheory.integral_indicator (measurableSet_cell c _)]
    simp [cellWalsh, Walsh4.transform, cellMass, mul_comm]
  · intro s _
    exact (integrable_const (Walsh4.char I s)).indicator (measurableSet_cell c s)

/-- Exact finite-Fourier characterization of sixteen equal cell masses. -/
theorem equalCellMasses_iff_cellWalsh_zero
    (μ : Measure E4) [IsFiniteMeasure μ] (c : HyperplaneCfg) :
    EqualCellMasses μ c ↔
      ∀ I : Walsh4.Index, I.Nonempty → cellWalsh μ c I = 0 := by
  unfold EqualCellMasses cellWalsh
  exact Walsh4.all_equal_iff_nontrivial_transform_zero
    (cellMass μ c) (μ.real Set.univ) (sum_cellMass μ c)

end Cells
end SoberonConvexBody
