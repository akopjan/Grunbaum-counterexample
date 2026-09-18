import Mathlib

/-!
# The 4-bit Walsh transform

This file isolates the finite Fourier algebra used by the hyperplane
partition argument.  It contains no geometric or measure-theoretic input.

The key point is that for four signs, equality of all 16 cell masses is
exactly equivalent to vanishing of the 15 non-trivial Walsh coefficients,
provided the trivial coefficient is the total mass.
-/

noncomputable section

namespace SoberonConvexBody
namespace Walsh4

open scoped BigOperators

set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev Pattern := Fin 4 → Bool
abbrev Index := Finset (Fin 4)

/-- The ±1 character of the Boolean cube associated with `I`. -/
def charZ (I : Index) (s : Pattern) : ℤ :=
  ∏ i ∈ I, if s i then 1 else -1

/-- The same character, viewed as a real number. -/
def char (I : Index) (s : Pattern) : ℝ := (charZ I s : ℝ)

@[simp] theorem charZ_empty (s : Pattern) : charZ ∅ s = 1 := by
  simp [charZ]

@[simp] theorem char_empty (s : Pattern) : char ∅ s = 1 := by
  simp [char, charZ]

/-- Integer-valued Walsh characters are always `+1` or `-1`. -/
theorem charZ_eq_one_or_neg_one :
    ∀ I : Index, ∀ s : Pattern, charZ I s = 1 ∨ charZ I s = -1 := by
  decide

/-- Every Boolean Walsh character has absolute value one. -/
@[simp] theorem abs_char (I : Index) (s : Pattern) : |char I s| = 1 := by
  rcases charZ_eq_one_or_neg_one I s with h | h <;> simp [char, h]

/-- A closed finite identity: every non-trivial character sums to zero. -/
theorem charZ_sum_nonempty :
    ∀ I : Index, I.Nonempty → (∑ s : Pattern, charZ I s) = 0 := by
  decide

/-- Orthogonality of the 16 Walsh characters. -/
theorem charZ_orthogonality :
    ∀ s t : Pattern,
      (∑ I : Index, charZ I s * charZ I t) = if s = t then 16 else 0 := by
  decide

/-- The Walsh transform of a real-valued function on the Boolean cube. -/
def transform (m : Pattern → ℝ) (I : Index) : ℝ :=
  ∑ s : Pattern, char I s * m s

@[simp] theorem transform_empty (m : Pattern → ℝ) :
    transform m ∅ = ∑ s : Pattern, m s := by
  simp [transform, char]

/-- Real form of character orthogonality. -/
theorem char_orthogonality (s t : Pattern) :
    (∑ I : Index, char I s * char I t) = if s = t then 16 else 0 := by
  have h := charZ_orthogonality s t
  change (∑ I : Index, ((charZ I s : ℝ) * (charZ I t : ℝ))) = if s = t then (16 : ℝ) else 0
  norm_cast
  rw [h]
  split_ifs <;> rfl

/-- Walsh inversion on the 4-dimensional Boolean cube. -/
theorem inversion (m : Pattern → ℝ) (s : Pattern) :
    m s = (1 / 16 : ℝ) * ∑ I : Index, char I s * transform m I := by
  classical
  symm
  unfold transform
  calc
    (1 / 16 : ℝ) * ∑ I : Index, char I s * (∑ t : Pattern, char I t * m t)
        = (1 / 16 : ℝ) * ∑ t : Pattern,
            (∑ I : Index, char I s * char I t) * m t := by
              congr 1
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro t _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro I _
              ring
    _ = (1 / 16 : ℝ) * ∑ t : Pattern,
          (if s = t then 16 else 0) * m t := by
            congr 1
            apply Finset.sum_congr rfl
            intro t _
            rw [char_orthogonality]
    _ = m s := by
          simp
  
/-- Constant cell masses imply vanishing of every nonempty Walsh coefficient. -/
theorem transform_eq_zero_of_constant
    (m : Pattern → ℝ) (a : ℝ) (hm : ∀ s, m s = a) :
    ∀ I : Index, I.Nonempty → transform m I = 0 := by
  intro I hI
  unfold transform
  simp_rw [hm]
  rw [← Finset.sum_mul]
  have hz : (∑ s : Pattern, char I s) = 0 := by
    unfold char
    exact_mod_cast charZ_sum_nonempty I hI
  rw [hz]
  simp

/-- The trivial coefficient together with the 15 zero non-trivial coefficients
forces all 16 values to be equal. -/
theorem constant_of_transform_nonempty_zero
    (m : Pattern → ℝ) (total : ℝ)
    (h0 : transform m ∅ = total)
    (h : ∀ I : Index, I.Nonempty → transform m I = 0) :
    ∀ s : Pattern, m s = total / 16 := by
  intro s
  rw [inversion m s]
  have hsum :
      (∑ I : Index, char I s * transform m I) = total := by
    classical
    calc
      (∑ I : Index, char I s * transform m I)
          = char ∅ s * transform m ∅ := by
              apply Finset.sum_eq_single
              · intro I _ hIne
                have hInonempty : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hIne
                simp [h I hInonempty]
              · simp
      _ = total := by simp [h0]
  rw [hsum]
  ring

/-- Exact equivalence, assuming `total` is the sum of the 16 values. -/
theorem all_equal_iff_nontrivial_transform_zero
    (m : Pattern → ℝ) (total : ℝ)
    (htotal : (∑ s : Pattern, m s) = total) :
    (∀ s : Pattern, m s = total / 16) ↔
      (∀ I : Index, I.Nonempty → transform m I = 0) := by
  constructor
  · intro hm
    exact transform_eq_zero_of_constant m (total / 16) hm
  · intro hzero s
    apply constant_of_transform_nonempty_zero m total
    · simpa [transform_empty] using htotal
    · exact hzero

end Walsh4
end SoberonConvexBody
