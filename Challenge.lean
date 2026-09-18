import Mathlib

/-!
# Four affine hyperplanes need not equipartition a convex body in R^4

This file is the small statement surface.
It contains only the advertised mathematical claim.

The statement is a geometric strengthening/variant of Pablo Soberón's 2026
counterexample for a mass in `R^4`: here the obstructed mass is specifically
Lebesgue volume restricted to a convex body with nonempty interior.

For a Boolean sign pattern `s`, `true` selects the closed halfspace
`⟪x,u_i⟫ >= t_i` and `false` selects the open halfspace
`⟪x,u_i⟫ < t_i`.  This convention makes the sixteen cells literally disjoint.
No nonzeroness or normalization assumption is placed on the vectors `u_i`.
-/

noncomputable section

open Set Real MeasureTheory

namespace SoberonConvexBody

/-- There is a convex body in `R^4`, with nonempty interior, for which no four
    affine linear inequalities cut the body into sixteen cells all having
    one sixteenth of its volume. -/
theorem grunbaum_counterexample :
    ∃ K : ConvexBody (EuclideanSpace ℝ (Fin 4)),
      (interior (K : Set (EuclideanSpace ℝ (Fin 4)))).Nonempty ∧
      ¬ ∃ (u : Fin 4 → EuclideanSpace ℝ (Fin 4)) (t : Fin 4 → ℝ),
          ∀ s : Fin 4 → Bool,
            volume.real
                ((K : Set (EuclideanSpace ℝ (Fin 4))) ∩
                  {x : EuclideanSpace ℝ (Fin 4) |
                    ∀ i,
                      if s i then
                        t i ≤ inner ℝ x (u i)
                      else
                        inner ℝ x (u i) < t i}) =
              volume.real (K : Set (EuclideanSpace ℝ (Fin 4))) / 16 := by
  sorry

end SoberonConvexBody
