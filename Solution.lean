import SoberonConvexBody.ComparatorBridge

/-!
# Proved solution

Checks this declaration against the statement-only declaration in
`Challenge.lean`.
-/

noncomputable section

open Set Real MeasureTheory

namespace SoberonConvexBody

/-- Literal statement of Grünbaum's counterexample. -/
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
  rcases exists_convex_body_counterexample with ⟨K, hKint, hno⟩
  exact ⟨K, hKint, fun ⟨u, t, h⟩ => noEquipartition_of_convex_body_counterexample K hKint hno u t h⟩

end SoberonConvexBody
