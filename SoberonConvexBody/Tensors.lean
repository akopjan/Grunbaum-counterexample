import SoberonConvexBody.TensorZeroClassification

/-!
# Global tensor obstruction

The proof has three explicit ingredients: classification at parameter zero,
local polynomial exclusion, and compactness away from the zero neighborhoods.
-/

noncomputable section
namespace SoberonConvexBody.Tensors
open Set

/-- All column-scaled permutations of the displayed identity neighborhood. -/
def tensorZeroNeighborhood : Set (Fin 4 -> E4) :=
  ⋃ p : Equiv.Perm (Fin 4), ⋃ s : Fin 4 -> Real,
    (reframe p s) ⁻¹' tensorIdentityNeighborhood

 theorem isOpen_tensorZeroNeighborhood : IsOpen tensorZeroNeighborhood := by
  unfold tensorZeroNeighborhood
  apply isOpen_iUnion
  intro p
  apply isOpen_iUnion
  intro s
  exact isOpen_tensorIdentityNeighborhood.preimage (continuous_reframe p s)

 theorem zero_mem_tensorZeroNeighborhood (q : Fin 4 -> E4)
    (hq : IsONFrame q) (hz : obstruction 0 q = 0) : q ∈ tensorZeroNeighborhood := by
  obtain ⟨p, s, _, he⟩ := zero_can_be_reframed_to_standard q hq hz
  apply Set.mem_iUnion.mpr
  refine ⟨p, Set.mem_iUnion.mpr ⟨s, ?_⟩⟩
  change reframe p s q ∈ tensorIdentityNeighborhood
  rw [he]
  exact standardFrame_mem_tensorIdentityNeighborhood

 theorem obstruction_ne_zero_in_zeroNeighborhood (tau : Real) (q : Fin 4 -> E4)
    (ht : 0 < tau) (ht' : tau < 1 / 4) (hq : q ∈ tensorZeroNeighborhood) :
    obstruction tau q ≠ 0 := by
  rcases Set.mem_iUnion.mp hq with ⟨p, hp⟩
  rcases Set.mem_iUnion.mp hp with ⟨s, hs⟩
  intro hz
  exact obstruction_ne_zero_near_standard tau (reframe p s q) ht ht' hs
    (obstruction_reframe_eq_zero tau q hz p s)

/-- The compact frame locus, in the original unbundled representation. -/
 theorem isCompact_onFrames : IsCompact {q : Fin 4 -> E4 | IsONFrame q} := by
  let P : Set (Fin 4 -> E4) := Set.univ.pi (fun _ => Metric.sphere (0 : E4) 1)
  have hP : IsCompact P := isCompact_univ_pi (fun _ => isCompact_sphere (0 : E4) 1)
  have hclosed : IsClosed {q : Fin 4 -> E4 | IsONFrame q} := by
    unfold IsONFrame
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_eq (by fun_prop) (by fun_prop)
  apply hP.of_isClosed_subset hclosed
  intro q hq
  change q ∈ Set.univ.pi (fun _ => Metric.sphere (0 : E4) 1)
  rw [Set.mem_pi]
  intro i _
  simpa [Metric.mem_sphere, dist_zero_right] using hq.norm_eq_one i

 theorem continuous_obstruction (tau : Real) : Continuous (obstruction tau) := by
  unfold obstruction A A0 C B nForm mForm
  fun_prop

/-- The perturbation vector is a concrete polynomial function of the frame. -/
def tensorPerturbation (q : Fin 4 -> E4) : E5 := obstruction 1 q - obstruction 0 q

 theorem continuous_tensorPerturbation : Continuous tensorPerturbation :=
  (continuous_obstruction 1).sub (continuous_obstruction 0)

 theorem obstruction_affine_parameter (tau : Real) (q : Fin 4 -> E4) :
    obstruction tau q = obstruction 0 q + tau • tensorPerturbation q := by
  ext i
  fin_cases i <;>
    simp [obstruction, tensorPerturbation, A, PiLp.toLp_apply,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] <;> ring

/-- Small positive parameters remove every tensor zero on the frame locus. -/
theorem exists_tau_obstruction_nonzero :
    ∃ tau : Real, 0 < tau ∧
      ∀ q : Fin 4 -> E4, IsONFrame q -> obstruction tau q ≠ 0 := by
  let S : Set (Fin 4 -> E4) := {q | IsONFrame q}
  let T : Set (Fin 4 -> E4) := S ∩ tensorZeroNeighborhoodᶜ
  have hS : IsCompact S := isCompact_onFrames
  have hT : IsCompact T := by
    apply hS.of_isClosed_subset
    · exact hS.isClosed.inter isOpen_tensorZeroNeighborhood.isClosed_compl
    · exact Set.inter_subset_left
  have hpos : ∀ q ∈ T, 0 < norm (obstruction 0 q) := by
    intro q hq
    apply norm_pos_iff.mpr
    intro hz
    exact hq.2 (zero_mem_tensorZeroNeighborhood q hq.1 hz)
  obtain ⟨m, hm, hmin⟩ := hT.exists_forall_le'
    (continuous_obstruction 0).norm.continuousOn hpos
  have hb : BddAbove ((fun q => norm (tensorPerturbation q)) '' S) :=
    hS.bddAbove_image continuous_tensorPerturbation.norm.continuousOn
  obtain ⟨b, hb⟩ := hb
  let K : Real := max 1 b
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbound : ∀ q ∈ S, norm (tensorPerturbation q) ≤ K := by
    intro q hq
    exact (hb ⟨q, hq, rfl⟩).trans (le_max_right _ _)
  let tau : Real := min (1 / 8) (m / (2 * K))
  have ht : 0 < tau := lt_min (by norm_num) (div_pos hm (mul_pos (by norm_num) hK))
  have ht' : tau < 1 / 4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htK : tau * K ≤ m / 2 := by
    calc
      tau * K ≤ (m / (2 * K)) * K :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hK.le
      _ = m / 2 := by field_simp [hK.ne']
  refine ⟨tau, ht, ?_⟩
  intro q hq
  by_cases hgood : q ∈ tensorZeroNeighborhood
  · exact obstruction_ne_zero_in_zeroNeighborhood tau q ht ht' hgood
  · intro hz
    have hmq : m ≤ norm (obstruction 0 q) := hmin q ⟨hq, hgood⟩
    have hnorm : norm (obstruction tau q - obstruction 0 q) =
        |tau| * norm (tensorPerturbation q) := by
      rw [obstruction_affine_parameter, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [hz, zero_sub, norm_neg, abs_of_pos ht] at hnorm
    have hle := mul_le_mul_of_nonneg_left (hbound q hq) ht.le
    linarith

end SoberonConvexBody.Tensors
