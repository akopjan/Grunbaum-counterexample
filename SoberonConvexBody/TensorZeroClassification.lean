import SoberonConvexBody.FrameBasics
import SoberonConvexBody.TensorLocal

/-!
# Classification of the unperturbed zeros

The only spectral fact used is the explicit three-entry diagonal calculation
in TensorZeroAlgebra. The remaining argument is finite-dimensional linear
algebra and case analysis on the four first coordinates.
-/

noncomputable section
namespace SoberonConvexBody.Tensors
open Set
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 0

 theorem mForm_comm (x y : E4) : mForm x y = mForm y x := by
  unfold mForm
  ring

 theorem mForm_smul_left (a : Real) (x y : E4) :
    mForm (a • x) y = a * mForm x y := by
  simp only [mForm, PiLp.smul_apply, smul_eq_mul]
  ring

@[simp] theorem inner_coordinateVector_left (i : Fin 4) (x : E4) :
    inner Real (coordinateVector i) x = x i := by
  simp [coordinateVector, EuclideanSpace.inner_single_left]

@[simp] theorem inner_coordinateVector_right (x : E4) (i : Fin 4) :
    inner Real x (coordinateVector i) = x i := by
  rw [real_inner_comm, inner_coordinateVector_left]

 theorem inner_mOperator (x y : E4) :
    inner Real x (mOperator y) = mForm x y := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mOperator, mForm,
    PiLp.toLp_apply, Fin.sum_univ_succ] <;> ring

 theorem IsONFrame.ext_inner {q : Fin 4 -> E4} (hq : IsONFrame q)
    {x y : E4} (h : forall i, inner Real (q i) x = inner Real (q i) y) : x = y := by
  apply hq.toONBasis.repr.injective
  ext i
  simpa only [OrthonormalBasis.repr_apply_apply, IsONFrame.toONBasis_apply] using h i

theorem isONFrame_coordinateVector : IsONFrame coordinateVector := by
  intro i j
  simp only [inner_coordinateVector_left, coordinateVector_apply]

@[simp] theorem norm_coordinateVector (i : Fin 4) : ‖coordinateVector i‖ = 1 :=
  isONFrame_coordinateVector.norm_eq_one i

theorem IsONFrame.first_row_sq_sum {q : Fin 4 -> E4} (hq : IsONFrame q) :
    (q 0 0)^2 + (q 1 0)^2 + (q 2 0)^2 + (q 3 0)^2 = 1 := by
  have h := hq.toONBasis.sum_inner_mul_inner (coordinateVector 0) (coordinateVector 0)
  simpa [Fin.sum_univ_succ, pow_two, add_assoc] using h

/-- A diagonal column of M perpendicular to e0 would be a forbidden eigenvector. -/
 theorem no_inactive_diagonal_column (q : Fin 4 -> E4) (hq : IsONFrame q)
    (j : Fin 4) (hc : q j 0 = 0)
    (hm : forall i, i ≠ j -> mForm (q i) (q j) = 0) : False := by
  have he : mOperator (q j) = mForm (q j) (q j) • q j := by
    apply hq.ext_inner
    intro i
    rw [inner_mOperator, real_inner_smul_right, hq i j]
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij, hm i hij]
  have hz := mOperator_eigen_first_zero (q j) (mForm (q j) (q j)) hc he
  have hn := hq.norm_eq_one j
  rw [hz, norm_zero] at hn
  norm_num at hn

/-- The four stored cubic components cover every ordered distinct triple. -/
 theorem cubic_zero_of_obstruction_zero (tau : Real) (q : Fin 4 -> E4)
    (hz : obstruction tau q = 0) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    A tau (q i) (q j) (q k) = 0 := by
  obtain ⟨h123, h023, h013, h012, _⟩ := (obstruction_eq_zero_iff tau q).mp hz
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | contradiction
    | exact h123 | exact h023 | exact h013 | exact h012
    | (rw [A_swap_12]; first | exact h123 | exact h023 | exact h013 | exact h012)
    | (rw [A_swap_23]; first | exact h123 | exact h023 | exact h013 | exact h012)
    | (rw [A_swap_12, A_swap_23]; first | exact h123 | exact h023 | exact h013 | exact h012)
    | (rw [A_swap_23, A_swap_12]; first | exact h123 | exact h023 | exact h013 | exact h012)
    | (rw [A_swap_12, A_swap_23, A_swap_12]; first | exact h123 | exact h023 | exact h013 | exact h012)

 theorem cubic_unperturbed_zero (q : Fin 4 -> E4)
    (hz : obstruction 0 q = 0) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    q i 0 * mForm (q j) (q k) + q j 0 * mForm (q i) (q k) +
      q k 0 * mForm (q i) (q j) = 0 := by
  have h := cubic_zero_of_obstruction_zero 0 q hz i j k hij hik hjk
  rw [A_zero] at h
  rw [← three_mul_A0, h, mul_zero]

theorem B_swap_13 (w x y z : E4) : B w x y z = B y x w z := by
  rw [B_swap_12, B_swap_23, B_swap_12]

theorem B_swap_14 (w x y z : E4) : B w x y z = B z x y w := by
  rw [B_swap_12, B_swap_23, B_swap_34, B_swap_23, B_swap_12]

/-- The quartic component is symmetric in all four columns. -/
 theorem quartic_zero_of_obstruction_zero (tau : Real) (q : Fin 4 -> E4)
    (hz : obstruction tau q = 0) (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    B (q i) (q j) (q k) (q l) = 0 := by
  have hB := (obstruction_eq_zero_iff tau q).mp hz |>.2.2.2.2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
  all_goals first
    | contradiction
    | first
      | exact hB
      | (rw [B_swap_23]; exact hB)
      | (rw [B_swap_34]; exact hB)
      | (rw [B_swap_23, B_swap_34]; exact hB)
      | (rw [B_swap_34, B_swap_23]; exact hB)
      | (rw [B_swap_23, B_swap_34, B_swap_23]; exact hB)
    | (rw [B_swap_12]; first
      | exact hB
      | (rw [B_swap_23]; exact hB)
      | (rw [B_swap_34]; exact hB)
      | (rw [B_swap_23, B_swap_34]; exact hB)
      | (rw [B_swap_34, B_swap_23]; exact hB)
      | (rw [B_swap_23, B_swap_34, B_swap_23]; exact hB))
    | (rw [B_swap_13]; first
      | exact hB
      | (rw [B_swap_23]; exact hB)
      | (rw [B_swap_34]; exact hB)
      | (rw [B_swap_23, B_swap_34]; exact hB)
      | (rw [B_swap_34, B_swap_23]; exact hB)
      | (rw [B_swap_23, B_swap_34, B_swap_23]; exact hB))
    | (rw [B_swap_14]; first
      | exact hB
      | (rw [B_swap_23]; exact hB)
      | (rw [B_swap_34]; exact hB)
      | (rw [B_swap_23, B_swap_34]; exact hB)
      | (rw [B_swap_34, B_swap_23]; exact hB)
      | (rw [B_swap_23, B_swap_34, B_swap_23]; exact hB))

/-- Signed column permutations preserve the zero equations. -/
 def reframe (p : Equiv.Perm (Fin 4)) (s : Fin 4 -> Real)
    (q : Fin 4 -> E4) : Fin 4 -> E4 := fun i => s i • q (p i)

 theorem continuous_reframe (p : Equiv.Perm (Fin 4)) (s : Fin 4 -> Real) :
    Continuous (reframe p s) := by
  unfold reframe
  fun_prop

 theorem obstruction_reframe_eq_zero (tau : Real) (q : Fin 4 -> E4)
    (hz : obstruction tau q = 0) (p : Equiv.Perm (Fin 4)) (s : Fin 4 -> Real) :
    obstruction tau (reframe p s q) = 0 := by
  apply (obstruction_eq_zero_iff tau _).mpr
  have hc (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      A tau (reframe p s q i) (reframe p s q j) (reframe p s q k) = 0 := by
    have h := cubic_zero_of_obstruction_zero tau q hz (p i) (p j) (p k)
      (fun e => hij (p.injective e)) (fun e => hik (p.injective e))
      (fun e => hjk (p.injective e))
    simp [reframe, A_smul_1, A_smul_2, A_smul_3, h]
  have hb := quartic_zero_of_obstruction_zero tau q hz (p 0) (p 1) (p 2) (p 3)
    (p.injective.ne (by decide)) (p.injective.ne (by decide))
    (p.injective.ne (by decide)) (p.injective.ne (by decide))
    (p.injective.ne (by decide)) (p.injective.ne (by decide))
  refine ⟨hc 1 2 3 (by decide) (by decide) (by decide),
    hc 0 2 3 (by decide) (by decide) (by decide),
    hc 0 1 3 (by decide) (by decide) (by decide),
    hc 0 1 2 (by decide) (by decide) (by decide), ?_⟩
  simp [reframe, B_smul_1, B_smul_2, B_smul_3, B_smul_4, hb]

/-- Precisely one first coordinate is active at an unperturbed zero. -/
 theorem zero_has_unique_active (q : Fin 4 -> E4) (hq : IsONFrame q)
    (hz : obstruction 0 q = 0) :
    ∃ j : Fin 4, q j 0 ≠ 0 ∧ forall i, i ≠ j -> q i 0 = 0 := by
  by_cases h0 : q 0 0 = 0
  · by_cases h1 : q 1 0 = 0
    · by_cases h2 : q 2 0 = 0
      · by_cases h3 : q 3 0 = 0
        · have h := hq.first_row_sq_sum
          simp_all
        · refine ⟨3, h3, ?_⟩
          intro i hi
          fin_cases i <;> simp_all
      · by_cases h3 : q 3 0 = 0
        · refine ⟨2, h2, ?_⟩
          intro i hi
          fin_cases i <;> simp_all
        · exfalso
          have e0 := cubic_unperturbed_zero q hz 2 0 1 (by decide) (by decide) (by decide)
          simp only [h0, h1, zero_mul, add_zero] at e0
          have e1 := cubic_unperturbed_zero q hz 2 3 0 (by decide) (by decide) (by decide)
          simp only [h0, h1, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 2 3 1 (by decide) (by decide) (by decide)
          simp only [h0, h1, zero_mul, add_zero] at e2
          have eB := quartic_zero_of_obstruction_zero 0 q hz 2 3 0 1
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          have eB3 := three_mul_B (q 2) (q 3) (q 0) (q 1)
          rw [eB] at eB3
          simp only [nForm, h0, h1, mul_zero, zero_mul, add_zero] at eB3
          rcases inactive_column_of_two_active (q 2 0) (q 3 0)
            (mForm (q 2) (q 3)) (mForm (q 2) (q 0)) (mForm (q 2) (q 1))
            (mForm (q 3) (q 0)) (mForm (q 3) (q 1)) (mForm (q 0) (q 1))
            h2 h3 e0 e1 e2 eB3.symm with h | h
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 0 h0
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 1 h1
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
    · by_cases h2 : q 2 0 = 0
      · by_cases h3 : q 3 0 = 0
        · refine ⟨1, h1, ?_⟩
          intro i hi
          fin_cases i <;> simp_all
        · exfalso
          have e0 := cubic_unperturbed_zero q hz 1 0 2 (by decide) (by decide) (by decide)
          simp only [h0, h2, zero_mul, add_zero] at e0
          have e1 := cubic_unperturbed_zero q hz 1 3 0 (by decide) (by decide) (by decide)
          simp only [h0, h2, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 1 3 2 (by decide) (by decide) (by decide)
          simp only [h0, h2, zero_mul, add_zero] at e2
          have eB := quartic_zero_of_obstruction_zero 0 q hz 1 3 0 2
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          have eB3 := three_mul_B (q 1) (q 3) (q 0) (q 2)
          rw [eB] at eB3
          simp only [nForm, h0, h2, mul_zero, zero_mul, add_zero] at eB3
          rcases inactive_column_of_two_active (q 1 0) (q 3 0)
            (mForm (q 1) (q 3)) (mForm (q 1) (q 0)) (mForm (q 1) (q 2))
            (mForm (q 3) (q 0)) (mForm (q 3) (q 2)) (mForm (q 0) (q 2))
            h1 h3 e0 e1 e2 eB3.symm with h | h
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 0 h0
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 2 h2
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
      · by_cases h3 : q 3 0 = 0
        · exfalso
          have e0 := cubic_unperturbed_zero q hz 1 0 3 (by decide) (by decide) (by decide)
          simp only [h0, h3, zero_mul, add_zero] at e0
          have e1 := cubic_unperturbed_zero q hz 1 2 0 (by decide) (by decide) (by decide)
          simp only [h0, h3, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 1 2 3 (by decide) (by decide) (by decide)
          simp only [h0, h3, zero_mul, add_zero] at e2
          have eB := quartic_zero_of_obstruction_zero 0 q hz 1 2 0 3
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          have eB3 := three_mul_B (q 1) (q 2) (q 0) (q 3)
          rw [eB] at eB3
          simp only [nForm, h0, h3, mul_zero, zero_mul, add_zero] at eB3
          rcases inactive_column_of_two_active (q 1 0) (q 2 0)
            (mForm (q 1) (q 2)) (mForm (q 1) (q 0)) (mForm (q 1) (q 3))
            (mForm (q 2) (q 0)) (mForm (q 2) (q 3)) (mForm (q 0) (q 3))
            h1 h2 e0 e1 e2 eB3.symm with h | h
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 0 h0
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 3 h3
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
        · exfalso
          have e1 := cubic_unperturbed_zero q hz 1 2 0 (by decide) (by decide) (by decide)
          simp only [h0, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 1 3 0 (by decide) (by decide) (by decide)
          simp only [h0, zero_mul, add_zero] at e2
          have e3 := cubic_unperturbed_zero q hz 2 3 0 (by decide) (by decide) (by decide)
          simp only [h0, zero_mul, add_zero] at e3
          obtain ⟨z1, z2, z3⟩ := inactive_column_of_three_active
            (q 1 0) (q 2 0) (q 3 0) (mForm (q 1) (q 0)) (mForm (q 2) (q 0)) (mForm (q 3) (q 0))
            h1 h2 h3 e1 e2 e3
          apply no_inactive_diagonal_column q hq 0 h0
          intro i hi
          fin_cases i <;> simp_all
  · by_cases h1 : q 1 0 = 0
    · by_cases h2 : q 2 0 = 0
      · by_cases h3 : q 3 0 = 0
        · refine ⟨0, h0, ?_⟩
          intro i hi
          fin_cases i <;> simp_all
        · exfalso
          have e0 := cubic_unperturbed_zero q hz 0 1 2 (by decide) (by decide) (by decide)
          simp only [h1, h2, zero_mul, add_zero] at e0
          have e1 := cubic_unperturbed_zero q hz 0 3 1 (by decide) (by decide) (by decide)
          simp only [h1, h2, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 0 3 2 (by decide) (by decide) (by decide)
          simp only [h1, h2, zero_mul, add_zero] at e2
          have eB := quartic_zero_of_obstruction_zero 0 q hz 0 3 1 2
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          have eB3 := three_mul_B (q 0) (q 3) (q 1) (q 2)
          rw [eB] at eB3
          simp only [nForm, h1, h2, mul_zero, zero_mul, add_zero] at eB3
          rcases inactive_column_of_two_active (q 0 0) (q 3 0)
            (mForm (q 0) (q 3)) (mForm (q 0) (q 1)) (mForm (q 0) (q 2))
            (mForm (q 3) (q 1)) (mForm (q 3) (q 2)) (mForm (q 1) (q 2))
            h0 h3 e0 e1 e2 eB3.symm with h | h
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 1 h1
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 2 h2
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
      · by_cases h3 : q 3 0 = 0
        · exfalso
          have e0 := cubic_unperturbed_zero q hz 0 1 3 (by decide) (by decide) (by decide)
          simp only [h1, h3, zero_mul, add_zero] at e0
          have e1 := cubic_unperturbed_zero q hz 0 2 1 (by decide) (by decide) (by decide)
          simp only [h1, h3, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 0 2 3 (by decide) (by decide) (by decide)
          simp only [h1, h3, zero_mul, add_zero] at e2
          have eB := quartic_zero_of_obstruction_zero 0 q hz 0 2 1 3
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          have eB3 := three_mul_B (q 0) (q 2) (q 1) (q 3)
          rw [eB] at eB3
          simp only [nForm, h1, h3, mul_zero, zero_mul, add_zero] at eB3
          rcases inactive_column_of_two_active (q 0 0) (q 2 0)
            (mForm (q 0) (q 2)) (mForm (q 0) (q 1)) (mForm (q 0) (q 3))
            (mForm (q 2) (q 1)) (mForm (q 2) (q 3)) (mForm (q 1) (q 3))
            h0 h2 e0 e1 e2 eB3.symm with h | h
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 1 h1
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 3 h3
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
        · exfalso
          have e1 := cubic_unperturbed_zero q hz 0 2 1 (by decide) (by decide) (by decide)
          simp only [h1, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 0 3 1 (by decide) (by decide) (by decide)
          simp only [h1, zero_mul, add_zero] at e2
          have e3 := cubic_unperturbed_zero q hz 2 3 1 (by decide) (by decide) (by decide)
          simp only [h1, zero_mul, add_zero] at e3
          obtain ⟨z0, z2, z3⟩ := inactive_column_of_three_active
            (q 0 0) (q 2 0) (q 3 0) (mForm (q 0) (q 1)) (mForm (q 2) (q 1)) (mForm (q 3) (q 1))
            h0 h2 h3 e1 e2 e3
          apply no_inactive_diagonal_column q hq 1 h1
          intro i hi
          fin_cases i <;> simp_all
    · by_cases h2 : q 2 0 = 0
      · by_cases h3 : q 3 0 = 0
        · exfalso
          have e0 := cubic_unperturbed_zero q hz 0 2 3 (by decide) (by decide) (by decide)
          simp only [h2, h3, zero_mul, add_zero] at e0
          have e1 := cubic_unperturbed_zero q hz 0 1 2 (by decide) (by decide) (by decide)
          simp only [h2, h3, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 0 1 3 (by decide) (by decide) (by decide)
          simp only [h2, h3, zero_mul, add_zero] at e2
          have eB := quartic_zero_of_obstruction_zero 0 q hz 0 1 2 3
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          have eB3 := three_mul_B (q 0) (q 1) (q 2) (q 3)
          rw [eB] at eB3
          simp only [nForm, h2, h3, mul_zero, zero_mul, add_zero] at eB3
          rcases inactive_column_of_two_active (q 0 0) (q 1 0)
            (mForm (q 0) (q 1)) (mForm (q 0) (q 2)) (mForm (q 0) (q 3))
            (mForm (q 1) (q 2)) (mForm (q 1) (q 3)) (mForm (q 2) (q 3))
            h0 h1 e0 e1 e2 eB3.symm with h | h
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 2 h2
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
          · obtain ⟨ha, hb, hjk⟩ := h
            apply no_inactive_diagonal_column q hq 3 h3
            intro i hi
            fin_cases i <;> first | contradiction | exact ha | exact hb | exact hjk | (rw [mForm_comm]; first | exact ha | exact hb | exact hjk)
        · exfalso
          have e1 := cubic_unperturbed_zero q hz 0 1 2 (by decide) (by decide) (by decide)
          simp only [h2, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 0 3 2 (by decide) (by decide) (by decide)
          simp only [h2, zero_mul, add_zero] at e2
          have e3 := cubic_unperturbed_zero q hz 1 3 2 (by decide) (by decide) (by decide)
          simp only [h2, zero_mul, add_zero] at e3
          obtain ⟨z0, z1, z3⟩ := inactive_column_of_three_active
            (q 0 0) (q 1 0) (q 3 0) (mForm (q 0) (q 2)) (mForm (q 1) (q 2)) (mForm (q 3) (q 2))
            h0 h1 h3 e1 e2 e3
          apply no_inactive_diagonal_column q hq 2 h2
          intro i hi
          fin_cases i <;> simp_all
      · by_cases h3 : q 3 0 = 0
        · exfalso
          have e1 := cubic_unperturbed_zero q hz 0 1 3 (by decide) (by decide) (by decide)
          simp only [h3, zero_mul, add_zero] at e1
          have e2 := cubic_unperturbed_zero q hz 0 2 3 (by decide) (by decide) (by decide)
          simp only [h3, zero_mul, add_zero] at e2
          have e3 := cubic_unperturbed_zero q hz 1 2 3 (by decide) (by decide) (by decide)
          simp only [h3, zero_mul, add_zero] at e3
          obtain ⟨z0, z1, z2⟩ := inactive_column_of_three_active
            (q 0 0) (q 1 0) (q 2 0) (mForm (q 0) (q 3)) (mForm (q 1) (q 3)) (mForm (q 2) (q 3))
            h0 h1 h2 e1 e2 e3
          apply no_inactive_diagonal_column q hq 3 h3
          intro i hi
          fin_cases i <;> simp_all
        · exfalso
          exact obstruction_zero_ne_of_all_first_coordinates_ne_zero q
            (by intro i; fin_cases i <;> assumption) hz


/-- A unit vector in the diagonal 1,2,4 eigenspaces has a single nonzero
coordinate, of square one. -/
 theorem diagonal_unit_is_coordinate (x : E4) (lam : Real)
    (hx0 : x 0 = 0) (hn : norm x = 1)
    (h1 : (lam - 1) * x 1 = 0) (h2 : (lam - 2) * x 2 = 0)
    (h4 : (lam - 4) * x 3 = 0) :
    ∃ k : Fin 4, x = x k • coordinateVector k ∧ (x k)^2 = 1 := by
  have hnorm := EuclideanSpace.real_norm_sq_eq x
  rw [hn] at hnorm
  have hs : (x 1)^2 + (x 2)^2 + (x 3)^2 = 1 := by
    simpa [Fin.sum_univ_succ, hx0, add_assoc] using hnorm.symm
  rcases mul_eq_zero.mp h1 with hL1 | hX1 <;>
    rcases mul_eq_zero.mp h2 with hL2 | hX2 <;>
    rcases mul_eq_zero.mp h4 with hL4 | hX4
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · refine ⟨1, ?_, by nlinarith [hs, hX2, hX4]⟩
    ext i; fin_cases i <;> simp [coordinateVector, coordinateVector_apply, PiLp.smul_apply, hx0, hX2, hX4]
  · exfalso; linarith
  · refine ⟨2, ?_, by nlinarith [hs, hX1, hX4]⟩
    ext i; fin_cases i <;> simp [coordinateVector, coordinateVector_apply, PiLp.smul_apply, hx0, hX1, hX4]
  · refine ⟨3, ?_, by nlinarith [hs, hX1, hX2]⟩
    ext i; fin_cases i <;> simp [coordinateVector, coordinateVector_apply, PiLp.smul_apply, hx0, hX1, hX2]
  · exfalso; nlinarith [hs, hX1, hX2, hX4]

/-- The unique active column is a signed copy of e0. -/
 theorem unique_active_column (q : Fin 4 -> E4) (hq : IsONFrame q)
    (j : Fin 4) (hinactive : forall i, i ≠ j -> q i 0 = 0) :
    q j = q j 0 • coordinateVector 0 ∧ (q j 0)^2 = 1 := by
  have hexp : (∑ i : Fin 4, q i 0 • q i) = coordinateVector 0 := by
    simpa using hq.toONBasis.sum_repr' (coordinateVector 0)
  have hsingle : (∑ i : Fin 4, q i 0 • q i) = q j 0 • q j := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      simp [hinactive i hij]
    · simp
  rw [hsingle] at hexp
  have hsq : (q j 0)^2 = 1 := by
    have h := congrArg (fun v : E4 => v 0) hexp
    simpa [PiLp.smul_apply, smul_eq_mul, pow_two] using h
  refine ⟨?_, hsq⟩
  calc
    q j = (q j 0 * q j 0) • q j := by rw [← pow_two, hsq, one_smul]
    _ = q j 0 • (q j 0 • q j) := by rw [smul_smul]
    _ = q j 0 • coordinateVector 0 := by rw [hexp]

/-- All columns of an unperturbed zero are signed coordinate vectors. -/
 theorem zero_columns_are_coordinates (q : Fin 4 -> E4) (hq : IsONFrame q)
    (hz : obstruction 0 q = 0) :
    forall i : Fin 4, ∃ k : Fin 4,
      q i = q i k • coordinateVector k ∧ (q i k)^2 = 1 := by
  obtain ⟨j, hc, hrest⟩ := zero_has_unique_active q hq hz
  obtain ⟨hqj, hsqj⟩ := unique_active_column q hq j hrest
  intro i
  by_cases hij : i = j
  · subst i
    exact ⟨0, hqj, hsqj⟩
  · have hi0 := hrest i hij
    let lam : Real := mForm (q i) (q i)
    let v : Real := q i 1 + q i 2 + q i 3
    have he : mOperator (q i) = lam • q i + v • coordinateVector 0 := by
      apply hq.ext_inner
      intro k
      rw [inner_mOperator, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, inner_coordinateVector_right, hq k i]
      by_cases hki : k = i
      · subst k
        simp [lam, hi0]
      · by_cases hkj : k = j
        · subst k
          have hmf : mForm (q j) (q i) = q j 0 * v := by
            rw [hqj, mForm_smul_left]
            simp [mForm, v]
          rw [hmf, if_neg hki]
          ring
        · have hrel := cubic_unperturbed_zero q hz j k i
            (Ne.symm hkj) (Ne.symm hij) hki
          simp only [hrest k hkj, hi0, zero_mul, add_zero] at hrel
          have hm : mForm (q k) (q i) = 0 := (mul_eq_zero.mp hrel).resolve_left hc
          simp [hki, hrest k hkj, hm]
    have e1 := congrArg (fun x : E4 => x 1) he
    have e2 := congrArg (fun x : E4 => x 2) he
    have e3 := congrArg (fun x : E4 => x 3) he
    simp [mOperator, PiLp.toLp_apply, hi0] at e1 e2 e3
    have h1 : (lam - 1) * q i 1 = 0 := by nlinarith [e1]
    have h2 : (lam - 2) * q i 2 = 0 := by
      rcases e2 with hlam | hz2
      · rw [← hlam]; ring
      · simp [hz2]
    have h3 : (lam - 4) * q i 3 = 0 := by
      rcases e3 with hlam | hz3
      · rw [← hlam]; ring
      · simp [hz3]
    exact diagonal_unit_is_coordinate (q i) lam hi0 (hq.norm_eq_one i) h1 h2 h3

/-- The coordinate supports form a permutation. Applying its inverse and
rescaling by the signs sends the original zero exactly to the identity. -/
 theorem zero_can_be_reframed_to_standard (q : Fin 4 -> E4) (hq : IsONFrame q)
    (hz : obstruction 0 q = 0) :
    ∃ p : Equiv.Perm (Fin 4), ∃ s : Fin 4 -> Real,
      (forall i, (s i)^2 = 1) ∧ reframe p s q = standardFrame := by
  classical
  choose k hk hs using zero_columns_are_coordinates q hq hz
  have hinj : Function.Injective k := by
    intro i j hij
    by_contra hne
    have hInner : inner Real (q i) (q j) = 0 := by simpa [hne] using hq i j
    have hmult : q i (k i) * q j (k j) = 0 := by
      have hv : inner Real (q i) (q j) = q i (k i) * q j (k j) := by
        conv_lhs => rw [hk i, hk j]
        rw [real_inner_smul_left, real_inner_smul_right, inner_coordinateVector_left]
        simp [hij]
      rw [hv] at hInner
      exact hInner
    rcases mul_eq_zero.mp hmult with hi | hj
    · have := hs i
      rw [hi] at this
      norm_num at this
    · have := hs j
      rw [hj] at this
      norm_num at this
  have hbij : Function.Bijective k :=
    (Fintype.bijective_iff_injective_and_card k).mpr ⟨hinj, rfl⟩
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective k hbij
  let p := e.symm
  let s : Fin 4 -> Real := fun i => q (p i) i
  have hkp : forall i, k (p i) = i := by
    intro i
    exact e.apply_symm_apply i
  have hs' : forall i, (s i)^2 = 1 := by
    intro i
    have h := hs (p i)
    simpa [hkp, s] using h
  refine ⟨p, s, hs', ?_⟩
  funext i
  have hcol : q (p i) = s i • coordinateVector i := by
    simpa [hkp, s] using hk (p i)
  change s i • q (p i) = coordinateVector i
  rw [hcol, smul_smul, ← pow_two, hs' i, one_smul]

end SoberonConvexBody.Tensors
