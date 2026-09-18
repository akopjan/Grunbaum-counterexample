import SoberonConvexBody.TensorDefs

/-!
# Exact algebra for the zero-set analysis

These lemmas are polynomial identities and ordered-field arguments. No
compactness, asymptotic estimate, or global obstruction theorem is imported.
-/

noncomputable section
namespace SoberonConvexBody.Tensors

private theorem divide_cubic_relation
    (a b c x y z : Real) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a * z + b * y + c * x = 0) :
    x / (a * b) + y / (a * c) + z / (b * c) = 0 := by
  have hp : a * b * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) hc
  have hm : (a * b * c) *
      (x / (a * b) + y / (a * c) + z / (b * c)) = 0 := by
    calc
      (a * b * c) * (x / (a * b) + y / (a * c) + z / (b * c))
          = a * z + b * y + c * x := by
            field_simp [ha, hb, hc] <;> ring
      _ = 0 := h
  exact (mul_eq_zero.mp hm).resolve_left hp

/-- Four cubic equations with four nonzero linear coordinates force the
quartic pairing to be nonzero. This is the sum-of-squares part of the
unperturbed zero classification. -/
theorem quartet_ne_zero_of_four_active
    (a b c d m01 m02 m03 m12 m13 m23 : Real)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h012 : a * m12 + b * m02 + c * m01 = 0)
    (h013 : a * m13 + b * m03 + d * m01 = 0)
    (h023 : a * m23 + c * m03 + d * m02 = 0)
    (h123 : b * m23 + c * m13 + d * m12 = 0) :
    (m01 + a * b) * (m23 + c * d) +
      (m02 + a * c) * (m13 + b * d) +
      (m03 + a * d) * (m12 + b * c) ≠ 0 := by
  let r01 := m01 / (a * b)
  let r02 := m02 / (a * c)
  let r03 := m03 / (a * d)
  let r12 := m12 / (b * c)
  let r13 := m13 / (b * d)
  let r23 := m23 / (c * d)
  have e012 : r01 + r02 + r12 = 0 :=
    divide_cubic_relation a b c m01 m02 m12 ha hb hc h012
  have e013 : r01 + r03 + r13 = 0 :=
    divide_cubic_relation a b d m01 m03 m13 ha hb hd h013
  have e023 : r02 + r03 + r23 = 0 :=
    divide_cubic_relation a c d m02 m03 m23 ha hc hd h023
  have e123 : r12 + r13 + r23 = 0 :=
    divide_cubic_relation b c d m12 m13 m23 hb hc hd h123
  have er23 : r23 = r01 := by linarith
  have er13 : r13 = r02 := by linarith
  have er12 : r12 = r03 := by linarith
  have esum : r01 + r02 + r03 = 0 := by linarith
  have hfactor :
      (m01 + a * b) * (m23 + c * d) +
        (m02 + a * c) * (m13 + b * d) +
        (m03 + a * d) * (m12 + b * c) =
      (a * b * c * d) *
        ((r01 + 1) * (r23 + 1) + (r02 + 1) * (r13 + 1) +
          (r03 + 1) * (r12 + 1)) := by
    dsimp [r01, r02, r03, r12, r13, r23]
    field_simp [ha, hb, hc, hd] <;> ring
  have hpositive : 0 <
      (r01 + 1) * (r23 + 1) + (r02 + 1) * (r13 + 1) +
        (r03 + 1) * (r12 + 1) := by
    rw [er23, er13, er12]
    nlinarith [sq_nonneg r01, sq_nonneg r02, sq_nonneg r03]
  rw [hfactor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd)
    (ne_of_gt hpositive)

/-- Three active linear coordinates force the three off-diagonal entries
in the inactive column to vanish. -/
theorem inactive_column_of_three_active
    (a b c m03 m13 m23 : Real)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h013 : a * m13 + b * m03 = 0)
    (h023 : a * m23 + c * m03 = 0)
    (h123 : b * m23 + c * m13 = 0) :
    m03 = 0 /\ m13 = 0 /\ m23 = 0 := by
  have hprod : (2 * b * c) * m03 = 0 := by
    calc
      (2 * b * c) * m03 =
          c * (a * m13 + b * m03) + b * (a * m23 + c * m03) -
            a * (b * m23 + c * m13) := by ring
      _ = 0 := by rw [h013, h023, h123] <;> ring
  have hz : m03 = 0 := (mul_eq_zero.mp hprod).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) hb) hc)
  have hz13 : a * m13 = 0 := by simpa [hz] using h013
  have hz23 : a * m23 = 0 := by simpa [hz] using h023
  exact ⟨hz, (mul_eq_zero.mp hz13).resolve_left ha,
    (mul_eq_zero.mp hz23).resolve_left ha⟩

/-- With exactly two active linear coordinates, the cubic and quartic
equations force one of the two inactive columns to be diagonal. -/
theorem inactive_column_of_two_active
    (a b m01 m02 m03 m12 m13 m23 : Real)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h023 : a * m23 = 0)
    (h012 : a * m12 + b * m02 = 0)
    (h013 : a * m13 + b * m03 = 0)
    (hB : (m01 + a * b) * m23 + m02 * m13 + m03 * m12 = 0) :
    (m02 = 0 /\ m12 = 0 /\ m23 = 0) \/
      (m03 = 0 /\ m13 = 0 /\ m23 = 0) := by
  have hz23 : m23 = 0 := (mul_eq_zero.mp h023).resolve_left ha
  have hcross : m02 * m13 + m03 * m12 = 0 := by
    simpa [hz23] using hB
  have hprod : (2 * b) * (m02 * m03) = 0 := by
    calc
      (2 * b) * (m02 * m03) =
          m02 * (a * m13 + b * m03) +
            m03 * (a * m12 + b * m02) -
            a * (m02 * m13 + m03 * m12) := by ring
      _ = 0 := by rw [h012, h013, hcross] <;> ring
  have hp : m02 * m03 = 0 := (mul_eq_zero.mp hprod).resolve_left
    (mul_ne_zero (by norm_num) hb)
  rcases mul_eq_zero.mp hp with hz02 | hz03
  · left
    have hh : a * m12 = 0 := by simpa [hz02] using h012
    exact ⟨hz02, (mul_eq_zero.mp hh).resolve_left ha, hz23⟩
  · right
    have hh : a * m13 = 0 := by simpa [hz03] using h013
    exact ⟨hz03, (mul_eq_zero.mp hh).resolve_left ha, hz23⟩

/-- The diagonal entries 1, 2, 4 are distinct, and no corresponding
nonzero eigenvector has coordinates summing to zero. -/
theorem diagonal_eigen_sum_zero
    (a b c lam : Real)
    (hs : a + b + c = 0)
    (h1 : (lam - 1) * a = 0)
    (h2 : (lam - 2) * b = 0)
    (h4 : (lam - 4) * c = 0) :
    a = 0 /\ b = 0 /\ c = 0 := by
  rcases mul_eq_zero.mp h1 with h1 | h1 <;>
    rcases mul_eq_zero.mp h2 with h2 | h2 <;>
    rcases mul_eq_zero.mp h4 with h4 | h4
  all_goals exact ⟨by linarith, by linarith, by linarith⟩

/-- The explicit linear operator with the matrix defining `mForm`. -/
def mOperator (x : E4) : E4 :=
  WithLp.toLp 2 ![x 1 + x 2 + x 3, x 0 + x 1,
    x 0 + 2 * x 2, x 0 + 4 * x 3]

/-- The matrix M has no nonzero eigenvector perpendicular to the first
coordinate direction. This conclusion is proved for the concrete matrix,
not assumed as a spectral hypothesis. -/
theorem mOperator_eigen_first_zero
    (x : E4) (lam : Real) (hx : x 0 = 0)
    (he : mOperator x = lam • x) : x = 0 := by
  have e0 := congrArg (fun v : E4 => v 0) he
  have e1 := congrArg (fun v : E4 => v 1) he
  have e2 := congrArg (fun v : E4 => v 2) he
  have e3 := congrArg (fun v : E4 => v 3) he
  simp [mOperator, PiLp.toLp_apply, hx] at e0 e1 e2 e3
  have h1 : (lam - 1) * x 1 = 0 := by nlinarith [e1]
  have h2 : (lam - 2) * x 2 = 0 := by rcases e2 with rfl | hz2 <;> [ring; simp [hz2]]
  have h4 : (lam - 4) * x 3 = 0 := by rcases e3 with rfl | hz3 <;> [ring; simp [hz3]]
  obtain ⟨hz1, hz2, hz3⟩ :=
    diagonal_eigen_sum_zero (x 1) (x 2) (x 3) lam e0 h1 h2 h4
  ext i
  fin_cases i <;> simp [hx, hz1, hz2, hz3]

/-- The all-active case of the zero classification, specialized to the
actual tensors and the actual obstruction vector. Orthonormality is not
needed in this case. -/
theorem obstruction_zero_ne_of_all_first_coordinates_ne_zero
    (q : Fin 4 -> E4) (hactive : forall i, q i 0 ≠ 0) :
    obstruction 0 q ≠ 0 := by
  intro hz
  obtain ⟨h123, h023, h013, h012, hB⟩ :=
    (obstruction_eq_zero_iff 0 q).mp hz
  simp only [A_zero] at h123 h023 h013 h012
  have e012 : q 0 0 * mForm (q 1) (q 2) +
      q 1 0 * mForm (q 0) (q 2) + q 2 0 * mForm (q 0) (q 1) = 0 := by
    rw [<- three_mul_A0, h012] <;> ring
  have e013 : q 0 0 * mForm (q 1) (q 3) +
      q 1 0 * mForm (q 0) (q 3) + q 3 0 * mForm (q 0) (q 1) = 0 := by
    rw [<- three_mul_A0, h013] <;> ring
  have e023 : q 0 0 * mForm (q 2) (q 3) +
      q 2 0 * mForm (q 0) (q 3) + q 3 0 * mForm (q 0) (q 2) = 0 := by
    rw [<- three_mul_A0, h023] <;> ring
  have e123 : q 1 0 * mForm (q 2) (q 3) +
      q 2 0 * mForm (q 1) (q 3) + q 3 0 * mForm (q 1) (q 2) = 0 := by
    rw [<- three_mul_A0, h123] <;> ring
  have hnz := quartet_ne_zero_of_four_active
    (q 0 0) (q 1 0) (q 2 0) (q 3 0)
    (mForm (q 0) (q 1)) (mForm (q 0) (q 2)) (mForm (q 0) (q 3))
    (mForm (q 1) (q 2)) (mForm (q 1) (q 3)) (mForm (q 2) (q 3))
    (hactive 0) (hactive 1) (hactive 2) (hactive 3) e012 e013 e023 e123
  apply hnz
  change nForm (q 0) (q 1) * nForm (q 2) (q 3) +
    nForm (q 0) (q 2) * nForm (q 1) (q 3) +
    nForm (q 0) (q 3) * nForm (q 1) (q 2) = 0
  rw [<- three_mul_B, hB]
  ring

/-- Exact elimination identity behind the local perturbation argument.
The four tensor residuals have not been assumed to vanish. -/
theorem cubic_residual_elimination
    (a b c d m01 m02 m03 m12 m13 m23 : Real) :
    a * (b * m23 + c * m13 + d * m12) =
      b * (a * m23 + c * m03 + d * m02) +
      c * (a * m13 + b * m03 + d * m01) +
      d * (a * m12 + b * m02 + c * m01) -
      2 * (b * c * m03 + b * d * m02 + c * d * m01) := by
  ring

/-- Concrete perturbed version of the residual identity. -/
theorem perturbed_cubic_residual_elimination
    (tau : Real) (q : Fin 4 -> E4) :
    3 * q 0 0 * A tau (q 1) (q 2) (q 3) =
      3 * q 1 0 * A tau (q 0) (q 2) (q 3) +
      3 * q 2 0 * A tau (q 0) (q 1) (q 3) +
      3 * q 3 0 * A tau (q 0) (q 1) (q 2) -
      2 * (q 1 0 * q 2 0 * mForm (q 0) (q 3) +
        q 1 0 * q 3 0 * mForm (q 0) (q 2) +
        q 2 0 * q 3 0 * mForm (q 0) (q 1)) +
      3 * tau * (q 0 0 * C (q 1) (q 2) (q 3) -
        q 1 0 * C (q 0) (q 2) (q 3) -
        q 2 0 * C (q 0) (q 1) (q 3) -
        q 3 0 * C (q 0) (q 1) (q 2)) := by
  unfold A A0
  ring

end SoberonConvexBody.Tensors
