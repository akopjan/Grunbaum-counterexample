import SoberonConvexBody.FrameBasics

/-!
# Quantitative orthonormalization of four almost orthogonal unit vectors

The construction is an explicit four-step Gram--Schmidt calculation.
The uniform constant is deliberately coarse: `26 * delta`.
-/

noncomputable section
namespace SoberonConvexBody.Tensors
open scoped BigOperators

namespace QuantitativeFrame

def normalize (v : E4) : E4 := (norm v)⁻¹ • v

 theorem normalize_norm (v : E4) (hv : v ≠ 0) : norm (normalize v) = 1 := by
  have hn : norm v ≠ 0 := norm_ne_zero_iff.mpr hv
  simp [normalize, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v), hn]

 theorem normalize_near_unit (v u : E4) (a : Real)
    (hu : norm u = 1) (hclose : norm (v-u) ≤ a) (ha : a < 1) :
    norm (normalize v) = 1 ∧ norm (normalize v-u) ≤ 2*a := by
  have hv : v ≠ 0 := by
    intro hz
    rw [hz, zero_sub, norm_neg, hu] at hclose
    linarith
  have hunit := normalize_norm v hv
  have hrec : norm v • normalize v = v := by
    simp [normalize, smul_smul, norm_ne_zero_iff.mpr hv]
  have heq : normalize v - v = (1-norm v) • normalize v := by
    rw [sub_smul, one_smul, hrec]
  have hn : norm (normalize v - v) ≤ a := by
    rw [heq, norm_smul, Real.norm_eq_abs, hunit, mul_one]
    have h := abs_norm_sub_norm_le v u
    rw [hu, abs_sub_comm] at h
    exact h.trans hclose
  refine ⟨hunit, ?_⟩
  have : normalize v - u = (normalize v - v) + (v - u) := by abel
  rw [this]
  exact (norm_add_le _ _).trans (by linarith)

 theorem inner_normalize_zero (v w : E4) (h : inner Real v w = 0) :
    inner Real (normalize v) w = 0 := by
  simp only [normalize, real_inner_smul_left, h, mul_zero]

 theorem abs_inner_of_near (u v w : E4) (delta a : Real)
    (hu : norm u = 1) (hiv : |inner Real u v| ≤ delta)
    (hn : norm (w-v) ≤ a) : |inner Real u w| ≤ delta+a := by
  have heq : inner Real u w = inner Real u v + inner Real u (w-v) := by
    rw [inner_sub_right]
    ring
  calc
    |inner Real u w| = |inner Real u v + inner Real u (w-v)| := by rw [heq]
    _ ≤ |inner Real u v| + |inner Real u (w-v)| := abs_add_le _ _
    _ ≤ delta + norm u * norm (w-v) :=
      add_le_add hiv (abs_real_inner_le_norm _ _)
    _ ≤ delta+a := by rw [hu, one_mul]; linarith

 theorem near_orthonormal (delta : Real) (hd : 0 ≤ delta) (hsmall : delta < 1/100)
    (n : Fin 4 -> E4) (hn : forall i, norm (n i) = 1)
    (hp : forall i j, i ≠ j -> |inner Real (n i) (n j)| ≤ delta) :
    ∃ q : Fin 4 -> E4, IsONFrame q ∧ forall i, norm (n i - q i) ≤ 26*delta := by
  let q0 := n 0
  have hn0 : norm q0 = 1 := hn 0
  have h00 : inner Real q0 q0 = 1 := by rw [real_inner_self_eq_norm_sq, hn0]; norm_num
  let b10 := inner Real (n 1) q0
  let v1 := n 1 - b10 • q0
  let q1 := normalize v1
  have hb10 : |b10| ≤ delta := hp 1 0 (by decide)
  have hv1 : norm (v1 - n 1) ≤ delta := by
    have he : v1 - n 1 = -(b10 • q0) := by dsimp [v1]; abel
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs, hn0, mul_one]
    exact hb10
  obtain ⟨hn1, hc1⟩ := normalize_near_unit v1 (n 1) delta (hn 1) hv1 (by linarith)
  change norm q1 = 1 at hn1
  change norm (q1-n 1) ≤ 2*delta at hc1
  have h10 : inner Real q1 q0 = 0 := by
    apply inner_normalize_zero
    simp [v1, b10, inner_sub_left, real_inner_smul_left, hn0]
  have h01 : inner Real q0 q1 = 0 := by rw [real_inner_comm, h10]
  have h11 : inner Real q1 q1 = 1 := by rw [real_inner_self_eq_norm_sq, hn1]; norm_num

  let b20 := inner Real (n 2) q0
  let b21 := inner Real (n 2) q1
  let v2 := n 2 - b20 • q0 - b21 • q1
  let q2 := normalize v2
  have hb20 : |b20| ≤ delta := hp 2 0 (by decide)
  have hb21 : |b21| ≤ 3*delta := by
    have h := abs_inner_of_near (n 2) (n 1) q1 delta (2*delta)
      (hn 2) (hp 2 1 (by decide)) hc1
    change |b21| ≤ _ at h
    linarith
  have hv2 : norm (v2-n 2) ≤ 4*delta := by
    have he : v2-n 2 = -(b20 • q0 + b21 • q1) := by dsimp [v2]; abel
    rw [he, norm_neg]
    calc
      norm (b20 • q0 + b21 • q1) ≤ norm (b20 • q0) + norm (b21 • q1) := norm_add_le _ _
      _ = |b20| + |b21| := by simp [norm_smul, Real.norm_eq_abs, hn0, hn1]
      _ ≤ 4*delta := by linarith
  obtain ⟨hn2, hc2⟩ := normalize_near_unit v2 (n 2) (4*delta) (hn 2) hv2 (by linarith)
  change norm q2 = 1 at hn2
  have hc2' : norm (q2-n 2) ≤ 8*delta := by change norm (q2-n 2) ≤ _ at hc2; linarith
  have h20 : inner Real q2 q0 = 0 := by
    apply inner_normalize_zero
    simp [v2, b20, inner_sub_left, real_inner_smul_left, h10, hn0]
  have h02 : inner Real q0 q2 = 0 := by rw [real_inner_comm, h20]
  have h21 : inner Real q2 q1 = 0 := by
    apply inner_normalize_zero
    simp [v2, b21, inner_sub_left, real_inner_smul_left, h01, hn1]
  have h12 : inner Real q1 q2 = 0 := by rw [real_inner_comm, h21]
  have h22 : inner Real q2 q2 = 1 := by rw [real_inner_self_eq_norm_sq, hn2]; norm_num

  let b30 := inner Real (n 3) q0
  let b31 := inner Real (n 3) q1
  let b32 := inner Real (n 3) q2
  let v3 := n 3 - b30 • q0 - b31 • q1 - b32 • q2
  let q3 := normalize v3
  have hb30 : |b30| ≤ delta := hp 3 0 (by decide)
  have hb31 : |b31| ≤ 3*delta := by
    have h := abs_inner_of_near (n 3) (n 1) q1 delta (2*delta)
      (hn 3) (hp 3 1 (by decide)) hc1
    change |b31| ≤ _ at h
    linarith
  have hb32 : |b32| ≤ 9*delta := by
    have h := abs_inner_of_near (n 3) (n 2) q2 delta (8*delta)
      (hn 3) (hp 3 2 (by decide)) hc2'
    change |b32| ≤ _ at h
    linarith
  have hv3 : norm (v3-n 3) ≤ 13*delta := by
    have he : v3-n 3 = -(b30 • q0 + b31 • q1 + b32 • q2) := by dsimp [v3]; abel
    rw [he, norm_neg]
    calc
      norm (b30 • q0 + b31 • q1 + b32 • q2)
          ≤ norm (b30 • q0 + b31 • q1) + norm (b32 • q2) := norm_add_le _ _
      _ ≤ norm (b30 • q0) + norm (b31 • q1) + norm (b32 • q2) := by
        have := norm_add_le (b30 • q0) (b31 • q1)
        linarith
      _ = |b30| + |b31| + |b32| := by simp [norm_smul, Real.norm_eq_abs, hn0, hn1, hn2]
      _ ≤ 13*delta := by linarith
  obtain ⟨hn3, hc3⟩ := normalize_near_unit v3 (n 3) (13*delta) (hn 3) hv3 (by linarith)
  change norm q3 = 1 at hn3
  have hc3' : norm (q3-n 3) ≤ 26*delta := by change norm (q3-n 3) ≤ _ at hc3; linarith
  have h30 : inner Real q3 q0 = 0 := by
    apply inner_normalize_zero
    simp [v3, b30, inner_sub_left, real_inner_smul_left, h10, h20, hn0]
  have h03 : inner Real q0 q3 = 0 := by rw [real_inner_comm, h30]
  have h31 : inner Real q3 q1 = 0 := by
    apply inner_normalize_zero
    simp [v3, b31, inner_sub_left, real_inner_smul_left, h01, h21, hn1]
  have h13 : inner Real q1 q3 = 0 := by rw [real_inner_comm, h31]
  have h32 : inner Real q3 q2 = 0 := by
    apply inner_normalize_zero
    simp [v3, b32, inner_sub_left, real_inner_smul_left, h02, h12, hn2]
  have h23 : inner Real q2 q3 = 0 := by rw [real_inner_comm, h32]
  have h33 : inner Real q3 q3 = 1 := by rw [real_inner_self_eq_norm_sq, hn3]; norm_num
  let q : Fin 4 -> E4 := ![q0,q1,q2,q3]
  refine ⟨q, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [q, q0, q1, q2, q3, hn0, hn1, hn2, hn3,
        h00, h01, h02, h03, h10, h11, h12, h13,
        h20, h21, h22, h23, h30, h31, h32, h33]
  · intro i
    fin_cases i
    · simp [q, q0]
      linarith [hd]
    · change norm (n 1 - q1) ≤ 26 * delta
      rw [norm_sub_rev]
      linarith [hc1]
    · change norm (n 2 - q2) ≤ 26 * delta
      rw [norm_sub_rev]
      linarith [hc2']
    · change norm (n 3 - q3) ≤ 26 * delta
      rw [norm_sub_rev]
      linarith [hc3']

end QuantitativeFrame
end SoberonConvexBody.Tensors
