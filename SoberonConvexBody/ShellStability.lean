import SoberonConvexBody.ShellBounds

/-!
# Quadratic stability of the radial shell

Two independent first-order restrictions occur: the point must lie in the
radial annulus, and its direction must be close to one of four hyperplanes.
The annulus/strip estimate is proved in ShellBounds, not assumed here.
-/

noncomputable section
namespace SoberonConvexBody
open Set Real MeasureTheory
open scoped BigOperators

namespace ShellBounds
open SphereGeometry

 theorem abs_of_closedSign_ne (a b : Real) (h : closedSign a ≠ closedSign b) :
    |b| ≤ |a-b| := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · simp [closedSign, ha, hb] at h
  · rw [abs_of_neg (lt_of_not_ge hb), abs_of_nonneg (by linarith : 0 ≤ a-b)]
    linarith
  · rw [abs_of_nonneg hb, abs_of_neg (by linarith : a-b < 0)]
    linarith
  · simp [closedSign, ha, hb] at h

 theorem signCharacter_ne_exists_index (c : HyperplaneCfg) (q : Fin 4 -> E4)
    (I : Walsh4.Index) (x : E4)
    (hne : Cells.signCharacter c I x ≠ Cells.signCharacter ⟨q, fun _ => 0⟩ I x) :
    ∃ i : Fin 4, closedSign (inner Real x (c.normal i) - c.offset i) ≠
      closedSign (inner Real x (q i)) := by
  classical
  by_contra! hn
  apply hne
  rw [Cells.signCharacter_eq_prod, Cells.signCharacter_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [closedSign, sub_nonneg] using hn i

/-- A changed character on the shell has direction in an explicit thin strip.
The proof does not assume any general-position condition on the perturbed planes. -/
 theorem changed_character_mem_shellStrips (tau eps B M : Real) (hB : 0 < B)
    (hM : 0 < M) (hsmall : |eps| * B ≤ 1/2)
    (hbound : forall u : E4, norm u = 1 -> |angularPerturbation tau u| ≤ B)
    (c : HyperplaneCfg) (q : Fin 4 -> E4)
    (hoff : forall i, |c.offset i| ≤ M*|eps|)
    (hnormal : forall i, norm (c.normal i - q i) ≤ M*|eps|)
    (I : Walsh4.Index) (x : E4)
    (hx : x ∈ symmDiff (radialSet tau eps) (Metric.closedBall (0 : E4) 1))
    (hne : Cells.signCharacter c I x ≠ Cells.signCharacter ⟨q, fun _ => 0⟩ I x) :
    x ∈ shellStrips (1-|eps| * B) (1+|eps| * B) q (6*M*|eps|) := by
  have hband := radial_symmDiff_band tau eps B hB hbound hx
  have hnorm := radial_symmDiff_norm_bounds tau eps B hB hsmall hbound hx
  obtain ⟨i, hi⟩ := signCharacter_ne_exists_index c q I x hne
  have hmargin := abs_of_closedSign_ne _ _ hi
  have heq : inner Real x (c.normal i) - c.offset i - inner Real x (q i) =
      inner Real x (c.normal i - q i) - c.offset i := by
    rw [inner_sub_right]
    ring
  rw [heq] at hmargin
  have hinner : |inner Real x (q i)| ≤ 3*M*|eps| := by
    calc
      |inner Real x (q i)| ≤ |inner Real x (c.normal i - q i) - c.offset i| := hmargin
      _ ≤ |inner Real x (c.normal i - q i)| + |c.offset i| := abs_sub _ _
      _ ≤ norm x * norm (c.normal i - q i) + M*|eps| :=
        add_le_add (abs_real_inner_le_norm _ _) (hoff i)
      _ ≤ 2*(M*|eps|) + M*|eps| := by
        have : norm x * norm (c.normal i - q i) ≤ 2 * (M * |eps|) :=
          mul_le_mul hnorm.2 (hnormal i) (norm_nonneg _) (by norm_num)
        linarith
      _ = 3*M*|eps| := by ring
  have hr : 0 < norm x := lt_trans (by norm_num) hnorm.1
  have hinv : (norm x)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hr (by norm_num : (0 : Real) < 2)]
    linarith [hnorm.1]
  have hdir : |inner Real (direction x) (q i)| ≤ 6*M*|eps| := by
    rw [direction, real_inner_smul_left, abs_mul, abs_inv,
      abs_of_nonneg (norm_nonneg x)]
    calc
      (norm x)⁻¹ * |inner Real x (q i)| ≤ 2*(3*M*|eps|) :=
        mul_le_mul hinv hinner (abs_nonneg _) (by norm_num)
      _ = 6*M*|eps| := by ring
  exact ⟨hband.1, hband.2, i, hdir⟩

 theorem integrable_signCharacter_restrict (A : Set E4) (hfin : volume A ≠ ⊤)
    (c : HyperplaneCfg) (I : Walsh4.Index) :
    Integrable (Cells.signCharacter c I) (volume.restrict A) := by
  letI : Fact (volume A < ⊤) := ⟨lt_top_iff_ne_top.mpr hfin⟩
  letI : IsFiniteMeasure (volume.restrict A) := MeasureTheory.Restrict.isFiniteMeasure volume
  apply (integrable_const (1 : Real)).mono'
  · exact (Cells.measurable_signCharacter c I).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      simp [Real.norm_eq_abs, Cells.signCharacter, Walsh4.abs_char])

 theorem integrable_indicator_const_finite (A : Set E4) (hA : MeasurableSet A)
    (hfin : volume A ≠ ⊤) (a : Real) :
    Integrable (A.indicator (fun _ : E4 => a)) volume := by
  letI : Fact (volume A < ⊤) := ⟨lt_top_iff_ne_top.mpr hfin⟩
  letI : IsFiniteMeasure (volume.restrict A) := MeasureTheory.Restrict.isFiniteMeasure volume
  rw [integrable_indicator_iff hA]
  exact integrable_const a

/-- A four-term Walsh difference is controlled by where both the body and
its character can change. No derivative of a sign function is used. -/
 theorem walsh_quadrilateral_le (A B E : Set E4)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hAf : volume A ≠ ⊤) (hBf : volume B ≠ ⊤) (hEf : volume E ≠ ⊤)
    (c d : HyperplaneCfg) (I : Walsh4.Index)
    (hsupport : forall x, x ∈ symmDiff A B ->
      Cells.signCharacter c I x ≠ Cells.signCharacter d I x -> x ∈ E) :
    |(walsh (volume.restrict A) c I - walsh (volume.restrict B) c I) -
      (walsh (volume.restrict A) d I - walsh (volume.restrict B) d I)|
      ≤ 2 * volume.real E := by
  classical
  let f := Cells.signCharacter c I
  let g := Cells.signCharacter d I
  let F : E4 -> Real := fun x =>
    (A.indicator f x - B.indicator f x) - (A.indicator g x - B.indicator g x)
  have hIAf : Integrable (A.indicator f) volume :=
    (integrable_indicator_iff hA).mpr (integrable_signCharacter_restrict A hAf c I)
  have hIBf : Integrable (B.indicator f) volume :=
    (integrable_indicator_iff hB).mpr (integrable_signCharacter_restrict B hBf c I)
  have hIAg : Integrable (A.indicator g) volume :=
    (integrable_indicator_iff hA).mpr (integrable_signCharacter_restrict A hAf d I)
  have hIBg : Integrable (B.indicator g) volume :=
    (integrable_indicator_iff hB).mpr (integrable_signCharacter_restrict B hBf d I)
  have hIF : Integrable F volume := (hIAf.sub hIBf).sub (hIAg.sub hIBg)
  have hIK := integrable_indicator_const_finite E hE hEf 2
  have hfg (x : E4) : |f x - g x| ≤ 2 := by
    calc
      |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
      _ = 2 := by norm_num [f, g, Cells.signCharacter, Walsh4.abs_char]
  have hpoint : forall x, norm (F x) ≤ E.indicator (fun _ => (2 : Real)) x := by
    intro x
    have hformula : F x = ((if x ∈ A then (1 : Real) else 0) -
        (if x ∈ B then (1 : Real) else 0)) * (f x - g x) := by
      by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
        simp [F, hxA, hxB] <;> ring
    by_cases hxE : x ∈ E
    · rw [Set.indicator_of_mem hxE, Real.norm_eq_abs, hformula, abs_mul]
      by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B
      · simp [hxA, hxB]
      · simpa [hxA, hxB] using hfg x
      · simpa [hxA, hxB] using hfg x
      · simp [hxA, hxB]
    · have hzero : F x = 0 := by
        by_cases hfg0 : f x = g x
        · rw [hformula, hfg0, sub_self, mul_zero]
        · have hsd : x ∉ symmDiff A B := fun hx => hxE (hsupport x hx hfg0)
          rw [Set.mem_symmDiff] at hsd
          by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
            simp_all [hformula]
      simp [hxE, hzero]
  have hIntegral : (∫ x, F x) =
      (walsh (volume.restrict A) c I - walsh (volume.restrict B) c I) -
      (walsh (volume.restrict A) d I - walsh (volume.restrict B) d I) := by
    have h1 : (∫ x, A.indicator f x - B.indicator f x) = walsh (volume.restrict A) c I - walsh (volume.restrict B) c I := by
      rw [integral_sub hIAf hIBf, integral_indicator hA, integral_indicator hB]
      rfl
    have h2 : (∫ x, A.indicator g x - B.indicator g x) = walsh (volume.restrict A) d I - walsh (volume.restrict B) d I := by
      rw [integral_sub hIAg hIBg, integral_indicator hA, integral_indicator hB]
      rfl
    have hF_eq : F = (fun x => A.indicator f x - B.indicator f x) - (fun x => A.indicator g x - B.indicator g x) := rfl
    have hF_int : (∫ x, F x) = (∫ x, A.indicator f x - B.indicator f x) - (∫ x, A.indicator g x - B.indicator g x) := by
      conv_lhs => rw [hF_eq]
      exact integral_sub (hIAf.sub hIBf) (hIAg.sub hIBg)
    rw [hF_int, h1, h2]
  rw [← hIntegral]
  calc
    |∫ x, F x| = norm (∫ x, F x) := by rw [Real.norm_eq_abs]
    _ ≤ ∫ x, norm (F x) := norm_integral_le_integral_norm _
    _ ≤ ∫ x, E.indicator (fun _ => (2 : Real)) x := integral_mono hIF.norm hIK hpoint
    _ = 2 * volume.real E := by
      rw [integral_indicator hE]
      simp [Measure.real, smul_eq_mul, mul_comm]

/-- One scalar Walsh coefficient satisfies the shell estimate uniformly in
its index, including low indices. -/
 theorem scalar_shell_stability (tau eps B M : Real) (hB : 0 < B) (hM : 0 < M)
    (hsmall : |eps| * B ≤ 1/2)
    (hbound : forall u : E4, norm u = 1 -> |angularPerturbation tau u| ≤ B)
    (c : HyperplaneCfg) (q : Fin 4 -> E4) (hq : Tensors.IsONFrame q)
    (hoff : forall i, |c.offset i| ≤ M*|eps|)
    (hnormal : forall i, norm (c.normal i - q i) ≤ M*|eps|)
    (I : Walsh4.Index) :
    |(walsh (radialMeasure tau eps) c I -
        walsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c I) -
      (walsh (radialMeasure tau eps) ⟨q, fun _ => 0⟩ I -
        walsh (volume.restrict (Metric.closedBall (0 : E4) 1)) ⟨q, fun _ => 0⟩ I)|
      ≤ 1536 * B * M * eps^2 := by
  let E := shellStrips (1-|eps| * B) (1+|eps| * B) q (6*M*|eps|)
  have heB : 0 ≤ |eps| * B := mul_nonneg (abs_nonneg eps) hB.le
  have hEbound : volume E ≤ ENNReal.ofReal (768*B*M*eps^2) := by
    have h := volume_shellStrips_le (1-|eps| * B) (1+|eps| * B)
      (by linarith) (by linarith) q hq (6*M*|eps|) (by positivity)
    have heq : 64*(6*M*|eps|)*((1+|eps| * B)-(1-|eps| * B)) = 768*B*M*eps^2 := by
      calc
        64*(6*M*|eps|)*((1+|eps| * B)-(1-|eps| * B)) =
            768*B*M*(|eps|^2) := by ring
        _ = 768*B*M*eps^2 := by rw [sq_abs]
    simpa only [E, heq] using h
  have hEf : volume E ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hEbound ENNReal.ofReal_lt_top)
  have hEr : volume.real E ≤ 768*B*M*eps^2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEbound
    simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ 768*B*M*eps^2)] using h
  have hAf : volume (radialSet tau eps) ≠ ⊤ := by
    exact ne_of_lt ((measure_mono (radialSet_subset_ball_two tau eps B hB hsmall hbound)).trans_lt
      (isCompact_closedBall (0 : E4) 2).measure_lt_top)
  have hBf : volume (Metric.closedBall (0 : E4) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : E4) 1).measure_lt_top.ne
  have h := walsh_quadrilateral_le (radialSet tau eps) (Metric.closedBall (0 : E4) 1) E
    (measurableSet_radialSet tau eps) measurableSet_closedBall
    (measurableSet_shellStrips _ _ _ _) hAf hBf hEf c ⟨q, fun _ => 0⟩ I
    (changed_character_mem_shellStrips tau eps B M hB hM hsmall hbound c q hoff hnormal I)
  have hfinal := h.trans (mul_le_mul_of_nonneg_left hEr (by norm_num : (0 : Real) ≤ 2))
  have hcalc : 2 * (768 * B * M * eps^2) = 1536 * B * M * eps^2 := by ring
  rw [hcalc] at hfinal
  exact hfinal

 theorem norm_five_le (v : E5) (a : Real) (ha : 0 ≤ a)
    (hcoord : forall i, |v i| ≤ a) : norm v ≤ 5*a := by
  have hsq (i : Fin 5) : (v i)^2 ≤ a^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (v i)) (hcoord i) 2
  have hsum : (∑ i : Fin 5, (v i)^2) ≤ 5*a^2 := by
    calc
      (∑ i : Fin 5, (v i)^2) ≤ ∑ _i : Fin 5, a^2 := Finset.sum_le_sum (fun i _ => hsq i)
      _ = 5*a^2 := by simp
  have hn : norm v ^ 2 ≤ (5*a)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    nlinarith [sq_nonneg a]
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : Nat) ≠ 0) (by positivity) hn

/-- The named estimate used by the original expansion theorem. -/
 theorem high_shell_stability (tau M : Real) (hM : 0 < M) :
    ∃ eps0 C : Real, 0 < eps0 ∧ 0 < C ∧
      forall eps c q, |eps| < eps0 -> UnitCfg c -> Tensors.IsONFrame q ->
        (forall i, |c.offset i| ≤ M*|eps|) ->
        (forall i, norm (c.normal i - q i) ≤ M*|eps|) ->
        norm ((highWalsh (radialMeasure tau eps) c -
          highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c) -
          (highWalsh (radialMeasure tau eps) ⟨q, fun _ => 0⟩ -
          highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) ⟨q, fun _ => 0⟩))
          ≤ C*eps^2 := by
  obtain ⟨B, hB, hbound⟩ := angularPerturbation_bounded_on_sphere tau
  refine ⟨1/(2*B), 7680*B*M, by positivity, by positivity, ?_⟩
  intro eps c q heps _hunit hq hoff hnormal
  have heB : |eps| * B ≤ 1/2 := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num) hB)).mp heps
    nlinarith
  have h := norm_five_le
    ((highWalsh (radialMeasure tau eps) c -
      highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) c) -
      (highWalsh (radialMeasure tau eps) ⟨q, fun _ => 0⟩ -
      highWalsh (volume.restrict (Metric.closedBall (0 : E4) 1)) ⟨q, fun _ => 0⟩))
    (1536*B*M*eps^2) (by positivity) (by
      intro i
      fin_cases i
      · simpa [highWalsh, PiLp.sub_apply, PiLp.toLp_apply] using
          scalar_shell_stability tau eps B M hB hM heB hbound c q hq hoff hnormal {1,2,3}
      · simpa [highWalsh, PiLp.sub_apply, PiLp.toLp_apply] using
          scalar_shell_stability tau eps B M hB hM heB hbound c q hq hoff hnormal {0,2,3}
      · simpa [highWalsh, PiLp.sub_apply, PiLp.toLp_apply] using
          scalar_shell_stability tau eps B M hB hM heB hbound c q hq hoff hnormal {0,1,3}
      · simpa [highWalsh, PiLp.sub_apply, PiLp.toLp_apply] using
          scalar_shell_stability tau eps B M hB hM heB hbound c q hq hoff hnormal {0,1,2}
      · simpa [highWalsh, PiLp.sub_apply, PiLp.toLp_apply] using
          scalar_shell_stability tau eps B M hB hM heB hbound c q hq hoff hnormal {0,1,2,3})
  nlinarith only [h]

end ShellBounds
end SoberonConvexBody
