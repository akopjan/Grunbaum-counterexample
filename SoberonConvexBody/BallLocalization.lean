import SoberonConvexBody.BallCompactness
import SoberonConvexBody.QuantitativeFrame

/-!
# Linear localization from small low coefficients

The only compactness step gives a qualitative neighborhood. Inside that
neighborhood, the explicit coefficient estimates and Gram--Schmidt estimate
absorb the quadratic remainder and give a linear bound.
-/
noncomputable section
namespace SoberonConvexBody.BallLocalization
open Set MeasureTheory
open scoped BigOperators
open Tensors SphereGeometry BallLocal BallCompactness

/-- A genuine finite minimum of the positive coordinate integrals. -/
def momentMinimum : Real :=
  (Finset.univ : Finset Walsh4.Index).inf' Finset.univ_nonempty coordinateMoment

theorem momentMinimum_pos : 0 < momentMinimum := by
  apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
  intro I _
  exact coordinateMoment_pos I

theorem momentMinimum_le (I : Walsh4.Index) : momentMinimum ≤ coordinateMoment I := by
  exact Finset.inf'_le coordinateMoment (Finset.mem_univ I)

/-- Scalar extraction of a leading coefficient without dividing by a variable. -/
theorem leading_term_bound (w a y b r m : Real)
    (hm : 0 ≤ m) (ha : m/2 ≤ a)
    (hw : |w| ≤ b) (he : |w-a*y| ≤ r) :
    m*|y| ≤ 2*b+2*r := by
  have ha0 : 0 ≤ a := by linarith
  have ht : |a*y| ≤ |w-a*y|+|w| := by
    have hid : a*y = -(w-a*y)+w := by ring
    conv_lhs => rw [hid]
    have h1 := abs_add_le (-(w-a*y)) w
    rw [abs_neg] at h1
    exact h1
  rw [abs_mul,abs_of_nonneg ha0] at ht
  have hm' := mul_le_mul_of_nonneg_right ha (abs_nonneg y)
  linarith

/-- The sum defect is linearly controlled by the low coefficients of the ball. -/
theorem localization :
    ∃ b0 C : Real, 0 < b0 ∧ 0 < C ∧
      forall b c, 0 ≤ b -> b < b0 -> UnitCfg c ->
        (forall I : Walsh4.Index, I.Nonempty -> I.card ≤ 2 ->
          |walsh ballMeasure c I| ≤ b) ->
        ∃ q : Fin 4 -> E4, IsONFrame q ∧
          (forall i, |c.offset i| ≤ C*b) ∧
          (forall i, norm (c.normal i-q i) ≤ C*b) := by
  classical
  obtain ⟨delta,hdelta,hcoeff⟩ := coefficient_estimates
  let m : Real := momentMinimum
  let K : Real := remainderConstant
  have hm : 0 < m := momentMinimum_pos
  have hK : 0 < K := remainderConstant_pos
  let zeta : Real := min (min (1/100) (delta/26)) (m/(54080*K))
  have hzeta : 0 < zeta := by dsimp [zeta]; positivity
  obtain ⟨r0,hr0,hqual⟩ := small_residual_small_deviation zeta hzeta
  let b0 : Real := min (ballVolume/2) (r0/32)
  have hb0 : 0 < b0 := by
    have hv := ballVolume_pos
    dsimp [b0]
    positivity
  have hC : 0 < 2080/m := by positivity
  refine ⟨b0,2080/m,hb0,hC,?_⟩
  intro b c hb hsmall hc hlow
  have hbvol : b < ballVolume := by
    have h : b < ballVolume/2 := lt_of_lt_of_le hsmall (min_le_left _ _)
    linarith [ballVolume_pos]
  have hoff2 : forall i, |c.offset i| ≤ 2 :=
    offsets_bounded_of_small_low c hc b hbvol
      (fun i => hlow {i} (Finset.singleton_nonempty i) (by simp))
  have hpc : param c ∈ compactConfigs := (mem_compactConfigs _).mpr ⟨hc,hoff2⟩
  have hres : lowResidual (param c) < r0 := by
    have h := lowResidual_le (param c) b hb (by simpa using hlow)
    have hb' : b < r0/32 := lt_of_lt_of_le hsmall (min_le_right _ _)
    linarith
  let gamma : Real := deviation (param c)
  have hg : 0 ≤ gamma := deviation_nonneg _
  have hgz : gamma < zeta := hqual (param c) hpc hres
  have hgnum : gamma < 1/100 :=
    lt_of_lt_of_le hgz ((min_le_left _ _).trans (min_le_left _ _))
  have hgdelta : gamma < delta/26 :=
    lt_of_lt_of_le hgz ((min_le_left _ _).trans (min_le_right _ _))
  have hgabsorb : gamma < m/(54080*K) := lt_of_lt_of_le hgz (min_le_right _ _)
  have hgoff (i : Fin 4) : |c.offset i| ≤ gamma := offset_le_deviation (param c) i
  have hgpair (i j : Fin 4) (hij : i ≠ j) :
      |inner Real (c.normal i) (c.normal j)| ≤ gamma :=
    inner_le_deviation (param c) i j hij
  obtain ⟨q,hq,hnq⟩ := QuantitativeFrame.near_orthonormal gamma hg hgnum c.normal hc hgpair
  have hd : 0 ≤ 26*gamma := by positivity
  have hdsmall : 26*gamma < delta := by linarith
  obtain ⟨J,hJlo,hJhi,hs,hp,_hh⟩ := hcoeff (26*gamma) c q hd hdsmall hq
    (fun i => (hgoff i).trans (by linarith)) hnq
  have hJpos : 0 ≤ J := by linarith
  have hlead (I : Walsh4.Index) : m/2 ≤ J*coordinateMoment I := by
    have hM := momentMinimum_le I
    have hMpos := (coordinateMoment_pos I).le
    have hmul := mul_le_mul hJlo hM hm.le hJpos
    nlinarith
  let T : Real := 2*b+2*(K*(26*gamma)^2)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hsing (i : Fin 4) : m*|c.offset i| ≤ T := by
    have h := leading_term_bound (walsh ballMeasure c {i})
      (J*coordinateMoment {i}) (-c.offset i) b (K*(26*gamma)^2) m hm.le (hlead {i})
      (hlow {i} (Finset.singleton_nonempty i) (by simp)) (by simpa only [mul_neg,sub_neg_eq_add] using hs i)
    simpa only [abs_neg] using h
  have hpair (i j : Fin 4) (hij : i ≠ j) :
      m*|inner Real (c.normal i) (c.normal j)| ≤ T := by
    exact leading_term_bound _ _ _ _ _ _ hm.le (hlead {i,j})
      (hlow {i,j} (Finset.insert_nonempty i _) (by simp [hij])) (hp i j hij)
  have hsum : m*gamma ≤ 20*T := by
    calc
      m*gamma = (∑ i : Fin 4, m*|c.offset i|)+
          ∑ i : Fin 4, ∑ j : Fin 4,
            m*(if i=j then 0 else |inner Real (c.normal i) (c.normal j)|) := by
              simp only [gamma,deviation,param,mul_add,Finset.mul_sum]
      _ ≤ (∑ _i : Fin 4, T)+∑ _i : Fin 4, ∑ _j : Fin 4, T := by
        apply add_le_add
        · exact Finset.sum_le_sum (fun i _ => hsing i)
        · apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          by_cases hij : i=j
          · simpa only [if_pos hij,mul_zero] using hT
          · simpa only [if_neg hij] using hpair i j hij
      _ = 20*T := by norm_num; ring
  have hquadratic : 54080*K*gamma^2 ≤ m*gamma := by
    have h1 : gamma*(54080*K) < m := (lt_div_iff₀ (by positivity : 0 < 54080*K)).mp hgabsorb
    have h2 := mul_le_mul_of_nonneg_right h1.le hg
    nlinarith only [h2]
  have hglinear : gamma ≤ 80*b/m := by
    apply (le_div_iff₀ hm).mpr
    dsimp [T] at hsum
    nlinarith only [hsum,hquadratic]
  refine ⟨q,hq,?_,?_⟩
  · intro i
    calc
      |c.offset i| ≤ gamma := hgoff i
      _ ≤ 80*b/m := hglinear
      _ ≤ (2080/m)*b := by
        have h1 : (80 * b) ≤ 2080 * b := by nlinarith
        have h2 : (80 * b) / m ≤ (2080 * b) / m := div_le_div_of_nonneg_right h1 hm.le
        have h3 : (2080 * b) / m = (2080 / m) * b := by ring
        linarith
  · intro i
    calc
      norm (c.normal i-q i) ≤ 26*gamma := hnq i
      _ ≤ 26*(80*b/m) := mul_le_mul_of_nonneg_left hglinear (by norm_num)
      _ = (2080/m)*b := by ring

end SoberonConvexBody.BallLocalization
