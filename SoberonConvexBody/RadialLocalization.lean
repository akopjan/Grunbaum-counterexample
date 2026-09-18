import SoberonConvexBody.BallLocalization
import SoberonConvexBody.Stability

/-!
# Transfer of localization from the ball to the radial model

The annulus bound is explicit, including the case eps = 0. The comparison
applies to arbitrary configurations, not just centered or independent normals.
-/
noncomputable section
namespace SoberonConvexBody.RadialLocalization
open Set MeasureTheory
open scoped BigOperators
open Tensors SphereGeometry ShellBounds BallLocal

theorem volume_radial_symmDiff_le (tau eps B : Real) (hB : 0 < B)
    (hsmall : |eps| * B ≤ 1/2)
    (hbound : forall u : E4, norm u=1 -> |angularPerturbation tau u| ≤ B) :
    volume (symmDiff (radialSet tau eps) (Metric.closedBall (0 : E4) 1))
      ≤ ENNReal.ofReal (128*B*|eps|) := by
  have hq : IsONFrame coordinateVector := by
    intro i j
    simp only [inner_coordinateVector_left,coordinateVector_apply]
  let E : Set E4 := shellStrips (1 - |eps| * B) (1 + |eps| * B) coordinateVector 1
  have hsub : symmDiff (radialSet tau eps) (Metric.closedBall (0 : E4) 1) ⊆ E := by
    intro x hx
    have hband := radial_symmDiff_band tau eps B hB hbound hx
    have hnorm := radial_symmDiff_norm_bounds tau eps B hB hsmall hbound hx
    have hx0 : x ≠ 0 := by intro hz; simp [hz] at hnorm; linarith
    refine ⟨hband.1,hband.2,0,?_⟩
    have h := abs_real_inner_le_norm (direction x) (coordinateVector 0)
    simpa only [norm_direction hx0,hq.norm_eq_one,mul_one] using h
  have heB : 0 ≤ |eps| * B := mul_nonneg (abs_nonneg eps) hB.le
  calc
    volume (symmDiff (radialSet tau eps) (Metric.closedBall (0 : E4) 1))
        ≤ volume E := measure_mono hsub
    _ ≤ ENNReal.ofReal (64*1*((1 + |eps| * B)-(1 - |eps| * B))) :=
      volume_shellStrips_le _ _ (by linarith) (by linarith) coordinateVector hq 1 (by norm_num)
    _ = ENNReal.ofReal (128*B*|eps|) := by congr 1; ring

theorem walsh_radial_ball_le (tau eps B : Real) (hB : 0 < B)
    (hsmall : |eps| * B ≤ 1/2)
    (hbound : forall u : E4, norm u=1 -> |angularPerturbation tau u| ≤ B)
    (c : HyperplaneCfg) (I : Walsh4.Index) :
    |walsh (radialMeasure tau eps) c I-walsh ballMeasure c I|
      ≤ 2048*B*|eps| := by
  have hball2 : volume (Metric.closedBall (0 : E4) 2) < ⊤ :=
    (isCompact_closedBall (0 : E4) 2).measure_lt_top
  have hrad : volume (radialSet tau eps) ≠ ⊤ :=
    ne_of_lt ((measure_mono (radialSet_subset_ball_two tau eps B hB hsmall hbound)).trans_lt hball2)
  have hball : volume (Metric.closedBall (0 : E4) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : E4) 1).measure_lt_top.ne
  have hsd := volume_radial_symmDiff_le tau eps B hB hsmall hbound
  have hsdFin : volume (symmDiff (radialSet tau eps) (Metric.closedBall (0 : E4) 1)) ≠ ⊤ :=
    ne_of_lt (hsd.trans_lt ENNReal.ofReal_lt_top)
  have hreal : volume.real (symmDiff (radialSet tau eps) (Metric.closedBall (0 : E4) 1))
      ≤ 128*B*|eps| := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsd
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 128*B*|eps|)] at h
    exact h
  have h := abs_walsh_restrict_sub_le_symmDiff c I hrad hball hsdFin
  change |walsh (radialMeasure tau eps) c I-walsh ballMeasure c I|
      ≤ 16*volume.real (symmDiff (radialSet tau eps) (Metric.closedBall (0 : E4) 1)) at h
  nlinarith only [h,hreal]

theorem robust_localization (tau A : Real) (hA : 0 ≤ A) :
    ∃ eps0 C : Real, 0 < eps0 ∧ 0 < C ∧
      forall eps c, |eps| < eps0 -> UnitCfg c ->
        (forall I : Walsh4.Index, I.Nonempty -> I.card ≤ 2 ->
          |walsh (radialMeasure tau eps) c I| ≤ A*eps^2) ->
        ∃ q : Fin 4 -> E4, IsONFrame q ∧
          (forall i, |c.offset i| ≤ C*|eps|) ∧
          (forall i, norm (c.normal i-q i) ≤ C*|eps|) := by
  obtain ⟨B,hB,hbound⟩ := angularPerturbation_bounded_on_sphere tau
  obtain ⟨b0,K,hb0,hK,hloc⟩ := BallLocalization.localization
  let L : Real := A+2048*B
  have hL : 0 < L := by dsimp [L]; positivity
  let eps0 : Real := min (min 1 (1/(2*B))) (b0/L)
  have heps0 : 0 < eps0 := by dsimp [eps0]; positivity
  refine ⟨eps0,K*L,heps0,mul_pos hK hL,?_⟩
  intro eps c heps hc hlow
  have he1 : |eps| < 1 := lt_of_lt_of_le heps ((min_le_left _ _).trans (min_le_left _ _))
  have heB : |eps| < 1/(2*B) := lt_of_lt_of_le heps ((min_le_left _ _).trans (min_le_right _ _))
  have heL : |eps| < b0/L := lt_of_lt_of_le heps (min_le_right _ _)
  have hsmall : |eps| * B ≤ 1/2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2*B)).mp heB
    nlinarith only [h]
  have he2 : eps^2 ≤ |eps| := by
    have h := mul_le_mul_of_nonneg_left he1.le (abs_nonneg eps)
    nlinarith only [h,sq_abs eps]
  have hle (I : Walsh4.Index) (hI : I.Nonempty) (hcard : I.card ≤ 2) :
      |walsh ballMeasure c I| ≤ L*|eps| := by
    have hdiff := walsh_radial_ball_le tau eps B hB hsmall hbound c I
    have hr := hlow I hI hcard
    have hr' := mul_le_mul_of_nonneg_left he2 hA
    have ht : |walsh ballMeasure c I| ≤
        |walsh (radialMeasure tau eps) c I-walsh ballMeasure c I|+
        |walsh (radialMeasure tau eps) c I| := by
      have hid : walsh ballMeasure c I =
          -(walsh (radialMeasure tau eps) c I-walsh ballMeasure c I)+
            walsh (radialMeasure tau eps) c I := by ring
      conv_lhs => rw [hid]
      have h1 := abs_add_le (-(walsh (radialMeasure tau eps) c I - walsh ballMeasure c I))
        (walsh (radialMeasure tau eps) c I)
      rw [abs_neg] at h1
      exact h1
    dsimp [L]
    nlinarith only [hdiff,hr,hr',ht]
  have hbsmall : L*|eps| < b0 := by
    have h := (lt_div_iff₀ hL).mp heL
    nlinarith only [h]
  obtain ⟨q,hq,hoff,hnormal⟩ := hloc (L*|eps|) c (by positivity) hbsmall hc hle
  refine ⟨q,hq,?_,?_⟩
  · intro i
    simpa only [mul_assoc] using hoff i
  · intro i
    simpa only [mul_assoc] using hnormal i

end SoberonConvexBody.RadialLocalization
