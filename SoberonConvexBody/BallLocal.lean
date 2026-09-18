import SoberonConvexBody.AffineBall
import SoberonConvexBody.ShellStability

/-!
# Simultaneous low and high coefficient estimates near an orthogonal frame

The Jacobian is the determinant of the explicitly constructed coordinate map.
The low coefficients detect offsets and pairwise scalar products; the high
coefficients have no terms of degree zero or one.
-/
noncomputable section
namespace SoberonConvexBody.BallLocal
open Set MeasureTheory
open scoped BigOperators
open Tensors SphereGeometry NearIdentity Ellipsoid

def ballMeasure : Measure E4 := volume.restrict (Metric.closedBall (0 : E4) 1)

theorem coordinateMoment_le_total (I : Walsh4.Index) :
    coordinateMoment I ≤ sphereVolume.real Set.univ := by
  calc
    coordinateMoment I ≤ ∫ _u : UnitSphere, (1 : Real) ∂sphereVolume :=
      integral_mono (integrable_absCoordinateProduct I) (integrable_const _)
        (absCoordinateProduct_le_one I)
    _ = sphereVolume.real Set.univ := by simp [integral_const,smul_eq_mul]

theorem isometry_coordinateVector (q : Fin 4 -> E4) (hq : IsONFrame q) (j : Fin 4) :
    hq.toIsometry (coordinateVector j) = q j := by
  rw [IsONFrame.toIsometry_apply]
  fin_cases j <;> simp [coordinateVector_apply,linearCombination4]

theorem errorMatrix_normal (c : HyperplaneCfg) (q : Fin 4 -> E4) (hq : IsONFrame q)
    (e : E4 ≃ₗ[Real] E4) (he : forall x, e x = normalMap hq c.normal x)
    (i j : Fin 4) :
    errorMatrix e i j = inner Real (c.normal i) (q j) - if i=j then 1 else 0 := by
  simp [errorMatrix,he,normalMap_apply,isometry_coordinateVector,real_inner_comm]

theorem pair_gram_error (c : HyperplaneCfg) (q : Fin 4 -> E4) (hq : IsONFrame q)
    (e : E4 ≃ₗ[Real] E4) (he : forall x, e x = normalMap hq c.normal x)
    (d : Real) (hd : 0 ≤ d) (hn : forall i, norm (c.normal i-q i) ≤ d)
    (i j : Fin 4) (hij : i ≠ j) :
    |inner Real (c.normal i) (c.normal j)-(errorMatrix e i j+errorMatrix e j i)| ≤ d^2 := by
  have hid : inner Real (c.normal i) (c.normal j)-(errorMatrix e i j+errorMatrix e j i) =
      inner Real (c.normal i-q i) (c.normal j-q j) := by
    rw [errorMatrix_normal c q hq e he, errorMatrix_normal c q hq e he]
    simp only [if_neg hij,if_neg (Ne.symm hij),sub_zero,inner_sub_left,inner_sub_right,
      hq i j,if_neg hij,real_inner_comm (q i) (c.normal j)]
    ring
  rw [hid]
  calc
    |inner Real (c.normal i-q i) (c.normal j-q j)| ≤
        norm (c.normal i-q i)*norm (c.normal j-q j) := abs_real_inner_le_norm _ _
    _ ≤ d*d := mul_le_mul (hn i) (hn j) (norm_nonneg _) hd
    _ = d^2 := by ring

/-- A single uniform constant works for all fifteen characters. -/
def remainderConstant : Real := 1000000 * (sphereVolume.real Set.univ+1)

theorem remainderConstant_pos : 0 < remainderConstant := by
  unfold remainderConstant
  have h : 0 ≤ sphereVolume.real Set.univ := ENNReal.toReal_nonneg
  positivity

/-- Local expansion with the real Jacobian retained in the leading terms. -/
theorem coefficient_estimates :
    ∃ delta : Real, 0 < delta ∧
      forall d c q, 0 ≤ d -> d < delta -> IsONFrame q ->
        (forall i, |c.offset i| ≤ d) -> (forall i, norm (c.normal i-q i) ≤ d) ->
        ∃ J : Real, 1/2 ≤ J ∧ J ≤ 2 ∧
          (forall i, |walsh ballMeasure c {i}+J*coordinateMoment {i}*c.offset i|
            ≤ remainderConstant*d^2) ∧
          (forall i j, i ≠ j ->
            |walsh ballMeasure c {i,j}-J*coordinateMoment {i,j}*
              inner Real (c.normal i) (c.normal j)| ≤ remainderConstant*d^2) ∧
          (forall I : Walsh4.Index, 3 ≤ I.card ->
            |walsh ballMeasure c I| ≤ remainderConstant*d^2) := by
  obtain ⟨eta,heta,hjac⟩ := exists_jacobian_neighborhood
  let delta : Real := min (eta/8) (1/10000)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  refine ⟨delta,hdelta,?_⟩
  intro d c q hd hsmall hq hoff hnormal
  have hdnum : d < 1/10000 := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hdeta : 4*d < eta := by
    have h : d < eta/8 := lt_of_lt_of_le hsmall (min_le_left _ _)
    linarith
  let A : E4 →ₗ[Real] E4 := normalMap hq c.normal
  have hA : forall x, norm (A x-x) ≤ (4*d)*norm x := by
    intro x
    exact normalMap_error hq c.normal d hd hnormal x
  have hk : 4*d < 1 := by linarith
  let e := equivalence A (4*d) hk hA
  have he : forall x, e x = normalMap hq c.normal x := by intro x; rfl
  have he' : forall x, norm (e x-x) ≤ (4*d)*norm x := hA
  have hj : 1/2 ≤ jacobian e ∧ jacobian e ≤ 2 :=
    hjac e ((opNorm_error e (4*d) (by positivity) he').trans_lt hdeta)
  let t : E4 := WithLp.toLp 2 c.offset
  have ht : forall i, t i = c.offset i := by intro i; rfl
  have htn : norm t ≤ 4*d := norm_four_le t d hd hoff
  have hbeta : 4*d ≤ 1/800 := by linarith
  have hc : coeffC e t < 1 := by
    have hbt := inverse_norm_le e (4*d) (by linarith) he' t
    have hbt' : norm (e.symm t) ≤ 8*d := by linarith
    unfold coeffC
    nlinarith [norm_nonneg (e.symm t)]
  let J := jacobian e
  have hJ0 : 0 ≤ J := (jacobian_pos e).le
  have htotal : 0 ≤ sphereVolume.real Set.univ := ENNReal.toReal_nonneg
  have hmain (I : Walsh4.Index) :
      |walsh ballMeasure c I-(J/4)*
        (∫ u : UnitSphere, coordinateCharacter I u * firstPolynomial e t u ∂sphereVolume)|
        ≤ 104000*sphereVolume.real Set.univ*d^2 := by
    rw [show walsh ballMeasure c I = (J/4)*
        (∫ u : UnitSphere, coordinateCharacter I u * radius e t u ^ 4 ∂sphereVolume) from
      walsh_ball_eq_sphere c q hq e he t ht hc I]
    rw [← mul_sub,abs_mul,abs_of_nonneg (div_nonneg hJ0 (by norm_num))]
    have h := integral_radius_remainder e t (4*d) (by positivity) hbeta he' htn I
    have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ J/4)
    have hjbound : J/4 ≤ 1/2 := by dsimp [J]; linarith [hj.2]
    have hm2 := mul_le_mul_of_nonneg_right hjbound
      (by positivity : 0 ≤ sphereVolume.real Set.univ * (13000*(4*d)^2))
    nlinarith
  refine ⟨J,hj.1,hj.2,?_,?_,?_⟩
  · intro i
    have hi := hmain {i}
    rw [firstPolynomial,integral_character_quadraticSphere_singleton] at hi
    have hid : walsh ballMeasure c {i}-(J/4)*((-4*t i)*coordinateMoment {i}) =
        walsh ballMeasure c {i}+J*coordinateMoment {i}*c.offset i := by rw [ht]; ring
    rw [hid] at hi
    have hcst : 104000*sphereVolume.real Set.univ*d^2 ≤ remainderConstant*d^2 := by
      unfold remainderConstant
      nlinarith [sq_nonneg d, mul_nonneg htotal (sq_nonneg d)]
    exact hi.trans hcst
  · intro i j hij
    have hi := hmain {i,j}
    rw [firstPolynomial,integral_character_quadraticSphere_pair i j hij] at hi
    have hgram := pair_gram_error c q hq e he d hd hnormal i j hij
    have hM := coordinateMoment_le_total ({i,j} : Walsh4.Index)
    have hM0 : 0 ≤ coordinateMoment ({i,j} : Walsh4.Index) := (coordinateMoment_pos _).le
    have hlinear : |J*coordinateMoment {i,j}*
        ((errorMatrix e i j+errorMatrix e j i)-inner Real (c.normal i) (c.normal j))|
        ≤ 2*sphereVolume.real Set.univ*d^2 := by
      rw [abs_mul,abs_mul,abs_of_nonneg hJ0,abs_of_nonneg hM0,abs_sub_comm]
      have hm1 := mul_le_mul hj.2 hM hM0 (by norm_num : (0 : Real) ≤ 2)
      have hm2 := mul_le_mul hm1 hgram (abs_nonneg _) (by positivity : 0 ≤ 2*sphereVolume.real Set.univ)
      nlinarith
    have hid : walsh ballMeasure c {i,j}-J*coordinateMoment {i,j}*
        inner Real (c.normal i) (c.normal j) =
        (walsh ballMeasure c {i,j}-(J/4)*
          ((4*errorMatrix e i j+4*errorMatrix e j i)*coordinateMoment {i,j}))+
        J*coordinateMoment {i,j}*
          ((errorMatrix e i j+errorMatrix e j i)-inner Real (c.normal i) (c.normal j)) := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    unfold remainderConstant
    nlinarith [sq_nonneg d, mul_nonneg htotal (sq_nonneg d)]
  · intro I hI
    have hi := hmain I
    rw [firstPolynomial,integral_character_quadraticSphere_high I hI,mul_zero,sub_zero] at hi
    apply hi.trans
    unfold remainderConstant
    nlinarith [sq_nonneg d, mul_nonneg htotal (sq_nonneg d)]

theorem high_quadratic_flatness :
    ∃ delta C : Real, 0 < delta ∧ 0 < C ∧
      forall d c q, 0 ≤ d -> d < delta -> UnitCfg c -> IsONFrame q ->
        (forall i, |c.offset i| ≤ d) -> (forall i, norm (c.normal i-q i) ≤ d) ->
        norm (highWalsh ballMeasure c) ≤ C*d^2 := by
  obtain ⟨delta,hdelta,hest⟩ := coefficient_estimates
  refine ⟨delta,5*remainderConstant,hdelta,mul_pos (by norm_num) remainderConstant_pos,?_⟩
  intro d c q hd hsmall _hunit hq ht hn
  obtain ⟨J,hJlo,hJhi,hs,hp,hh⟩ := hest d c q hd hsmall hq ht hn
  have h := ShellBounds.norm_five_le (highWalsh ballMeasure c) (remainderConstant*d^2)
    (mul_nonneg remainderConstant_pos.le (sq_nonneg d)) (by
      intro i
      fin_cases i
      · simpa [highWalsh,PiLp.toLp_apply] using hh {1,2,3} (by decide)
      · simpa [highWalsh,PiLp.toLp_apply] using hh {0,2,3} (by decide)
      · simpa [highWalsh,PiLp.toLp_apply] using hh {0,1,3} (by decide)
      · simpa [highWalsh,PiLp.toLp_apply] using hh {0,1,2} (by decide)
      · simpa [highWalsh,PiLp.toLp_apply] using hh {0,1,2,3} (by decide))
  nlinarith only [h]

end SoberonConvexBody.BallLocal
