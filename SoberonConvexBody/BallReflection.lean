import SoberonConvexBody.BallLocal

/-!
# Qualitative rigidity of the low Walsh equations on a ball

A reflection in the first normal proves that the centered pair coefficient
has the sign of the scalar product of the two normals. Strictness follows
from an explicit nonempty open set, rather than an arcsine integration formula.
-/
noncomputable section
namespace SoberonConvexBody.BallReflection
open Set MeasureTheory
open scoped BigOperators
open Tensors SphereGeometry BallLocal

instance ballMeasure_finite : IsFiniteMeasure ballMeasure := by
  letI : Fact ((volume : Measure E4) (Metric.closedBall 0 1) < ⊤) :=
    ⟨(isCompact_closedBall (0 : E4) 1).measure_lt_top⟩
  exact MeasureTheory.Restrict.isFiniteMeasure volume

def normalKernel (a : E4) : Submodule Real E4 where
  carrier := {x | inner Real x a=0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change inner Real x a=0 at hx
    change inner Real y a=0 at hy
    change inner Real (x+y) a=0
    simp only [inner_add_left,hx,hy,add_zero]
  smul_mem' := by
    intro r x hx
    change inner Real x a=0 at hx
    change inner Real (r • x) a=0
    simp only [real_inner_smul_left,hx,mul_zero]

theorem volume_hyperplane_zero (a : E4) (ha : a ≠ 0) (t : Real) :
    (volume : Measure E4) {x | inner Real x a=t} = 0 := by
  have ha2 : 0 < inner Real a a := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr ha)
  have hk : normalKernel a ≠ ⊤ := by
    intro he
    have hmem : a ∈ normalKernel a := by rw [he]; trivial
    change inner Real a a=0 at hmem
    linarith
  have hnull := volume.addHaar_submodule (normalKernel a) hk
  have hK : MeasurableSet (normalKernel a : Set E4) :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  let z : E4 := (t / inner Real a a) • a
  have hz : inner Real z a=t := by
    dsimp [z]
    rw [real_inner_smul_left]
    field_simp [ha2.ne']
  have hid : {x : E4 | inner Real x a=t} =
      (fun x : E4 => x-z) ⁻¹' (normalKernel a : Set E4) := by
    ext x
    change inner Real x a=t ↔ inner Real (x-z) a=0
    rw [inner_sub_left,hz,sub_eq_zero]
  rw [hid]
  calc
    volume ((fun x : E4 => x-z) ⁻¹' (normalKernel a : Set E4)) =
        Measure.map (fun x : E4 => x-z) volume (normalKernel a) := by
      rw [Measure.map_apply (by fun_prop) hK]
    _ = volume (normalKernel a) := by rw [map_sub_right_eq_self]
    _ = 0 := hnull

theorem ae_inner_ne (a : E4) (ha : a ≠ 0) (t : Real) :
    ∀ᵐ x ∂ballMeasure, inner Real x a ≠ t := by
  apply ae_restrict_of_ae
  rw [ae_iff]
  simpa using volume_hyperplane_zero a ha t

def reflectFun (a : E4) (x : E4) : E4 := x-(2*inner Real x a) • a

theorem reflectFun_inner_self (a x : E4) (ha : norm a=1) :
    inner Real (reflectFun a x) a = -inner Real x a := by
  have ha2 : inner Real a a=1 := by rw [real_inner_self_eq_norm_sq,ha]; norm_num
  simp only [reflectFun,inner_sub_left,real_inner_smul_left,ha2,mul_one]
  ring

theorem reflectFun_involution (a : E4) (ha : norm a=1) (x : E4) :
    reflectFun a (reflectFun a x)=x := by
  rw [reflectFun,reflectFun_inner_self a x ha]
  simp [reflectFun,neg_smul]

def reflection (a : E4) (ha : norm a=1) : E4 ≃ₗᵢ[Real] E4 where
  toFun := reflectFun a
  invFun := reflectFun a
  left_inv := reflectFun_involution a ha
  right_inv := reflectFun_involution a ha
  map_add' x y := by
    simp only [reflectFun,inner_add_left,mul_add,add_smul]
    abel
  map_smul' r x := by
    simp only [reflectFun,real_inner_smul_left,smul_sub,smul_smul,RingHom.id_apply]
    congr 1
    ring
  norm_map' x := by
    have ha2 : inner Real a a=1 := by rw [real_inner_self_eq_norm_sq,ha]; norm_num
    have hs : norm (reflectFun a x)^2=norm x^2 := by
      simp only [← real_inner_self_eq_norm_sq,reflectFun,inner_sub_left,inner_sub_right,
        real_inner_smul_left,real_inner_smul_right,real_inner_comm a x,ha2]
      ring
    calc norm (reflectFun a x) = Real.sqrt (norm (reflectFun a x)^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (norm x^2) := by rw [hs]
      _ = norm x := Real.sqrt_sq (norm_nonneg _)

@[simp] theorem reflection_apply (a : E4) (ha : norm a=1) (x : E4) :
    reflection a ha x=reflectFun a x := rfl

theorem integral_comp_ball_isometry (e : E4 ≃ₗᵢ[Real] E4) (f : E4 -> Real) :
    (∫ x, f (e x) ∂ballMeasure) = ∫ x, f x ∂ballMeasure := by
  let B : Set E4 := Metric.closedBall 0 1
  have hid (x : E4) : B.indicator (fun x => f (e x)) x = B.indicator f (e x) := by
    have hmem : e x ∈ B ↔ x ∈ B := by simp [B,Metric.mem_closedBall,dist_zero_right]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (hmem.mpr hx)]
    · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (mt hmem.mp hx)]
  calc
    (∫ x, f (e x) ∂ballMeasure) = ∫ x, B.indicator (fun x => f (e x)) x := by
      rw [integral_indicator measurableSet_closedBall]
      rfl
    _ = ∫ x, B.indicator f (e x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hid
    _ = ∫ x, B.indicator f x := e.measurePreserving.integral_comp
      e.toHomeomorph.measurableEmbedding (B.indicator f)
    _ = ∫ x, f x ∂ballMeasure := by
      rw [integral_indicator measurableSet_closedBall]
      rfl

theorem integrable_abs_bounded (f : E4 -> Real) (hf : Measurable f)
    (M : Real) (hb : forall x, |f x| ≤ M) : Integrable f ballMeasure := by
  apply (integrable_const M).mono'
  · exact hf.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

/-- A nonnegative integrand which is at least two on an explicit open set
has strictly positive integral over the ball. -/
theorem integral_pos_of_open (f : E4 -> Real) (hi : Integrable f ballMeasure)
    (h0 : forall x, 0 ≤ f x) (S : Set E4) (hS : IsOpen S) (hne : S.Nonempty)
    (hsub : S ⊆ Metric.closedBall (0 : E4) 1) (hfS : ∀ x ∈ S, 2 ≤ f x) :
    0 < ∫ x, f x ∂ballMeasure := by
  have hms : ballMeasure S = volume S := by
    rw [ballMeasure,Measure.restrict_apply hS.measurableSet,Set.inter_eq_left.mpr hsub]
  have hpos : 0 < ballMeasure S := by rw [hms]; exact hS.measure_pos volume hne
  have hreal : 0 < ballMeasure.real S := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hlow : 2*ballMeasure.real S ≤ ∫ x, f x ∂ballMeasure := by
    calc
      2*ballMeasure.real S = ∫ x, S.indicator (fun _ : E4 => (2 : Real)) x ∂ballMeasure := by
        rw [integral_indicator hS.measurableSet]
        simp [integral_const,smul_eq_mul,mul_comm,Measure.real,Measure.restrict_apply_univ]
      _ ≤ ∫ x, f x ∂ballMeasure := by
        apply integral_mono ((integrable_const (2 : Real)).indicator hS.measurableSet) hi
        intro x
        by_cases hx : x ∈ S
        · simpa [hx] using hfS x hx
        · simpa [hx] using h0 x
  linarith

def single (a : E4) (t : Real) (x : E4) : Real := closedSign (inner Real x a-t)
def pair (a b : E4) (x : E4) : Real := single a 0 x * single b 0 x

theorem measurable_single (a : E4) (t : Real) : Measurable (single a t) := by
  unfold single closedSign
  have hc : Continuous (fun x : E4 => inner ℝ x a - t) :=
    (continuous_id.inner continuous_const).sub continuous_const
  exact Measurable.ite (measurableSet_le measurable_const hc.measurable) measurable_const measurable_const

theorem integrable_single (a : E4) (t : Real) : Integrable (single a t) ballMeasure := by
  exact integrable_abs_bounded _ (measurable_single a t) 1 (by intro x; simp [single])

theorem integrable_pair (a b : E4) : Integrable (pair a b) ballMeasure := by
  exact integrable_abs_bounded _ ((measurable_single a 0).mul (measurable_single b 0)) 1
    (by intro x; simp [pair,single,abs_mul])

theorem single_integral_centered (a : E4) (ha : norm a=1) :
    (∫ x, single a 0 x ∂ballMeasure)=0 := by
  have hne : a ≠ 0 := by intro hz; simp [hz] at ha
  have hae : (fun x => single a 0 (reflection a ha x)) =ᵐ[ballMeasure]
      (fun x => -single a 0 x) := by
    filter_upwards [ae_inner_ne a hne 0] with x hx
    simpa [single,reflectFun_inner_self a x ha] using closedSign_neg (inner Real x a) hx
  have h := integral_comp_ball_isometry (reflection a ha) (single a 0)
  rw [integral_congr_ae hae,integral_neg] at h
  linarith

theorem closedSign_monotone : Monotone closedSign := by
  intro x y hxy
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · simp [closedSign,hx,hy]
  · linarith
  · norm_num [closedSign,hx,hy]
  · simp [closedSign,hx,hy]

theorem single_integral_neg_of_pos (a : E4) (ha : norm a=1) (t : Real) (ht : 0 < t) :
    (∫ x, single a t x ∂ballMeasure) < 0 := by
  let S : Set E4 := {x | norm x < 1 ∧ 0 < inner Real x a ∧ inner Real x a < t}
  have hS : IsOpen S := by
    have h1 : Continuous (fun x : E4 => norm x) := continuous_norm
    have h2 : Continuous (fun x : E4 => inner Real x a) := continuous_id.inner continuous_const
    exact (isOpen_lt h1 continuous_const).inter
      ((isOpen_lt continuous_const h2).inter (isOpen_lt h2 continuous_const))
  let r : Real := min (t/2) (1/2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrt : r < t := by have h := min_le_left (t/2) (1/2); dsimp [r]; linarith
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have ha2 : inner Real a a=1 := by rw [real_inner_self_eq_norm_sq,ha]; norm_num
  have hne : S.Nonempty := by
    refine ⟨r • a,?_⟩
    simp only [S,Set.mem_setOf_eq,norm_smul,Real.norm_eq_abs,abs_of_pos hr,ha,mul_one,
      real_inner_smul_left,ha2]
    exact ⟨hr1,hr,hrt⟩
  have hp : 0 < ∫ x, (single a 0 x-single a t x) ∂ballMeasure := by
    apply integral_pos_of_open _ ((integrable_single a 0).sub (integrable_single a t))
      (fun x => sub_nonneg.mpr (closedSign_monotone (by linarith))) S hS hne
    · intro x hx
      exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hx.1.le)
    · intro x hx
      have hp : 0 ≤ inner Real x a := hx.2.1.le
      have hn : ¬ 0 ≤ inner Real x a-t := by linarith [hx.2.2]
      norm_num [single,closedSign,hp,hn]
  rw [integral_sub (integrable_single a 0) (integrable_single a t),
    single_integral_centered a ha] at hp
  linarith

theorem single_integral_negate (a : E4) (ha : a ≠ 0) (t : Real) :
    (∫ x, single (-a) (-t) x ∂ballMeasure) = -(∫ x, single a t x ∂ballMeasure) := by
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_inner_ne a ha t] with x hx
  have hz : inner Real x a-t ≠ 0 := sub_ne_zero.mpr hx
  have hid : inner Real x (-a)-(-t) = -(inner Real x a-t) := by simp; ring
  simpa only [single,hid] using closedSign_neg (inner Real x a-t) hz

theorem single_zero_implies_offset_zero (a : E4) (ha : norm a=1) (t : Real)
    (hz : (∫ x, single a t x ∂ballMeasure)=0) : t=0 := by
  rcases lt_trichotomy t 0 with hn | he | hp
  · have hne : a ≠ 0 := by intro hh; simp [hh] at ha
    have h := single_integral_neg_of_pos (-a) (by simpa using ha) (-t) (by linarith)
    rw [single_integral_negate a hne t,hz,neg_zero] at h
    exact (lt_irrefl 0 h).elim
  · exact he
  · have h := single_integral_neg_of_pos a ha t hp
    rw [hz] at h
    exact (lt_irrefl 0 h).elim

theorem reflection_sign_difference_nonneg (p q alpha : Real) (ha : 0 ≤ alpha) :
    0 ≤ closedSign p*(closedSign q-closedSign (q-2*alpha*p)) := by
  by_cases hp : 0 ≤ p
  · have hnonneg := mul_nonneg ha hp
    have hq := closedSign_monotone (show q-2*alpha*p ≤ q by nlinarith only [hnonneg])
    have hv : closedSign p=1 := if_pos hp
    rw [hv,one_mul]
    exact sub_nonneg.mpr hq
  · have hnonpos := mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt (lt_of_not_ge hp))
    have hq := closedSign_monotone (show q ≤ q-2*alpha*p by nlinarith only [hnonpos])
    have hv : closedSign p=-1 := if_neg hp
    rw [hv,neg_one_mul]
    linarith only [hq]

/-- Strict positive correlation needs no evaluation of an arcsine integral. -/
theorem pair_integral_pos (a b : E4) (ha : norm a=1)
    (halpha : 0 < inner Real a b) : 0 < ∫ x, pair a b x ∂ballMeasure := by
  let alpha := inner Real a b
  let g : E4 -> Real := fun x => closedSign (inner Real x a) *
    closedSign (inner Real x b-2*alpha*inner Real x a)
  have hgi : Integrable g ballMeasure := by
    have hca : Continuous (fun x : E4 => inner Real x a) := continuous_id.inner continuous_const
    have hcb : Continuous (fun x : E4 => inner Real x b - 2*alpha*inner Real x a) :=
      (continuous_id.inner continuous_const).sub (continuous_const.mul hca)
    have hma : Measurable (fun x => closedSign (inner Real x a)) := by
      dsimp [closedSign]
      exact Measurable.ite (measurableSet_le measurable_const hca.measurable) measurable_const measurable_const
    have hmb : Measurable (fun x => closedSign (inner Real x b - 2*alpha*inner Real x a)) := by
      dsimp [closedSign]
      exact Measurable.ite (measurableSet_le measurable_const hcb.measurable) measurable_const measurable_const
    apply integrable_abs_bounded _ (hma.mul hmb) 1
    intro x
    simp [g,abs_mul]
  have hne : a ≠ 0 := by intro hz; simp [hz] at ha
  have href (x : E4) : inner Real (reflection a ha x) b =
      inner Real x b-2*alpha*inner Real x a := by
    simp only [reflection_apply,reflectFun,inner_sub_left,real_inner_smul_left,alpha]
    ring
  have heq : (fun x => pair a b (reflection a ha x)) =ᵐ[ballMeasure] (fun x => -g x) := by
    filter_upwards [ae_inner_ne a hne 0] with x hx
    simp only [pair,single,sub_zero,reflection_apply,reflectFun_inner_self a x ha]
    rw [show inner Real (reflectFun a x) b = inner Real x b-2*alpha*inner Real x a from href x,
      closedSign_neg _ hx]
    dsimp [g]
    ring
  have hrot := integral_comp_ball_isometry (reflection a ha) (pair a b)
  rw [integral_congr_ae heq,integral_neg] at hrot
  let S : Set E4 := {x | norm x < 1 ∧ 0 < inner Real x a ∧ 0 < inner Real x b ∧
    inner Real x b-2*alpha*inner Real x a < 0}
  have hS : IsOpen S := by
    have h1 : Continuous (fun x : E4 => norm x) := continuous_norm
    have h2 : Continuous (fun x : E4 => inner Real x a) := continuous_id.inner continuous_const
    have h3 : Continuous (fun x : E4 => inner Real x b) := continuous_id.inner continuous_const
    have h4 : Continuous (fun x : E4 => inner Real x b - 2*alpha*inner Real x a) := h3.sub (continuous_const.mul h2)
    exact (isOpen_lt h1 continuous_const).inter
      ((isOpen_lt continuous_const h2).inter
        ((isOpen_lt continuous_const h3).inter
          (isOpen_lt h4 continuous_const)))
  have ha2 : inner Real a a=1 := by rw [real_inner_self_eq_norm_sq,ha]; norm_num
  have hSne : S.Nonempty := by
    refine ⟨(1/2 : Real) • a,?_⟩
    have hn : norm ((1/2 : Real) • a) < 1 := by
      norm_num [norm_smul,ha]
    have hpa : inner Real ((1/2 : Real) • a) a = 1/2 := by
      rw [real_inner_smul_left,ha2,mul_one]
    have hpb : inner Real ((1/2 : Real) • a) b = alpha/2 := by
      rw [real_inner_smul_left]
      dsimp [alpha]
      ring
    change norm ((1/2 : Real) • a) < 1 ∧
      0 < inner Real ((1/2 : Real) • a) a ∧
      0 < inner Real ((1/2 : Real) • a) b ∧
      inner Real ((1/2 : Real) • a) b-2*alpha*inner Real ((1/2 : Real) • a) a < 0
    rw [hpa,hpb]
    have hp : 0 < alpha := halpha
    exact ⟨hn,by norm_num,by linarith,by nlinarith⟩
  have hpos : 0 < ∫ x, (pair a b x-g x) ∂ballMeasure := by
    apply integral_pos_of_open (fun x => pair a b x - g x) ((integrable_pair a b).sub hgi)
      (fun x => by
        have h := reflection_sign_difference_nonneg (inner Real x a) (inner Real x b) alpha halpha.le
        dsimp [pair, single, g]
        ring_nf at h ⊢
        exact h)
      S hS hSne
    · intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.1.le
    · intro x hx
      have hpa : 0 ≤ inner Real x a := hx.2.1.le
      have hpb : 0 ≤ inner Real x b := hx.2.2.1.le
      have hn : ¬ 0 ≤ inner Real x b-2*alpha*inner Real x a :=
        not_le_of_gt hx.2.2.2
      have h1 : 0 ≤ inner Real x a - 0 := by linarith
      have h2 : 0 ≤ inner Real x b - 0 := by linarith
      have h3 : 0 ≤ inner Real x a := hpa
      have h4 : ¬ 0 ≤ inner Real x b - 2 * alpha * inner Real x a := hn
      dsimp [pair, single, g, closedSign]
      rw [if_pos h1, if_pos h2, if_pos h3, if_neg h4]
      norm_num
  rw [integral_sub (integrable_pair a b) hgi] at hpos
  linarith

theorem pair_integral_negate_right (a b : E4) (hb : b ≠ 0) :
    (∫ x, pair a (-b) x ∂ballMeasure) = -(∫ x, pair a b x ∂ballMeasure) := by
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_inner_ne b hb 0] with x hx
  simp only [pair,single,sub_zero,inner_neg_right,closedSign_neg _ hx]
  ring

theorem pair_zero_implies_inner_zero (a b : E4) (ha : norm a=1) (hb : norm b=1)
    (hz : (∫ x, pair a b x ∂ballMeasure)=0) : inner Real a b=0 := by
  rcases lt_trichotomy (inner Real a b) 0 with hn | he | hp
  · have hbn : b ≠ 0 := by intro hh; simp [hh] at hb
    have h := pair_integral_pos a (-b) ha (by simpa using neg_pos.mpr hn)
    rw [pair_integral_negate_right a b hbn,hz,neg_zero] at h
    exact (lt_irrefl 0 h).elim
  · exact he
  · have h := pair_integral_pos a b ha hp
    rw [hz] at h
    exact (lt_irrefl 0 h).elim

theorem low_zero_rigidity (c : HyperplaneCfg) (hc : UnitCfg c)
    (hz : forall I : Walsh4.Index, I.Nonempty -> I.card ≤ 2 -> walsh ballMeasure c I=0) :
    (forall i, c.offset i=0) ∧ IsONFrame c.normal := by
  have hoff (i : Fin 4) : c.offset i=0 := by
    apply single_zero_implies_offset_zero (c.normal i) (hc i) (c.offset i)
    have h := hz {i} (by simp) (by simp)
    simpa [walsh,Cells.signCharacter_eq_prod,single,closedSign,sub_nonneg] using h
  refine ⟨hoff,?_⟩
  intro i j
  by_cases hij : i=j
  · subst j
    simp [real_inner_self_eq_norm_sq,hc i]
  · rw [if_neg hij]
    apply pair_zero_implies_inner_zero (c.normal i) (c.normal j) (hc i) (hc j)
    have h := hz {i,j} (by simp) (by simp [hij])
    simpa [walsh,Cells.signCharacter_eq_prod,hoff,pair,single,closedSign,hij] using h

end SoberonConvexBody.BallReflection
