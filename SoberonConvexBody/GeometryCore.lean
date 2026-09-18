import Mathlib
import SoberonConvexBody.Walsh4
import SoberonConvexBody.Cells
import SoberonConvexBody.Tensors
import SoberonConvexBody.FrameGeometry

/-!
# Geometric and measure-theoretic reduction

Unlike the earlier draft, this file does not package the analytic content in a
single certificate.  Every remaining analytic statement is exposed as a named
lemma with concrete definitions.
-/

noncomputable section

namespace SoberonConvexBody

open Set Real MeasureTheory
open scoped BigOperators

abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev E5 := EuclideanSpace ℝ (Fin 5)

abbrev HyperplaneCfg := Cells.HyperplaneCfg

/-- We use unit normals to remove the scaling ambiguity of affine hyperplanes. -/
def UnitCfg (c : HyperplaneCfg) : Prop := ∀ i, ‖c.normal i‖ = 1

/-- Walsh coefficient of a finite measure.  The pointwise character is the
finite Walsh character of the sixteen-cell sign pattern. -/
def walsh (μ : Measure E4) (c : HyperplaneCfg) (I : Walsh4.Index) : ℝ :=
  ∫ x, Cells.signCharacter c I x ∂μ

/-- The radial polynomial associated with the explicit tensor pair. -/
def angularPerturbation (tau : ℝ) (u : E4) : ℝ :=
  Tensors.A tau u u u + Tensors.B u u u u

/-- Direction of a nonzero vector.  The value at zero is immaterial. -/
def direction (x : E4) : E4 := (‖x‖)⁻¹ • x

/-- Exact radial perturbation used in the paper proof:
`rho(u)^4 = 1 + eps * f(u)`.
-/
def radialSet (tau eps : ℝ) : Set E4 :=
  {x | ‖x‖ ^ 4 ≤ 1 + eps * angularPerturbation tau (direction x)}

/-- Volume restricted to the radial set. -/
def radialMeasure (tau eps : ℝ) : Measure E4 :=
  volume.restrict (radialSet tau eps)

/-- At `eps = 0` the radial body is exactly the Euclidean unit ball. -/
theorem radialSet_zero (tau : ℝ) :
    radialSet tau 0 = Metric.closedBall (0 : E4) 1 := by
  ext x
  simp only [radialSet, Set.mem_setOf_eq, zero_mul, add_zero,
    Metric.mem_closedBall, dist_zero_right]
  exact pow_le_one_iff_of_nonneg (norm_nonneg x) (by norm_num : (4 : ℕ) ≠ 0)

@[simp] theorem radialMeasure_zero (tau : ℝ) :
    radialMeasure tau 0 = volume.restrict (Metric.closedBall (0 : E4) 1) := by
  simp [radialMeasure, radialSet_zero]

/-- The angular polynomial is continuous. -/
theorem continuous_angularPerturbation (tau : ℝ) :
    Continuous (angularPerturbation tau) := by
  unfold angularPerturbation Tensors.A Tensors.A0 Tensors.C Tensors.B Tensors.nForm Tensors.mForm
  fun_prop

/-- The angular perturbation is smooth as a polynomial on the ambient space. -/
theorem contDiff_angularPerturbation (tau : ℝ) :
    ContDiff ℝ ⊤ (angularPerturbation tau) := by
  unfold angularPerturbation Tensors.A Tensors.A0 Tensors.C Tensors.B Tensors.nForm Tensors.mForm
  fun_prop

/-- On the closed unit ball the angular polynomial has a global Lipschitz
constant.  This follows from the compact convex `C¹` mean-value theorem in
mathlib. -/
theorem angularPerturbation_lipschitzOn_unitBall (tau : ℝ) :
    ∃ L : NNReal,
      LipschitzOnWith L (angularPerturbation tau)
        (Metric.closedBall (0 : E4) 1) := by
  have hcd : ContDiffOn ℝ (1 : WithTop ℕ∞) (angularPerturbation tau)
      (Metric.closedBall (0 : E4) 1) :=
    (contDiff_angularPerturbation tau).contDiffOn.of_le le_top
  exact hcd.exists_lipschitzOnWith (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    (convex_closedBall (0 : E4) 1) (isCompact_closedBall (0 : E4) 1)

/-- A continuous angular polynomial is uniformly bounded on the unit sphere. -/
theorem angularPerturbation_bounded_on_sphere (tau : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M := by
  have hK : IsCompact (Metric.sphere (0 : E4) 1) := isCompact_sphere _ _
  have hcont : ContinuousOn (fun u : E4 => |angularPerturbation tau u|)
      (Metric.sphere (0 : E4) 1) :=
    (continuous_angularPerturbation tau).abs.continuousOn
  have hb : BddAbove ((fun u : E4 => |angularPerturbation tau u|) ''
      Metric.sphere (0 : E4) 1) := hK.bddAbove_image hcont
  rcases hb with ⟨a, ha⟩
  refine ⟨max 1 a, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  have hus : u ∈ Metric.sphere (0 : E4) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hu
  have himg : |angularPerturbation tau u| ∈
      (fun v : E4 => |angularPerturbation tau v|) '' Metric.sphere (0 : E4) 1 :=
    ⟨u, hus, rfl⟩
  exact (ha himg).trans (le_max_right _ _)

/-- Wulff body with support function `1 + eps * f / 4`.  The factor `1/4`
is chosen so that its radial function satisfies
`rho(u)^4 = 1 + eps * f(u) + O(eps^2)`. -/
def supportBody (tau eps : ℝ) : Set E4 :=
  {x | ∀ u : E4, ‖u‖ = 1 →
    inner ℝ x u ≤ 1 + (eps / 4) * angularPerturbation tau u}

/-- Lebesgue measure restricted to the Wulff body. -/
def supportMeasure (tau eps : ℝ) : Measure E4 :=
  volume.restrict (supportBody tau eps)

/-- The radial model whose radius in direction `u` is
`1 + eps * f(u) / 4`. -/
def linearRadialSet (tau eps : ℝ) : Set E4 :=
  {x | ‖x‖ ≤ 1 + (eps / 4) * angularPerturbation tau (direction x)}

/-- A uniformly shrunken version of the linear radial model. -/
def shrunkenLinearRadialSet (tau eps D : ℝ) : Set E4 :=
  {x | ‖x‖ ≤
    1 + (eps / 4) * angularPerturbation tau (direction x) - D * eps^2}

/-- Multiplying the direction by the norm recovers a nonzero vector. -/
theorem norm_smul_direction {x : E4} (hx : x ≠ 0) :
    ‖x‖ • direction x = x := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp [direction, smul_smul, hnorm]

/-- Convexity of the Wulff construction is immediate from halfspaces. -/
theorem supportBody_convex (tau eps : ℝ) : Convex ℝ (supportBody tau eps) := by
  intro x hx y hy a b ha hb hab u hu
  have hx' := hx u hu
  have hy' := hy u hu
  simp only [inner_add_left, real_inner_smul_left]
  have hxa := mul_le_mul_of_nonneg_left hx' ha
  have hyb := mul_le_mul_of_nonneg_left hy' hb
  calc
    a * inner ℝ x u + b * inner ℝ y u ≤
        a * (1 + eps / 4 * angularPerturbation tau u) + b * (1 + eps / 4 * angularPerturbation tau u) :=
      add_le_add hxa hyb
    _ = (a + b) * (1 + eps / 4 * angularPerturbation tau u) := by ring
    _ = 1 + eps / 4 * angularPerturbation tau u := by rw [hab, one_mul]

/-- The Wulff body is closed, being an intersection of closed halfspaces. -/
theorem supportBody_isClosed (tau eps : ℝ) : IsClosed (supportBody tau eps) := by
  have hrepr :
      supportBody tau eps =
        ⋂ u : E4, ⋂ (_h : ‖u‖ = 1),
          {x : E4 | inner ℝ x u ≤
            1 + (eps / 4) * angularPerturbation tau u} := by
    ext x
    simp [supportBody]
  rw [hrepr]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro hu
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- Unit direction of a nonzero vector. -/
theorem norm_direction {x : E4} (hx : x ≠ 0) : ‖direction x‖ = 1 := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp [direction, norm_smul, Real.norm_eq_abs, abs_inv, hnorm]

/-- The radial direction pairs with the vector to its norm. -/
theorem inner_direction {x : E4} (hx : x ≠ 0) :
    inner ℝ x (direction x) = ‖x‖ := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [direction, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp [hnorm]


/-- Every point of the Wulff body lies below the support radius in its own
radial direction. -/
theorem supportBody_subset_linearRadialSet (tau eps : ℝ) :
    supportBody tau eps ⊆ linearRadialSet tau eps := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp [linearRadialSet, direction, angularPerturbation,
      Tensors.A, Tensors.A0, Tensors.C, Tensors.B,
      Tensors.nForm, Tensors.mForm]
  · have hu : ‖direction x‖ = 1 := norm_direction hx0
    have hs := hx (direction x) hu
    rw [inner_direction hx0] at hs
    exact hs

/-- Uniform control of the support perturbation from a uniform bound on `f`. -/
theorem support_perturbation_abs_le
    {tau eps M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M)
    {u : E4} (hu : ‖u‖ = 1) :
    |(eps / 4) * angularPerturbation tau u| ≤ |eps| * M / 4 := by
  rw [abs_mul, abs_div, show |(4 : ℝ)| = 4 by norm_num]
  have h := hbound u hu
  nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg eps)]

/-- The Wulff body lies between two concentric balls. -/
theorem supportBody_ball_sandwich
    {tau eps M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u : E4, ‖u‖ = 1 → |angularPerturbation tau u| ≤ M) :
    Metric.closedBall (0 : E4) (1 - |eps| * M / 4) ⊆ supportBody tau eps ∧
    supportBody tau eps ⊆ Metric.closedBall (0 : E4) (1 + |eps| * M / 4) := by
  constructor
  · intro x hx
    have hnx : ‖x‖ ≤ 1 - |eps| * M / 4 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    intro u hu
    have hinner : inner ℝ x u ≤ ‖x‖ := by
      have h := real_inner_le_norm x u
      simpa [hu] using h
    have habs := support_perturbation_abs_le hM hbound (eps := eps) hu
    have hlower : -(|eps| * M / 4) ≤
        (eps / 4) * angularPerturbation tau u := (neg_le_of_abs_le habs)
    linarith
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp only [Metric.mem_closedBall, dist_self]
      positivity
    · let u : E4 := direction x
      have hu : ‖u‖ = 1 := norm_direction hx0
      have hsupport := hx u hu
      have habs := support_perturbation_abs_le hM hbound (eps := eps) hu
      have hupper : (eps / 4) * angularPerturbation tau u ≤
          |eps| * M / 4 := le_of_abs_le habs
      have hinner : inner ℝ x u = ‖x‖ := inner_direction hx0
      rw [hinner] at hsupport
      have hnorm : ‖x‖ ≤ 1 + |eps| * M / 4 := by linarith
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm

/-- For small `eps`, the Wulff body is an honest convex body with nonempty
interior.  No differential geometry is used here. -/
theorem supportBody_is_convexBody (tau : ℝ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ eps, |eps| < eps0 →
        ∃ K : ConvexBody E4,
          (K : Set E4) = supportBody tau eps ∧
          (interior (K : Set E4)).Nonempty := by
  rcases angularPerturbation_bounded_on_sphere tau with ⟨M, hM, hbound⟩
  let eps0 : ℝ := 2 / M
  have heps0 : 0 < eps0 := by
    dsimp [eps0]
    positivity
  refine ⟨eps0, heps0, ?_⟩
  intro eps heps
  have hr : 0 < 1 - |eps| * M / 4 := by
    have hmul : |eps| * M < 2 := by
      have := mul_lt_mul_of_pos_right heps hM
      dsimp [eps0] at this
      field_simp [ne_of_gt hM] at this
      linarith
    linarith
  have hsand := supportBody_ball_sandwich (tau := tau) (eps := eps)
    (M := M) (le_of_lt hM) hbound
  have hclosed : IsClosed (supportBody tau eps) := supportBody_isClosed tau eps
  have hbounded : Bornology.IsBounded (supportBody tau eps) := by
    exact Metric.isBounded_closedBall.subset hsand.2
  have hcompact : IsCompact (supportBody tau eps) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩
  have hzero : (0 : E4) ∈ supportBody tau eps := by
    apply hsand.1
    simp [Metric.mem_closedBall, le_of_lt hr]
  let K : ConvexBody E4 :=
    { carrier := supportBody tau eps
      convex' := supportBody_convex tau eps
      isCompact' := hcompact
      nonempty' := ⟨0, hzero⟩ }
  have hinterior : (interior (K : Set E4)).Nonempty := by
    have hball : Metric.ball (0 : E4) (1 - |eps| * M / 4) ⊆
        supportBody tau eps := by
      intro x hx
      apply hsand.1
      exact Metric.ball_subset_closedBall hx
    have hopen : IsOpen (Metric.ball (0 : E4) (1 - |eps| * M / 4)) :=
      Metric.isOpen_ball
    have hinto : Metric.ball (0 : E4) (1 - |eps| * M / 4) ⊆
        interior (supportBody tau eps) := interior_maximal hball hopen
    refine ⟨0, ?_⟩
    change (0 : E4) ∈ interior (supportBody tau eps)
    apply hinto
    simpa [Metric.mem_ball] using hr
  refine ⟨K, ?_, ?_⟩
  · rfl
  · exact hinterior

/-- For sufficiently small parameter, the fourth power of the radial function
is uniformly positive. -/
theorem radial_rhs_positive_small (tau : ℝ) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ eps, |eps| < eps0 →
        ∀ u : E4, ‖u‖ = 1 → 0 < 1 + eps * angularPerturbation tau u := by
  rcases angularPerturbation_bounded_on_sphere tau with ⟨M, hM, hbound⟩
  refine ⟨M⁻¹, inv_pos.mpr hM, ?_⟩
  intro eps heps u hu
  have hf := hbound u hu
  have hprod : |eps * angularPerturbation tau u| < 1 := by
    calc
      |eps * angularPerturbation tau u|
          = |eps| * |angularPerturbation tau u| := abs_mul _ _
      _ ≤ |eps| * M := mul_le_mul_of_nonneg_left hf (abs_nonneg eps)
      _ < M⁻¹ * M := mul_lt_mul_of_pos_right heps hM
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hM)
  have hlower : -1 < eps * angularPerturbation tau u := (abs_lt.mp hprod).1
  linarith

/-- High Walsh vector, in the order matching the tensor obstruction. -/
def highWalsh (μ : Measure E4) (c : HyperplaneCfg) : E5 :=
  WithLp.toLp 2 ![walsh μ c {1,2,3},
    walsh μ c {0,2,3},
    walsh μ c {0,1,3},
    walsh μ c {0,1,2},
    walsh μ c {0,1,2,3}]

/-- The scale factors are concrete integrals against mathlib's sphere measure.
Their positivity is proved; no numerical sphere-moment evaluation is assumed. -/
def highScale : Fin 5 -> Real :=
  ![(3 / 2 : Real) * SphereGeometry.coordinateMoment {1,2,3},
    (3 / 2 : Real) * SphereGeometry.coordinateMoment {0,2,3},
    (3 / 2 : Real) * SphereGeometry.coordinateMoment {0,1,3},
    (3 / 2 : Real) * SphereGeometry.coordinateMoment {0,1,2},
    6 * SphereGeometry.coordinateMoment {0,1,2,3}]

theorem highScale_pos (i : Fin 5) : 0 < highScale i := by
  fin_cases i
  · change 0 < (3 / 2 : Real) * SphereGeometry.coordinateMoment {1,2,3}
    exact mul_pos (by norm_num) (SphereGeometry.coordinateMoment_pos _)
  · change 0 < (3 / 2 : Real) * SphereGeometry.coordinateMoment {0,2,3}
    exact mul_pos (by norm_num) (SphereGeometry.coordinateMoment_pos _)
  · change 0 < (3 / 2 : Real) * SphereGeometry.coordinateMoment {0,1,3}
    exact mul_pos (by norm_num) (SphereGeometry.coordinateMoment_pos _)
  · change 0 < (3 / 2 : Real) * SphereGeometry.coordinateMoment {0,1,2}
    exact mul_pos (by norm_num) (SphereGeometry.coordinateMoment_pos _)
  · change 0 < (6 : Real) * SphereGeometry.coordinateMoment {0,1,2,3}
    exact mul_pos (by norm_num) (SphereGeometry.coordinateMoment_pos _)

/-- The exact first-order obstruction, with its sphere-measure normalization. -/
def scaledObstruction (tau : Real) (q : Fin 4 -> E4) : E5 :=
  WithLp.toLp 2 (fun i => highScale i * Tensors.obstruction tau q i)

/-- Scaling by the five proved-positive moments does not introduce zeros. -/
theorem scaledObstruction_ne_zero
    {tau : Real} {q : Fin 4 -> E4}
    (h : Tensors.obstruction tau q ≠ 0) :
    scaledObstruction tau q ≠ 0 := by
  intro hz
  apply h
  ext i
  have hi := congrArg (fun v : E5 => v i) hz
  have hp : highScale i * Tensors.obstruction tau q i = 0 := by
    simpa [scaledObstruction, PiLp.toLp_apply] using hi
  exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt (highScale_pos i))

/-- The norm of a point of the unit sphere, after coercion to the ambient
space, is one. -/
theorem norm_coe_unitSphere
    (u : Metric.sphere (0 : E4) 1) : ‖(u : E4)‖ = 1 := by
  exact SphereGeometry.norm_coe u

/-- Positive radial scaling does not change the unit direction. -/
theorem direction_pos_smul_unitSphere
    (u : Metric.sphere (0 : E4) 1) (r : Set.Ioi (0 : ℝ)) :
    direction ((r : ℝ) • (u : E4)) = (u : E4) := by
  have hr : (0 : ℝ) < r := r.property
  have hu : ‖(u : E4)‖ = 1 := norm_coe_unitSphere u
  simp [direction, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu,
    smul_smul, hr.ne']

/-- The norm of a positive radial scaling of a unit vector is the radius. -/
theorem norm_pos_smul_unitSphere
    (u : Metric.sphere (0 : E4) 1) (r : Set.Ioi (0 : ℝ)) :
    ‖(r : ℝ) • (u : E4)‖ = (r : ℝ) := by
  have hr : (0 : ℝ) < r := r.property
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_coe_unitSphere]

/-- A fourth root convenient for the radial measure computation. -/
private noncomputable def fourthRoot (a : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt a)

private theorem fourthRoot_pos {a : ℝ} (ha : 0 < a) : 0 < fourthRoot a := by
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 ha)

private theorem fourthRoot_pow_four {a : ℝ} (ha : 0 ≤ a) :
    fourthRoot a ^ 4 = a := by
  calc
    fourthRoot a ^ 4 = (Real.sqrt (Real.sqrt a) ^ 2) ^ 2 := by
      simp only [fourthRoot]
      ring
    _ = (Real.sqrt a) ^ 2 := by
      rw [Real.sq_sqrt (Real.sqrt_nonneg a)]
    _ = a := Real.sq_sqrt ha

/-- In dimension four, the radial Haar factor assigns mass `a / 4` to the
positive radii whose fourth power is at most `a`. -/
theorem volumeIoiPow_three_radialSlice
    (a : ℝ) (ha : 0 ≤ a) :
    Measure.volumeIoiPow 3
        {r : Set.Ioi (0 : ℝ) | (r : ℝ) ^ 4 ≤ a} =
      ENNReal.ofReal (a / 4) := by
  by_cases ha0 : a = 0
  · subst a
    have hempty :
        {r : Set.Ioi (0 : ℝ) | (r : ℝ) ^ 4 ≤ (0 : ℝ)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro r hr
      have hle : (r : ℝ) ^ 4 ≤ 0 := hr
      exact (not_le_of_gt (pow_pos r.property 4)) hle
    simp [hempty]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let rho : ℝ := fourthRoot a
    have hrho : 0 < rho := fourthRoot_pos ha'
    let r0 : Set.Ioi (0 : ℝ) := ⟨rho, hrho⟩
    have hrho4 : rho ^ 4 = a := fourthRoot_pow_four ha
    have hslice :
        {r : Set.Ioi (0 : ℝ) | (r : ℝ) ^ 4 ≤ a} = Set.Iic r0 := by
      ext r
      change (r : ℝ) ^ 4 ≤ a ↔ r ≤ r0
      rw [← Subtype.coe_le_coe]
      have hr0 : 0 ≤ (r : ℝ) := le_of_lt r.property
      have hrho0 : 0 ≤ rho := le_of_lt hrho
      have hp :=
        pow_le_pow_iff_left₀ hr0 hrho0 (by norm_num : (4 : ℕ) ≠ 0)
      simpa [r0, hrho4] using hp
    rw [hslice]
    have hdisj : Disjoint (Set.Iio r0) ({r0} : Set (Set.Ioi (0 : ℝ))) := by
      refine Set.disjoint_left.2 ?_
      intro x hx hxr
      have hxlt : x < r0 := hx
      have hxeq : x = r0 := Set.mem_singleton_iff.mp hxr
      exact (ne_of_lt hxlt) hxeq
    have hsingle :
        Measure.volumeIoiPow 3 ({r0} : Set (Set.Ioi (0 : ℝ))) = 0 := by
      rw [Measure.volumeIoiPow,
        withDensity_apply _ (measurableSet_singleton r0)]
      have hbase :
          (Measure.comap Subtype.val volume)
              ({r0} : Set (Set.Ioi (0 : ℝ))) = 0 := by
        rw [comap_subtype_coe_apply measurableSet_Ioi]
        simp
      exact setLIntegral_measure_zero _ _ hbase
    calc
      Measure.volumeIoiPow 3 (Set.Iic r0)
          = Measure.volumeIoiPow 3 (Set.Iio r0 ∪ {r0}) := by
              rw [Set.Iio_union_right]
      _ = Measure.volumeIoiPow 3 (Set.Iio r0) +
            Measure.volumeIoiPow 3 ({r0} : Set (Set.Ioi (0 : ℝ))) := by
              exact measure_union hdisj (measurableSet_singleton r0)
      _ = Measure.volumeIoiPow 3 (Set.Iio r0) := by rw [hsingle, add_zero]
      _ = ENNReal.ofReal ((r0 : ℝ) ^ 4 / 4) := by
            have hpow := Measure.volumeIoiPow_apply_Iio 3 r0
            norm_num at hpow
            exact hpow
      _ = ENNReal.ofReal (a / 4) := by
            simp only [r0]
            rw [hrho4]

/-- Projecting a four-dimensional radial region in polar coordinates onto its
angular variable produces the expected density `a(u) / 4` on the sphere. -/
theorem map_fst_restrict_radialProduct
    (a : Metric.sphere (0 : E4) 1 → ℝ)
    (ha : Measurable a) (hpos : ∀ u, 0 ≤ a u) :
    Measure.map Prod.fst
        ((volume.toSphere.prod (Measure.volumeIoiPow 3)).restrict
          {p : Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ) |
            (p.2 : ℝ) ^ 4 ≤ a p.1}) =
      volume.toSphere.withDensity
        (fun u => (Real.toNNReal (a u / 4) : ENNReal)) := by
  let S : Set (Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) ^ 4 ≤ a p.1}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  apply Measure.ext
  intro T hT
  rw [Measure.map_apply measurable_fst hT]
  rw [Measure.restrict_apply (measurable_fst hT)]
  rw [Measure.prod_apply ((measurable_fst hT).inter hS)]
  rw [withDensity_apply _ hT]
  rw [← lintegral_indicator hT]
  apply lintegral_congr
  intro u
  by_cases hu : u ∈ T
  · have hpre :
        Prod.mk u ⁻¹' (Prod.fst ⁻¹' T ∩ S) =
          {r : Set.Ioi (0 : ℝ) | (r : ℝ) ^ 4 ≤ a u} := by
      ext r
      simp [S, hu]
    rw [hpre, volumeIoiPow_three_radialSlice (a u) (hpos u)]
    simp [hu, ENNReal.ofReal]
  · have hpre : Prod.mk u ⁻¹' (Prod.fst ⁻¹' T ∩ S) = ∅ := by
      ext r
      simp [S, hu]
    rw [hpre]
    simp [hu]

/-- The generalized polar-coordinate theorem from mathlib is the foundation
for the exact radial integral identity.  This lemma specializes it to dimension
four and to star-shaped radial sets.
-/
theorem radial_integral_formula
    (tau eps : ℝ) (g : E4 → ℝ)
    (hg : Measurable g)
    (hangular : ∀ r : ℝ, 0 < r → ∀ u : E4, ‖u‖ = 1 → g (r • u) = g u)
    (hpos : ∀ u : E4, ‖u‖ = 1 → 0 ≤ 1 + eps * angularPerturbation tau u) :
    ∫ x in radialSet tau eps, g x =
      (1/4 : ℝ) * ∫ u : Metric.sphere (0 : E4) 1,
        g u * (1 + eps * angularPerturbation tau u) ∂(volume.toSphere) := by
  let a : Metric.sphere (0 : E4) 1 → ℝ :=
    fun u => 1 + eps * angularPerturbation tau (u : E4)
  let S : Set (Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) ^ 4 ≤ a p.1}
  let P : Measure (Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ)) :=
    volume.toSphere.prod (Measure.volumeIoiPow 3)
  have ha : Measurable a :=
    (continuous_const.add (continuous_const.mul
      ((continuous_angularPerturbation tau).comp continuous_subtype_val))).measurable
  have ha_nonneg : ∀ u, 0 ≤ a u := by
    intro u
    exact hpos (u : E4) (norm_coe_unitSphere u)
  have hpow : Measurable fun p : Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ) => (p.2 : ℝ) ^ 4 := by
    fun_prop
  have hS : MeasurableSet S := measurableSet_le hpow (ha.comp measurable_fst)
  have hdir : Measurable direction := by
    unfold direction
    fun_prop
  have hradial : MeasurableSet (radialSet tau eps) := by
    apply measurableSet_le
    · fun_prop
    · exact measurable_const.add
        (measurable_const.mul
          ((continuous_angularPerturbation tau).measurable.comp hdir))
  have hdim : Module.finrank ℝ E4 = 4 := by
    simp [E4]
  have hmem : ∀ p : Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ),
      (↑((homeomorphUnitSphereProd E4).symm p) : E4) ∈ radialSet tau eps ↔ p ∈ S := by
    intro p
    rcases p with ⟨u, r⟩
    simp only [homeomorphUnitSphereProd_symm_apply_coe]
    change ‖(r : ℝ) • (u : E4)‖ ^ 4 ≤
        1 + eps * angularPerturbation tau (direction ((r : ℝ) • (u : E4))) ↔
      (r : ℝ) ^ 4 ≤ a u
    rw [norm_pos_smul_unitSphere, direction_pos_smul_unitSphere]
  have hpush :
      Measure.map Prod.fst (P.restrict S) =
        volume.toSphere.withDensity
          (fun u => (Real.toNNReal (a u / 4) : ENNReal)) := by
    simpa [P, S] using map_fst_restrict_radialProduct a ha ha_nonneg
  calc
    ∫ x in radialSet tau eps, g x
        = ∫ x : ({0}ᶜ : Set E4),
            (radialSet tau eps).indicator g (x : E4)
              ∂(volume.comap (Subtype.val : ({0}ᶜ : Set E4) → E4)) := by
            rw [← integral_indicator hradial,
              integral_subtype_comap (measurableSet_singleton _).compl
                (fun x => (radialSet tau eps).indicator g x),
              restrict_compl_singleton]
    _ = ∫ p : Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ),
          (radialSet tau eps).indicator g
            (↑((homeomorphUnitSphereProd E4).symm p) : E4) ∂P := by
          have hpolar :=
            volume.measurePreserving_homeomorphUnitSphereProd.integral_comp
              (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd E4))
              (fun p : Metric.sphere (0 : E4) 1 × Set.Ioi (0 : ℝ) =>
                (radialSet tau eps).indicator g
                  (↑((homeomorphUnitSphereProd E4).symm p) : E4))
          simpa [P, hdim] using hpolar
    _ = ∫ p in S, g (p.1 : E4) ∂P := by
          rw [← integral_indicator hS]
          apply integral_congr_ae
          filter_upwards with p
          by_cases hp : p ∈ S
          · rw [Set.indicator_of_mem ((hmem p).2 hp)]
            rw [Set.indicator_of_mem hp]
            simpa only [homeomorphUnitSphereProd_symm_apply_coe] using
              hangular (p.2 : ℝ) p.2.property (p.1 : E4)
                (norm_coe_unitSphere p.1)
          · rw [Set.indicator_of_notMem (mt (hmem p).1 hp)]
            rw [Set.indicator_of_notMem hp]
    _ = ∫ u : Metric.sphere (0 : E4) 1,
          g (u : E4) ∂Measure.map Prod.fst (P.restrict S) := by
          exact (integral_map (μ := P.restrict S) measurable_fst.aemeasurable
            (hg.comp measurable_subtype_coe).aestronglyMeasurable).symm
    _ = ∫ u : Metric.sphere (0 : E4) 1,
          g (u : E4) ∂volume.toSphere.withDensity
            (fun u => (Real.toNNReal (a u / 4) : ENNReal)) := by
          rw [hpush]
    _ = ∫ u : Metric.sphere (0 : E4) 1,
          Real.toNNReal (a u / 4) • g (u : E4) ∂volume.toSphere := by
          rw [integral_withDensity_eq_integral_smul]
          measurability
    _ = ∫ u : Metric.sphere (0 : E4) 1,
          (1 / 4 : ℝ) * (g (u : E4) * a u) ∂volume.toSphere := by
          apply integral_congr_ae
          filter_upwards with u
          have hau : 0 ≤ a u := ha_nonneg u
          rw [NNReal.smul_def, Real.coe_toNNReal _ (div_nonneg hau (by norm_num))]
          ring
    _ = (1 / 4 : ℝ) * ∫ u : Metric.sphere (0 : E4) 1,
          g (u : E4) * a u ∂volume.toSphere := by
          rw [integral_const_mul]
    _ = (1 / 4 : ℝ) * ∫ u : Metric.sphere (0 : E4) 1,
          g u * (1 + eps * angularPerturbation tau u) ∂volume.toSphere := by
          simp [a]

/-- Polar integration and the zero constant term for any nonempty centered
character. All integrability claims concern the actual sphere measure. -/
private theorem centered_radial_walsh
    (tau eps : Real) (q : Fin 4 -> E4) (hq : Tensors.IsONFrame q)
    (I : Walsh4.Index) (hI : I.Nonempty)
    (hpos : forall u : E4, norm u = 1 ->
      0 <= 1 + eps * angularPerturbation tau u) :
    walsh (radialMeasure tau eps) ⟨ q, fun _ => 0 ⟩ I =
      (eps / 4) * ∫ u : SphereGeometry.UnitSphere,
        Cells.signCharacter ⟨ q, fun _ => 0 ⟩ I (u : E4) *
          Tensors.tensorPolynomial tau (u : E4) ∂ SphereGeometry.sphereVolume := by
  let c : HyperplaneCfg := ⟨ q, fun _ => 0 ⟩
  let g : SphereGeometry.UnitSphere -> Real :=
    fun u => Cells.signCharacter c I (u : E4)
  let f : SphereGeometry.UnitSphere -> Real :=
    fun u => Tensors.tensorPolynomial tau (u : E4)
  have hg : Measurable (Cells.signCharacter c I) := Cells.measurable_signCharacter c I
  have hang : forall r : Real, 0 < r -> forall u : E4, norm u = 1 ->
      Cells.signCharacter c I (r • u) = Cells.signCharacter c I u := by
    intro r hr u _
    exact Cells.centered_signCharacter_pos_smul q I r hr u
  have hpolar : walsh (radialMeasure tau eps) c I =
      (1 / 4 : Real) * ∫ u : SphereGeometry.UnitSphere,
        g u * (1 + eps * f u) ∂ SphereGeometry.sphereVolume := by
    simpa only [walsh, radialMeasure, g, f, SphereGeometry.sphereVolume,
      Tensors.tensorPolynomial, angularPerturbation] using
        radial_integral_formula tau eps (Cells.signCharacter c I) hg hang hpos
  have hIg : Integrable g SphereGeometry.sphereVolume := by
    simpa only [mul_one] using
      SphereGeometry.integrable_sign_mul_continuous g (fun _ => (1 : Real))
        (hg.comp measurable_subtype_coe)
        (fun u => Walsh4.abs_char I (Cells.pattern c (u : E4))) continuous_const
  have hIgp : Integrable (fun u => g u * f u) SphereGeometry.sphereVolume :=
    SphereGeometry.integrable_centered_character_mul_polynomial tau q I
  have hzero : (∫ u, g u ∂ SphereGeometry.sphereVolume) = 0 :=
    SphereGeometry.integral_centered_character q hq I hI
  have hsplit :
      (∫ u, g u * (1 + eps * f u) ∂ SphereGeometry.sphereVolume) =
        (∫ u, g u ∂ SphereGeometry.sphereVolume) +
          eps * (∫ u, g u * f u ∂ SphereGeometry.sphereVolume) := by
    calc
      (∫ u, g u * (1 + eps * f u) ∂ SphereGeometry.sphereVolume) =
          ∫ u, g u + eps * (g u * f u) ∂ SphereGeometry.sphereVolume := by
        apply integral_congr_ae
        filter_upwards with u
        ring
      _ = (∫ u, g u ∂ SphereGeometry.sphereVolume) +
          eps * (∫ u, g u * f u ∂ SphereGeometry.sphereVolume) := by
        rw [integral_add hIg (hIgp.const_mul eps), integral_const_mul]
  rw [hpolar, hsplit, hzero]
  change (1 / 4 : Real) * (0 + eps * (∫ u, g u * f u
    ∂ SphereGeometry.sphereVolume)) =
      (eps / 4) * (∫ u, g u * f u ∂ SphereGeometry.sphereVolume)
  ring

/-- Exact computation at a centered orthonormal frame, using the five
positive coordinate moments rather than assumed numerical sphere constants. -/
theorem highWalsh_centered_onFrame
    (tau eps : Real) (q : Fin 4 -> E4)
    (hq : Tensors.IsONFrame q)
    (hpos : forall u : E4, norm u = 1 ->
      0 <= 1 + eps * angularPerturbation tau u) :
    highWalsh (radialMeasure tau eps)
      ⟨ q, fun _ => 0 ⟩ = eps • scaledObstruction tau q := by
  have h123 := centered_radial_walsh tau eps q hq {1,2,3} (by decide) hpos
  rw [SphereGeometry.integral_centered_polynomial_high123 tau q hq] at h123
  have h023 := centered_radial_walsh tau eps q hq {0,2,3} (by decide) hpos
  rw [SphereGeometry.integral_centered_polynomial_high023 tau q hq] at h023
  have h013 := centered_radial_walsh tau eps q hq {0,1,3} (by decide) hpos
  rw [SphereGeometry.integral_centered_polynomial_high013 tau q hq] at h013
  have h012 := centered_radial_walsh tau eps q hq {0,1,2} (by decide) hpos
  rw [SphereGeometry.integral_centered_polynomial_high012 tau q hq] at h012
  have h0123 := centered_radial_walsh tau eps q hq {0,1,2,3} (by decide) hpos
  rw [SphereGeometry.integral_centered_polynomial_high0123 tau q hq] at h0123
  ext i
  fin_cases i <;>
    simp [highWalsh, scaledObstruction, highScale, Tensors.obstruction,
      PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul,
      h123, h023, h013, h012, h0123] <;> ring


end SoberonConvexBody
