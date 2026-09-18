import SoberonConvexBody.GeometryCore
import SoberonConvexBody.SphereBounds

/-!
# Radial bands intersected with thin angular strips

This module proves the product estimate for a radial shell and a union of
four strips. Both factors are computed using actual measures.
-/

noncomputable section
namespace SoberonConvexBody
open Set Real MeasureTheory
open scoped BigOperators

namespace ShellBounds
open SphereGeometry

abbrev Radius := Set.Ioi (0 : Real)
abbrev PolarSpace := UnitSphere × Radius

def polarVolume : Measure PolarSpace := sphereVolume.prod (Measure.volumeIoiPow 3)

def ambientPolar (p : PolarSpace) : E4 := (p.2 : Real) • (p.1 : E4)

 theorem measurable_ambientPolar : Measurable ambientPolar := by
  unfold ambientPolar
  fun_prop

/-- Polar coordinates apply to the measure of every measurable ambient set.
The only omitted point is the null singleton at the origin. -/
 theorem volume_eq_polar_preimage (A : Set E4) (hA : MeasurableSet A) :
    volume A = polarVolume (ambientPolar ⁻¹' A) := by
  let e := homeomorphUnitSphereProd E4
  have hdim : Module.finrank Real E4 = 4 := by simp [E4]
  have hmap : Measure.map e (volume.comap (Subtype.val : ({0}ᶜ : Set E4) -> E4)) =
      polarVolume := by
    simpa [e, polarVolume, sphereVolume, hdim] using
      (volume : Measure E4).measurePreserving_homeomorphUnitSphereProd.map_eq
  have hpre : e ⁻¹' (ambientPolar ⁻¹' A) =
      (Subtype.val : ({0}ᶜ : Set E4) -> E4) ⁻¹' A := by
    ext x
    have he : ambientPolar (e x) = (x : E4) := by
      have hh := congrArg (fun y : ({0}ᶜ : Set E4) => (y : E4))
        (e.symm_apply_apply x)
      simpa only [e, homeomorphUnitSphereProd_symm_apply_coe, ambientPolar] using hh
    simp only [Set.mem_preimage, he]
  have himage : (Subtype.val : ({0}ᶜ : Set E4) -> E4) ''
      ((Subtype.val : ({0}ᶜ : Set E4) -> E4) ⁻¹' A) = A ∩ {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · rintro ⟨hxA, hx0⟩
      exact ⟨⟨x, hx0⟩, hxA, rfl⟩
  symm
  calc
    polarVolume (ambientPolar ⁻¹' A)
        = (volume.comap (Subtype.val : ({0}ᶜ : Set E4) -> E4))
            (e ⁻¹' (ambientPolar ⁻¹' A)) := by
      rw [← hmap, Measure.map_apply e.continuous.measurable
        (measurable_ambientPolar hA)]
    _ = (volume.comap (Subtype.val : ({0}ᶜ : Set E4) -> E4))
          ((Subtype.val : ({0}ᶜ : Set E4) -> E4) ⁻¹' A) := by rw [hpre]
    _ = volume (A ∩ {0}ᶜ) := by
      rw [comap_subtype_coe_apply (measurableSet_singleton (0 : E4)).compl,
        himage]
    _ = volume A := by
      rw [← Measure.restrict_apply hA, restrict_compl_singleton]

/-- The radial interval is open at its inner endpoint and closed at its outer
endpoint, so differences of nested radial cuts are literal set differences. -/
def radialBand (a b : Real) : Set Radius :=
  {r | a < (r : Real)^4 ∧ (r : Real)^4 ≤ b}

 theorem measurableSet_radialBand (a b : Real) : MeasurableSet (radialBand a b) := by
  have hpow : Measurable fun r : Radius => (r : Real) ^ 4 := (continuous_subtype_val.pow 4).measurable
  exact (measurableSet_lt measurable_const hpow).inter
    (measurableSet_le hpow measurable_const)

 theorem volumeIoiPow_radialBand (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) :
    Measure.volumeIoiPow 3 (radialBand a b) = ENNReal.ofReal ((b-a)/4) := by
  let A : Set Radius := {r | (r : Real)^4 ≤ a}
  let B : Set Radius := {r | (r : Real)^4 ≤ b}
  have hpow : Measurable fun r : Radius => (r : Real) ^ 4 := (continuous_subtype_val.pow 4).measurable
  have hA : MeasurableSet A := measurableSet_le hpow measurable_const
  have hsub : A ⊆ B := by
    intro r hr
    exact hr.trans hab
  have he : radialBand a b = B \ A := by
    ext r
    simp [radialBand, A, B, not_le, and_comm]
  have hAf : Measure.volumeIoiPow 3 A ≠ ⊤ := by
    rw [volumeIoiPow_three_radialSlice a ha]
    exact ENNReal.ofReal_ne_top
  rw [he, measure_sdiff hsub hA.nullMeasurableSet hAf,
    volumeIoiPow_three_radialSlice b (ha.trans hab),
    volumeIoiPow_three_radialSlice a ha,
    ← ENNReal.ofReal_sub (b / 4) (by positivity : 0 ≤ a / 4)]
  congr 1
  ring

 theorem measurable_direction : Measurable direction := by
  unfold direction
  measurability

 theorem measurableSet_radialSet (tau eps : Real) : MeasurableSet (radialSet tau eps) := by
  apply measurableSet_le (by fun_prop)
  exact measurable_const.add (measurable_const.mul
    ((continuous_angularPerturbation tau).measurable.comp measurable_direction))

/-- An annular band restricted to four strips in angular coordinates. -/
def shellStrips (a b : Real) (q : Fin 4 -> E4) (h : Real) : Set E4 :=
  {x | a < norm x ^ 4 ∧ norm x ^ 4 ≤ b ∧
    ∃ i : Fin 4, |inner Real (direction x) (q i)| ≤ h}

 theorem measurableSet_shellStrips (a b : Real) (q : Fin 4 -> E4) (h : Real) :
    MeasurableSet (shellStrips a b q h) := by
  have hnorm4 : Measurable fun x : E4 => norm x ^ 4 := (continuous_norm.pow 4).measurable
  have hex : {x : E4 | ∃ i : Fin 4, |inner Real (direction x) (q i)| ≤ h} =
      ⋃ i : Fin 4, {x : E4 | |inner Real (direction x) (q i)| ≤ h} := by ext x; simp
  unfold shellStrips
  apply MeasurableSet.inter
  · exact measurableSet_lt measurable_const hnorm4
  · apply MeasurableSet.inter
    · exact measurableSet_le hnorm4 measurable_const
    · change MeasurableSet {x : E4 | ∃ i : Fin 4, |inner Real (direction x) (q i)| ≤ h}
      rw [hex]
      apply MeasurableSet.iUnion
      intro i
      exact measurableSet_le ((measurable_direction.inner measurable_const).abs)
        measurable_const

 theorem volume_shellStrips (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (q : Fin 4 -> E4) (h : Real) :
    volume (shellStrips a b q h) =
      sphereVolume (frameStrips q h) * ENNReal.ofReal ((b-a)/4) := by
  have hpre : ambientPolar ⁻¹' shellStrips a b q h =
      frameStrips q h ×ˢ radialBand a b := by
    ext p
    rcases p with ⟨u, r⟩
    simp only [Set.mem_preimage, shellStrips, Set.mem_setOf_eq, ambientPolar,
      norm_pos_smul_unitSphere, direction_pos_smul_unitSphere,
      Set.mem_prod, frameStrips, Set.mem_iUnion, radialBand]
    tauto
  rw [volume_eq_polar_preimage _ (measurableSet_shellStrips a b q h), hpre]
  change (sphereVolume.prod (Measure.volumeIoiPow 3))
    (frameStrips q h ×ˢ radialBand a b) = _
  rw [Measure.prod_prod, volumeIoiPow_radialBand a b ha hab]

 theorem volume_shellStrips_le (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (q : Fin 4 -> E4) (hq : Tensors.IsONFrame q)
    (h : Real) (hh : 0 ≤ h) :
    volume (shellStrips a b q h) ≤ ENNReal.ofReal (64 * h * (b-a)) := by
  rw [volume_shellStrips a b ha hab q h]
  calc
    sphereVolume (frameStrips q h) * ENNReal.ofReal ((b-a)/4)
        ≤ ENNReal.ofReal (256*h) * ENNReal.ofReal ((b-a)/4) := by
      gcongr
      exact sphereVolume_frameStrips_le q hq h hh
    _ = ENNReal.ofReal (64*h*(b-a)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 256*h)]
      congr 1
      ring

/-- Points where the radial body differs from the ball lie in the explicit
annulus. Strictness at the inner boundary is retained. -/
 theorem radial_symmDiff_band (tau eps B : Real) (hB : 0 < B)
    (hbound : forall u : E4, norm u = 1 -> |angularPerturbation tau u| ≤ B)
    {x : E4} (hx : x ∈ symmDiff (radialSet tau eps) (Metric.closedBall (0 : E4) 1)) :
    1 - |eps| * B < norm x ^ 4 ∧ norm x ^ 4 ≤ 1 + |eps| * B := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp [Set.mem_symmDiff, radialSet, direction, angularPerturbation,
      Tensors.A, Tensors.A0, Tensors.C, Tensors.B, Tensors.nForm, Tensors.mForm] at hx
  have hf := hbound (direction x) (norm_direction hx0)
  have he : |eps * angularPerturbation tau (direction x)| ≤ |eps| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hf (abs_nonneg eps)
  have hlo := (abs_le.mp he).1
  have hup := (abs_le.mp he).2
  have hball : x ∈ Metric.closedBall (0 : E4) 1 ↔ norm x ^ 4 ≤ 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (pow_le_one_iff_of_nonneg (norm_nonneg x) (by norm_num : (4 : Nat) ≠ 0)).symm
  have heB : 0 ≤ |eps| * B := mul_nonneg (abs_nonneg eps) hB.le
  rw [Set.mem_symmDiff] at hx
  rcases hx with ⟨hr, hb⟩ | ⟨hb, hr⟩
  · change norm x ^ 4 ≤ 1 + eps * angularPerturbation tau (direction x) at hr
    have hn : 1 < norm x ^ 4 := lt_of_not_ge (fun h => hb (hball.mpr h))
    constructor <;> linarith
  · have hb' := hball.mp hb
    have hn : 1 + eps * angularPerturbation tau (direction x) < norm x ^ 4 :=
      lt_of_not_ge hr
    constructor <;> linarith

 theorem radial_symmDiff_norm_bounds (tau eps B : Real) (hB : 0 < B)
    (hsmall : |eps| * B ≤ 1/2)
    (hbound : forall u : E4, norm u = 1 -> |angularPerturbation tau u| ≤ B)
    {x : E4} (hx : x ∈ symmDiff (radialSet tau eps) (Metric.closedBall (0 : E4) 1)) :
    (1/2 : Real) < norm x ∧ norm x ≤ 2 := by
  have h := radial_symmDiff_band tau eps B hB hbound hx
  constructor
  · by_contra! hn
    have hp := pow_le_pow_left₀ (norm_nonneg x) hn 4
    norm_num at hp
    linarith [h.1]
  · apply (pow_le_pow_iff_left₀ (norm_nonneg x) (by norm_num : (0 : Real) ≤ 2)
      (by norm_num : (4 : Nat) ≠ 0)).mp
    norm_num
    linarith [h.2]

 theorem radialSet_subset_ball_two (tau eps B : Real) (hB : 0 < B)
    (hsmall : |eps| * B ≤ 1/2)
    (hbound : forall u : E4, norm u = 1 -> |angularPerturbation tau u| ≤ B) :
    radialSet tau eps ⊆ Metric.closedBall (0 : E4) 2 := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp
  have hf := hbound (direction x) (norm_direction hx0)
  have he : eps * angularPerturbation tau (direction x) ≤ |eps| * B := by
    calc
      eps * angularPerturbation tau (direction x)
          ≤ |eps * angularPerturbation tau (direction x)| := le_abs_self _
      _ = |eps| * |angularPerturbation tau (direction x)| := abs_mul _ _
      _ ≤ |eps| * B := mul_le_mul_of_nonneg_left hf (abs_nonneg eps)
  have hp : norm x ^ 4 ≤ (2 : Real)^4 := by
    change norm x ^ 4 ≤ 1 + eps * angularPerturbation tau (direction x) at hx
    norm_num
    linarith
  change norm (x - 0) ≤ 2
  rw [sub_zero]
  exact (pow_le_pow_iff_left₀ (norm_nonneg x) (by norm_num : (0 : Real) ≤ 2)
    (by norm_num : (4 : Nat) ≠ 0)).mp hp

end ShellBounds
end SoberonConvexBody
