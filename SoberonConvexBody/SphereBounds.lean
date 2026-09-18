import SoberonConvexBody.SphereMeasure
import SoberonConvexBody.FrameBasics

/-!
# Explicit thin-strip estimates on the four-dimensional unit sphere

The proof uses only the cone definition of `volume.toSphere`, the measure
of a rectangular box, and orthogonal invariance. There is no assumed
surface-area or coarea formula in this module.
-/

noncomputable section
namespace SoberonConvexBody.SphereGeometry
open Set MeasureTheory
open scoped Pointwise BigOperators

/-- A box with one short side and three sides of length two. -/
def coordinateBox (i : Fin 4) (h : Real) : Set V :=
  {x | forall j, |x j| ≤ if j = i then h else 1}

 theorem measurableSet_coordinateBox (i : Fin 4) (h : Real) :
    MeasurableSet (coordinateBox i h) := by
  unfold coordinateBox
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (by fun_prop) measurable_const

/-- Exact Euclidean volume of the coordinate box. -/
 theorem volume_coordinateBox (i : Fin 4) (h : Real) (hh : 0 ≤ h) :
    (volume : Measure V) (coordinateBox i h) = ENNReal.ofReal (16 * h) := by
  classical
  let w : Fin 4 -> Real := fun j => if j = i then h else 1
  let S : Set (Fin 4 -> Real) := Set.univ.pi (fun j => Set.Icc (-(w j)) (w j))
  have hS : MeasurableSet S := by
    apply MeasurableSet.univ_pi
    intro j
    exact measurableSet_Icc
  have hpre : (WithLp.ofLp : V -> Fin 4 -> Real) ⁻¹' S = coordinateBox i h := by
    ext x
    simp [S, w, coordinateBox, abs_le, Pi.le_def, forall_and]
  calc
    (volume : Measure V) (coordinateBox i h)
        = (volume : Measure V) (WithLp.ofLp ⁻¹' S) := by rw [hpre]
    _ = (Measure.map (WithLp.ofLp : V -> Fin 4 -> Real) volume) S := by
      rw [Measure.map_apply (WithLp.measurable_ofLp 2 (Fin 4 -> Real)) hS]
    _ = (volume : Measure (Fin 4 -> Real)) S := by
      rw [(PiLp.volume_preserving_ofLp (Fin 4)).map_eq]
    _ = ∏ j : Fin 4, ENNReal.ofReal (2 * w j) := by
      rw [volume_pi_pi]
      apply Finset.prod_congr rfl
      intro j _
      rw [Real.volume_Icc]
      congr 1
      ring
    _ = ENNReal.ofReal (16 * h) := by
      fin_cases i <;>
        norm_num [w, Fin.prod_univ_succ, ENNReal.ofReal_mul, hh] <;> ring

/-- Directions in a strip about one coordinate great sphere. -/
def coordinateStrip (i : Fin 4) (h : Real) : Set UnitSphere :=
  {u | |(u : V) i| ≤ h}

 theorem measurableSet_coordinateStrip (i : Fin 4) (h : Real) :
    MeasurableSet (coordinateStrip i h) := by
  exact measurableSet_le (by fun_prop) measurable_const

/-- A coarse bound is enough: the cone lies in a box of volume `16*h`,
and the cone-to-sphere normalization multiplies by four. -/
 theorem sphereVolume_coordinateStrip_le (i : Fin 4) (h : Real) (hh : 0 ≤ h) :
    sphereVolume (coordinateStrip i h) ≤ ENNReal.ofReal (64 * h) := by
  let cone : Set V := Ioo (0 : Real) 1 •
    ((Subtype.val : UnitSphere -> V) '' coordinateStrip i h)
  have hsub : cone ⊆ coordinateBox i h := by
    rintro x ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
    intro j
    change |r * (u : V) j| ≤ if j = i then h else 1
    rw [abs_mul, abs_of_pos hr.1]
    have hmul : r * |(u : V) j| ≤ |(u : V) j| := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr.2.le) (abs_nonneg ((u : V) j))]
    by_cases hj : j = i
    · subst j
      simp only [if_true]
      exact hmul.trans hu
    · simp only [if_neg hj]
      have hn : |(u : V) j| ≤ 1 := by
        simpa only [Real.norm_eq_abs, norm_coe] using PiLp.norm_apply_le (u : V) j
      exact hmul.trans hn
  have hdim : Module.finrank Real V = 4 := by simp [V, Tensors.E4]
  calc
    sphereVolume (coordinateStrip i h) = (4 : ENNReal) * (volume : Measure V) cone := by
      rw [sphereVolume, Measure.toSphere_apply' _ (measurableSet_coordinateStrip i h)]
      simp [hdim, cone]
    _ ≤ 4 * (volume : Measure V) (coordinateBox i h) := by
      gcongr
    _ = 4 * ENNReal.ofReal (16 * h) := by rw [volume_coordinateBox i h hh]
    _ = ENNReal.ofReal (64 * h) := by
      rw [show (4 : ENNReal) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 4)]
      congr 1
      ring

/-- The union of the four strips in a prescribed orthonormal frame. -/
def frameStrips (q : Fin 4 -> V) (h : Real) : Set UnitSphere :=
  ⋃ i : Fin 4, {u : UnitSphere | |inner Real (u : V) (q i)| ≤ h}

 theorem measurableSet_frameStrips (q : Fin 4 -> V) (h : Real) :
    MeasurableSet (frameStrips q h) := by
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

 theorem sphereVolume_frameStrip_le (q : Fin 4 -> V) (hq : Tensors.IsONFrame q)
    (i : Fin 4) (h : Real) (hh : 0 ≤ h) :
    sphereVolume {u : UnitSphere | |inner Real (u : V) (q i)| ≤ h}
      ≤ ENNReal.ofReal (64 * h) := by
  let e := hq.toIsometry
  let S : Set UnitSphere := {u | |inner Real (u : V) (q i)| ≤ h}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hp : (sphereMap e) ⁻¹' S = coordinateStrip i h := by
    ext u
    simp only [Set.mem_preimage, S, coordinateStrip, Set.mem_setOf_eq, sphereMap_coe]
    rw [hq.inner_toIsometry]
  have heq : sphereVolume S = sphereVolume (coordinateStrip i h) := by
    calc
      sphereVolume S = (Measure.map (sphereMap e) sphereVolume) S := by
        rw [(sphereMap_measurePreserving e).map_eq]
      _ = sphereVolume ((sphereMap e) ⁻¹' S) := by
        rw [Measure.map_apply (sphereMap e).continuous.measurable hS]
      _ = sphereVolume (coordinateStrip i h) := by rw [hp]
  exact heq.le.trans (sphereVolume_coordinateStrip_le i h hh)

 theorem sphereVolume_frameStrips_le (q : Fin 4 -> V) (hq : Tensors.IsONFrame q)
    (h : Real) (hh : 0 ≤ h) :
    sphereVolume (frameStrips q h) ≤ ENNReal.ofReal (256 * h) := by
  calc
    sphereVolume (frameStrips q h)
        ≤ ∑' i : Fin 4,
          sphereVolume {u : UnitSphere | |inner Real (u : V) (q i)| ≤ h} :=
      measure_iUnion_le _
    _ = ∑ i : Fin 4,
          sphereVolume {u : UnitSphere | |inner Real (u : V) (q i)| ≤ h} :=
      tsum_fintype _
    _ ≤ ∑ _i : Fin 4, ENNReal.ofReal (64 * h) := by
      apply Finset.sum_le_sum
      intro i _
      exact sphereVolume_frameStrip_le q hq i h hh
    _ = 4 * ENNReal.ofReal (64 * h) := by simp
    _ = ENNReal.ofReal (256 * h) := by
      rw [show (4 : ENNReal) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 4)]
      congr 1
      ring

end SoberonConvexBody.SphereGeometry
