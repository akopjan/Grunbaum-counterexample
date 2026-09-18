import SoberonConvexBody.GeometryCore

/-!
# Polar integration for an arbitrary measurable radial region

The region is described by its fourth radial power. This is a genuine
specialization of the polar measure equivalence, independent of the tensor
polynomial used by the construction.
-/
noncomputable section
namespace SoberonConvexBody
open Set Real MeasureTheory
open scoped BigOperators

 theorem angular_setIntegral
    (K : Set E4) (hK : MeasurableSet K)
    (w : SphereGeometry.UnitSphere -> Real) (hw : Measurable w)
    (hw0 : forall u, 0 ≤ w u)
    (hmem : forall u : SphereGeometry.UnitSphere, forall r : Set.Ioi (0 : Real),
      (r : Real) • (u : E4) ∈ K ↔ (r : Real)^4 ≤ w u)
    (g : E4 -> Real) (hg : Measurable g)
    (hangular : forall r : Real, 0 < r -> forall u : E4, norm u = 1 ->
      g (r • u) = g u) :
    (∫ x in K, g x) = (1/4 : Real) *
      ∫ u : SphereGeometry.UnitSphere, g (u : E4) * w u
        ∂SphereGeometry.sphereVolume := by
  let S : Set (SphereGeometry.UnitSphere × Set.Ioi (0 : Real)) :=
    {p | (p.2 : Real)^4 ≤ w p.1}
  let P : Measure (SphereGeometry.UnitSphere × Set.Ioi (0 : Real)) :=
    volume.toSphere.prod (Measure.volumeIoiPow 3)
  have hS : MeasurableSet S := by
    exact measurableSet_le (by fun_prop) (hw.comp measurable_fst)
  have hdim : Module.finrank Real E4 = 4 := by simp [E4]
  have hm : forall p : SphereGeometry.UnitSphere × Set.Ioi (0 : Real),
      (↑((homeomorphUnitSphereProd E4).symm p) : E4) ∈ K ↔ p ∈ S := by
    intro p
    simpa only [homeomorphUnitSphereProd_symm_apply_coe, S, Set.mem_setOf_eq] using
      hmem p.1 p.2
  have hpush : Measure.map Prod.fst (P.restrict S) =
      volume.toSphere.withDensity (fun u => (Real.toNNReal (w u / 4) : ENNReal)) := by
    simpa only [P, S] using map_fst_restrict_radialProduct w hw hw0
  calc
    (∫ x in K, g x) = ∫ x : ({0}ᶜ : Set E4),
        K.indicator g (x : E4) ∂(volume.comap (Subtype.val : ({0}ᶜ : Set E4) → E4)) := by
      rw [← integral_indicator hK,
        integral_subtype_comap (measurableSet_singleton _).compl
          (fun x => K.indicator g x), restrict_compl_singleton]
    _ = ∫ p : SphereGeometry.UnitSphere × Set.Ioi (0 : Real),
        K.indicator g (↑((homeomorphUnitSphereProd E4).symm p) : E4) ∂P := by
      have hp := volume.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd E4))
        (fun p : SphereGeometry.UnitSphere × Set.Ioi (0 : Real) =>
          K.indicator g (↑((homeomorphUnitSphereProd E4).symm p) : E4))
      simpa [P, hdim] using hp
    _ = ∫ p in S, g (p.1 : E4) ∂P := by
      rw [← integral_indicator hS]
      apply integral_congr_ae
      filter_upwards with p
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem ((hm p).mpr hp), Set.indicator_of_mem hp]
        simpa only [homeomorphUnitSphereProd_symm_apply_coe] using
          hangular (p.2 : Real) p.2.property (p.1 : E4) (norm_coe_unitSphere p.1)
      · rw [Set.indicator_of_notMem (mt (hm p).mp hp), Set.indicator_of_notMem hp]
    _ = ∫ u : SphereGeometry.UnitSphere, g (u : E4)
        ∂Measure.map Prod.fst (P.restrict S) := by
      exact (integral_map measurable_fst.aemeasurable
        (hg.comp measurable_subtype_coe).aestronglyMeasurable).symm
    _ = ∫ u : SphereGeometry.UnitSphere, g (u : E4)
        ∂volume.toSphere.withDensity
          (fun u => (Real.toNNReal (w u / 4) : ENNReal)) := by rw [hpush]
    _ = ∫ u : SphereGeometry.UnitSphere, Real.toNNReal (w u / 4) • g (u : E4)
        ∂volume.toSphere := by
      rw [integral_withDensity_eq_integral_smul]
      measurability
    _ = ∫ u : SphereGeometry.UnitSphere, (1/4 : Real) * (g (u : E4) * w u)
        ∂volume.toSphere := by
      apply integral_congr_ae
      filter_upwards with u
      rw [NNReal.smul_def, Real.coe_toNNReal _ (div_nonneg (hw0 u) (by norm_num))]
      ring
    _ = (1/4 : Real) * ∫ u : SphereGeometry.UnitSphere, g (u : E4) * w u
        ∂SphereGeometry.sphereVolume := by
      rw [integral_const_mul]
      rfl

end SoberonConvexBody
