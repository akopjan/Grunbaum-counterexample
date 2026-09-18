import SoberonConvexBody.TensorDefs

/-!
# Rotations and null coordinate sections of the unit sphere

The normalization is mathlib's `volume.toSphere`. Its cone formula is used
directly, so no separate surface measure is postulated.
-/

noncomputable section
namespace SoberonConvexBody.SphereGeometry

open Set MeasureTheory
open scoped Pointwise BigOperators

abbrev V := Tensors.E4
abbrev UnitSphere := ↥(Metric.sphere (0 : V) 1)

def sphereVolume : Measure UnitSphere := (volume : Measure V).toSphere

@[simp] theorem norm_coe (u : UnitSphere) : norm (u : V) = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using u.property

/-- An ambient orthogonal transformation restricted to the sphere. -/
def sphereMap (e : V ≃ₗᵢ[Real] V) : UnitSphere ≃ₜ UnitSphere where
  toEquiv := {
    toFun := fun u => ⟨e (u : V), by
      change dist (e (u : V)) 0 = 1
      rw [dist_zero_right, e.norm_map, norm_coe]⟩
    invFun := fun u => ⟨e.symm (u : V), by
      change dist (e.symm (u : V)) 0 = 1
      rw [dist_zero_right, e.symm.norm_map, norm_coe]⟩
    left_inv := by
      intro u
      apply Subtype.ext
      exact e.symm_apply_apply (u : V)
    right_inv := by
      intro u
      apply Subtype.ext
      exact e.apply_symm_apply (u : V) }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem sphereMap_coe (e : V ≃ₗᵢ[Real] V) (u : UnitSphere) :
    ((sphereMap e u : UnitSphere) : V) = e (u : V) := rfl

@[simp] theorem sphereMap_symm_coe (e : V ≃ₗᵢ[Real] V) (u : UnitSphere) :
    (((sphereMap e).symm u : UnitSphere) : V) = e.symm (u : V) := rfl

private theorem cone_preimage (e : V ≃ₗᵢ[Real] V) (s : Set UnitSphere) :
    Ioo (0 : Real) 1 • ((Subtype.val : UnitSphere -> V) ''
      ((sphereMap e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : Real) 1 • ((Subtype.val : UnitSphere -> V) '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨r, hr, e (u : V), ?_, ?_⟩
    · exact ⟨sphereMap e u, hu, rfl⟩
    · simp
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, hx⟩
    refine ⟨r, hr, e.symm (u : V), ?_, ?_⟩
    · refine ⟨(sphereMap e).symm u, ?_, rfl⟩
      simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hu
    · apply e.injective
      simpa using hx

/-- Orthogonal changes of coordinates preserve the actual sphere measure. -/
theorem sphereMap_measurePreserving (e : V ≃ₗᵢ[Real] V) :
    MeasurePreserving (sphereMap e) sphereVolume sphereVolume := by
  have hm : Measurable (sphereMap e) := (sphereMap e).continuous.measurable
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hm hs]
  change (volume : Measure V).toSphere ((sphereMap e) ⁻¹' s) =
    (volume : Measure V).toSphere s
  rw [Measure.toSphere_apply' _ (hm hs), Measure.toSphere_apply' _ hs,
    cone_preimage]
  congr 1
  calc
    (volume : Measure V) (e ⁻¹'
        (Ioo (0 : Real) 1 • ((Subtype.val : UnitSphere -> V) '' s))) =
        (Measure.map e volume)
          (Ioo (0 : Real) 1 • ((Subtype.val : UnitSphere -> V) '' s)) :=
      (e.toMeasurableEquiv.map_apply _).symm
    _ = (volume : Measure V)
        (Ioo (0 : Real) 1 • ((Subtype.val : UnitSphere -> V) '' s)) := by
      rw [e.measurePreserving.map_eq]

/-- Change of variables for scalar sphere integrals. -/
theorem integral_comp_sphereMap (e : V ≃ₗᵢ[Real] V) (f : UnitSphere -> Real) :
    (∫ u, f (sphereMap e u) ∂ sphereVolume) =
      ∫ u, f u ∂ sphereVolume := by
  exact (sphereMap_measurePreserving e).integral_comp
    (sphereMap e).measurableEmbedding f

private def coordinateKernel (i : Fin 4) : Submodule Real V where
  carrier := {x | x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x i = 0 at hx
    change y i = 0 at hy
    change (x + y) i = 0
    simp [hx, hy]
  smul_mem' := by
    intro a x hx
    change x i = 0 at hx
    change (a • x) i = 0
    simp [hx]

private theorem coordinateKernel_ne_top (i : Fin 4) :
    coordinateKernel i ≠ ⊤ := by
  intro h
  have hx : (WithLp.toLp 2 (fun j : Fin 4 => if j = i then (1 : Real) else 0) : V)
      ∈ coordinateKernel i := by
    rw [h]
    trivial
  change ((WithLp.toLp 2 (fun j : Fin 4 => if j = i then (1 : Real) else 0) : V) i) = 0 at hx
  simp only [PiLp.toLp_apply, ↓reduceIte] at hx
  norm_num at hx

/-- Intersections of coordinate hyperplanes with the sphere are null. -/
theorem sphere_coordinate_zero (i : Fin 4) :
    sphereVolume (setOf fun (u : UnitSphere) => (u : V) i = 0) = 0 := by
  have hs : MeasurableSet (setOf fun (u : UnitSphere) => (u : V) i = 0) :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hk : (volume : Measure V) (coordinateKernel i : Set V) = 0 :=
    volume.addHaar_submodule (coordinateKernel i) (coordinateKernel_ne_top i)
  have hc : (volume : Measure V)
      (Ioo (0 : Real) 1 • ((Subtype.val : UnitSphere -> V) ''
        (setOf fun (u : UnitSphere) => (u : V) i = 0))) = 0 := by
    apply measure_mono_null _ hk
    rintro x ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
    change (r • (u : V)) i = 0
    change (u : V) i = 0 at hu
    simp [hu]
  unfold sphereVolume
  rw [Measure.toSphere_apply' _ hs, hc, mul_zero]

/-- Every coordinate is nonzero outside a set of sphere measure zero. -/
theorem ae_all_coordinates_ne_zero :
    ∀ᵐ (u : UnitSphere) ∂ sphereVolume, forall i : Fin 4, (u : V) i ≠ 0 := by
  have : Countable (Fin 4) := inferInstance
  rw [ae_all_iff]
  intro i
  filter_upwards [compl_mem_ae_iff.2 (sphere_coordinate_zero i)] with u hu
  exact hu

/-- The nonnegative coordinate monomial used by the moment computation. -/
def absCoordinateProduct (I : Finset (Fin 4)) (u : UnitSphere) : Real :=
  ∏ i ∈ I, abs ((u : V) i)

theorem absCoordinateProduct_nonneg (I : Finset (Fin 4)) (u : UnitSphere) :
    0 <= absCoordinateProduct I u := by
  exact Finset.prod_nonneg (fun i _ => abs_nonneg ((u : V) i))

theorem absCoordinateProduct_le_one (I : Finset (Fin 4)) (u : UnitSphere) :
    absCoordinateProduct I u <= 1 := by
  apply Finset.prod_le_one₀
  · intro i _
    exact abs_nonneg ((u : V) i)
  · intro i _
    have h := PiLp.norm_apply_le (u : V) i
    simpa only [Real.norm_eq_abs, norm_coe] using h

theorem integrable_absCoordinateProduct (I : Finset (Fin 4)) :
    Integrable (absCoordinateProduct I) sphereVolume := by
  letI : IsFiniteMeasure sphereVolume := by
    unfold sphereVolume
    infer_instance
  apply (integrable_const (1 : Real)).mono'
  · unfold absCoordinateProduct
    fun_prop
  · exact Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (absCoordinateProduct_nonneg I u)]
      exact absCoordinateProduct_le_one I u)

/-- Every nonnegative coordinate moment is the integral of a concrete
function against the sphere measure, not an extra tensor parameter. -/
def coordinateMoment (I : Finset (Fin 4)) : Real :=
  ∫ u, absCoordinateProduct I u ∂ sphereVolume

private def balancedPoint : UnitSphere :=
  ⟨WithLp.toLp 2 (fun _ : Fin 4 => (1 / 2 : Real)), by
    rw [Metric.mem_sphere, dist_zero_right]
    have hn : ‖(WithLp.toLp 2 (fun _ : Fin 4 => (1 / 2 : Real)) : V)‖^2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_four]
      norm_num
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun _ : Fin 4 => (1 / 2 : Real)) : V)]⟩

/-- Coordinate moments are strictly positive, including all four cubic
moments and the quartic moment needed for the high characters. -/
theorem coordinateMoment_pos (I : Finset (Fin 4)) :
    0 < coordinateMoment I := by
  letI : sphereVolume.IsOpenPosMeasure := by
    unfold sphereVolume
    infer_instance
  have hc : Continuous (absCoordinateProduct I) := by
    unfold absCoordinateProduct
    fun_prop
  have hx : absCoordinateProduct I balancedPoint ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    norm_num [balancedPoint, PiLp.toLp_apply]
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (integrable_absCoordinateProduct I)
    (absCoordinateProduct_nonneg I) hx

/-- Sphere integration annihilates functions odd under an orthogonal
symmetry. No integrability assumption is needed for the totalized integral. -/
theorem integral_eq_zero_of_odd_symmetry
    (e : V ≃ₗᵢ[Real] V) (f : UnitSphere -> Real)
    (h : forall u, f (sphereMap e u) = -f u) :
    (∫ u, f u ∂ sphereVolume) = 0 := by
  have he := integral_comp_sphereMap e f
  simp_rw [h] at he
  rw [integral_neg] at he
  linarith

/-- Almost-everywhere version, suitable for sign functions whose convention
at zero breaks pointwise oddness on a null section. -/
theorem integral_eq_zero_of_ae_odd_symmetry
    (e : V ≃ₗᵢ[Real] V) (f : UnitSphere -> Real)
    (h : ∀ᵐ u ∂ sphereVolume, f (sphereMap e u) = -f u) :
    (∫ u, f u ∂ sphereVolume) = 0 := by
  have he := integral_comp_sphereMap e f
  have he' := integral_congr_ae h
  rw [integral_neg] at he'
  linarith

/-- A coordinate reflection, defined without choosing an orthonormal basis. -/
def coordinateReflection (i : Fin 4) : V ≃ₗᵢ[Real] V where
  toFun x := WithLp.toLp 2 (fun j => if j = i then -x j else x j)
  invFun x := WithLp.toLp 2 (fun j => if j = i then -x j else x j)
  left_inv := by
    intro x
    ext j
    by_cases h : j = i <;> simp [PiLp.toLp_apply, h]
  right_inv := by
    intro x
    ext j
    by_cases h : j = i <;> simp [PiLp.toLp_apply, h]
  map_add' := by
    intro x y
    ext j
    by_cases h : j = i <;> simp [PiLp.toLp_apply, h, add_comm]
  map_smul' := by
    intro a x
    ext j
    by_cases h : j = i <;> simp [PiLp.toLp_apply, h]
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = i <;> simp [PiLp.toLp_apply, h]

@[simp] theorem coordinateReflection_apply (i j : Fin 4) (x : V) :
    coordinateReflection i x j = if j = i then -x j else x j := rfl

@[simp] theorem sphere_coordinateReflection_apply
    (i j : Fin 4) (u : UnitSphere) :
    (sphereMap (coordinateReflection i) u : V) j =
      if j = i then -(u : V) j else (u : V) j := rfl

end SoberonConvexBody.SphereGeometry
