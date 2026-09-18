import SoberonConvexBody.SphereParity

/-!
# Degree at most two under the coordinate sign characters

All selection rules are proved by averaging the sixteen coordinate reflections.
No numerical evaluation of a spherical moment is needed.
-/
noncomputable section
namespace SoberonConvexBody.SphereGeometry
open Set MeasureTheory
open scoped BigOperators
set_option maxRecDepth 200000
set_option maxHeartbeats 0

private def signZ (b : Bool) : Int := if b then 1 else -1
private def characterZ (I : Finset (Fin 4)) (s : SignQuad) : Int :=
  ∏ i ∈ I, signZ (quadPattern s i)

private theorem cast_signZ (b : Bool) : (signZ b : Real) = signFactor b := by
  cases b <;> norm_num [signZ, signFactor]

private theorem cast_characterZ (I : Finset (Fin 4)) (s : SignQuad) :
    (characterZ I s : Real) = cubeCharacter I s := by
  simp [characterZ, cubeCharacter, cast_signZ]

private theorem linear_selection_Z : forall I : Finset (Fin 4), forall k : Fin 4,
    (∑ s : SignQuad, characterZ I s * signZ (quadPattern s k)) =
      if I = {k} then (16 : Int) else 0 := by
  decide

private theorem quadratic_selection_Z : forall I : Finset (Fin 4), I.Nonempty ->
    forall k l : Fin 4,
    (∑ s : SignQuad, characterZ I s *
      signZ (quadPattern s k) * signZ (quadPattern s l)) =
      if k ≠ l ∧ I = {k,l} then (16 : Int) else 0 := by
  decide

 theorem linear_selection (I : Finset (Fin 4)) (k : Fin 4) :
    (∑ s : SignQuad, cubeCharacter I s * signFactor (quadPattern s k)) =
      if I = {k} then (16 : Real) else 0 := by
  have h := linear_selection_Z I k
  have h' := congrArg (fun z : Int => (z : Real)) h
  simpa [Int.cast_sum, Int.cast_mul, cast_characterZ, cast_signZ] using h'

 theorem quadratic_selection (I : Finset (Fin 4)) (hI : I.Nonempty) (k l : Fin 4) :
    (∑ s : SignQuad, cubeCharacter I s *
      signFactor (quadPattern s k) * signFactor (quadPattern s l)) =
      if k ≠ l ∧ I = {k,l} then (16 : Real) else 0 := by
  have h := quadratic_selection_Z I hI k l
  have h' := congrArg (fun z : Int => (z : Real)) h
  simpa [Int.cast_sum, Int.cast_mul, cast_characterZ, cast_signZ] using h'

 theorem integral_character_coordinate (I : Finset (Fin 4)) (k : Fin 4) :
    (∫ u : UnitSphere, coordinateCharacter I u * (u : V) k ∂sphereVolume) =
      if I = {k} then coordinateMoment {k} else 0 := by
  have hint := integrable_sign_mul_continuous (coordinateCharacter I)
    (fun u : UnitSphere => (u : V) k) (measurable_coordinateCharacter I)
    (abs_coordinateCharacter I) (by fun_prop)
  have havg : cubeAverage (fun u : UnitSphere => coordinateCharacter I u * (u : V) k)
      =ᵐ[sphereVolume] (fun u => if I = {k} then absCoordinateProduct {k} u else 0) := by
    filter_upwards [ae_all_coordinates_ne_zero] with u hu
    unfold cubeAverage
    simp_rw [coordinateCharacter_signChange I _ u hu, sphereMap_coe,
      signChange_apply]
    have hsum : (∑ s : SignQuad,
        (cubeCharacter I s * coordinateCharacter I u) *
          (signFactor (quadPattern s k) * (u : V) k)) =
        (∑ s : SignQuad, cubeCharacter I s * signFactor (quadPattern s k)) *
          (coordinateCharacter I u * (u : V) k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hsum, linear_selection]
    by_cases h : I = {k}
    · subst I
      norm_num [coordinateCharacter, absCoordinateProduct, closedSign_mul_self, ← mul_assoc]
    · simp [h]
  rw [← integral_cubeAverage _ hint, integral_congr_ae havg]
  by_cases h : I = {k}
  · simp [h, coordinateMoment]
  · simp [h]

 theorem integral_character_coordinate_mul (I : Finset (Fin 4)) (hI : I.Nonempty)
    (k l : Fin 4) :
    (∫ u : UnitSphere,
      coordinateCharacter I u * ((u : V) k * (u : V) l) ∂sphereVolume) =
      if k ≠ l ∧ I = {k,l} then coordinateMoment {k,l} else 0 := by
  have hint := integrable_sign_mul_continuous (coordinateCharacter I)
    (fun u : UnitSphere => (u : V) k * (u : V) l) (measurable_coordinateCharacter I)
    (abs_coordinateCharacter I) (by fun_prop)
  have havg : cubeAverage (fun u : UnitSphere =>
        coordinateCharacter I u * ((u : V) k * (u : V) l))
      =ᵐ[sphereVolume]
        (fun u => if k ≠ l ∧ I = {k,l} then absCoordinateProduct {k,l} u else 0) := by
    filter_upwards [ae_all_coordinates_ne_zero] with u hu
    unfold cubeAverage
    simp_rw [coordinateCharacter_signChange I _ u hu, sphereMap_coe,
      signChange_apply]
    have hsum : (∑ s : SignQuad,
        (cubeCharacter I s * coordinateCharacter I u) *
          ((signFactor (quadPattern s k) * (u : V) k) *
           (signFactor (quadPattern s l) * (u : V) l))) =
        (∑ s : SignQuad, cubeCharacter I s *
          signFactor (quadPattern s k) * signFactor (quadPattern s l)) *
          (coordinateCharacter I u * ((u : V) k * (u : V) l)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hsum, quadratic_selection I hI]
    by_cases h : k ≠ l ∧ I = {k,l}
    · rcases h with ⟨hkl, rfl⟩
      have hm := character_mul_coordinates ({k,l} : Finset (Fin 4)) u
      simpa [hkl, Finset.prod_insert, Finset.prod_singleton, ← mul_assoc] using hm
    · simp [h]
  rw [← integral_cubeAverage _ hint, integral_congr_ae havg]
  by_cases h : k ≠ l ∧ I = {k,l}
  · simp [h, coordinateMoment]
  · simp [h]

/-- A scalar polynomial of degree at most two on the sphere. -/
def quadraticSphere (a : Real) (b : Fin 4 -> Real) (m : Fin 4 -> Fin 4 -> Real)
    (u : UnitSphere) : Real :=
  a + ∑ i : Fin 4, b i * (u : V) i +
    ∑ i : Fin 4, ∑ j : Fin 4, m i j * ((u : V) i * (u : V) j)

 theorem continuous_quadraticSphere (a : Real) (b : Fin 4 -> Real)
    (m : Fin 4 -> Fin 4 -> Real) : Continuous (quadraticSphere a b m) := by
  unfold quadraticSphere
  fun_prop

 theorem integral_character_sum {J : Type*} (s : Finset J)
    (I : Finset (Fin 4)) (f : J -> UnitSphere -> Real)
    (hf : ∀ j ∈ s, Continuous (f j)) :
    (∫ u : UnitSphere, coordinateCharacter I u * (∑ j ∈ s, f j u)
      ∂sphereVolume) =
      ∑ j ∈ s, ∫ u : UnitSphere, coordinateCharacter I u * f j u
        ∂sphereVolume := by
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s (fun j hj =>
    integrable_sign_mul_continuous (coordinateCharacter I) (f j)
      (measurable_coordinateCharacter I) (abs_coordinateCharacter I) (hf j hj))

 theorem integral_character_quadraticSphere (I : Finset (Fin 4)) (hI : I.Nonempty)
    (a : Real) (b : Fin 4 -> Real) (m : Fin 4 -> Fin 4 -> Real) :
    (∫ u : UnitSphere, coordinateCharacter I u * quadraticSphere a b m u
      ∂sphereVolume) =
    (∑ i : Fin 4, b i * (if I = {i} then coordinateMoment {i} else 0)) +
    (∑ i : Fin 4, ∑ j : Fin 4,
      m i j * (if i ≠ j ∧ I = {i,j} then coordinateMoment {i,j} else 0)) := by
  have hi := integrable_sign_mul_continuous (coordinateCharacter I)
    (fun u : UnitSphere => a + ∑ i : Fin 4, b i * (u : V) i)
    (measurable_coordinateCharacter I) (abs_coordinateCharacter I) (by fun_prop)
  have hj := integrable_sign_mul_continuous (coordinateCharacter I)
    (fun u : UnitSphere => ∑ i : Fin 4, ∑ j : Fin 4,
      m i j * ((u : V) i * (u : V) j))
    (measurable_coordinateCharacter I) (abs_coordinateCharacter I) (by fun_prop)
  have h0 := integrable_sign_mul_continuous (coordinateCharacter I)
    (fun _u : UnitSphere => a)
    (measurable_coordinateCharacter I) (abs_coordinateCharacter I) continuous_const
  have h1 := integrable_sign_mul_continuous (coordinateCharacter I)
    (fun u : UnitSphere => ∑ i : Fin 4, b i * (u : V) i)
    (measurable_coordinateCharacter I) (abs_coordinateCharacter I) (by fun_prop)
  have h_add : (fun u : UnitSphere => coordinateCharacter I u * quadraticSphere a b m u) =
      (fun u => (coordinateCharacter I u * (a + ∑ i : Fin 4, b i * (u : V) i)) +
        (coordinateCharacter I u * (∑ i : Fin 4, ∑ j : Fin 4, m i j * ((u : V) i * (u : V) j)))) := by
    ext u
    simp only [quadraticSphere]
    ring
  rw [h_add, integral_add hi hj]
  have h_add2 : (fun u : UnitSphere => coordinateCharacter I u * (a + ∑ i : Fin 4, b i * (u : V) i)) =
      (fun u => coordinateCharacter I u * a + coordinateCharacter I u * ∑ i : Fin 4, b i * (u : V) i) := by
    ext u
    ring
  rw [h_add2, integral_add h0 h1,
    integral_mul_const, integral_coordinateCharacter_eq_zero I hI, zero_mul, zero_add]
  rw [integral_character_sum Finset.univ I
    (fun i u => b i * (u : V) i) (by intro i _; fun_prop)]
  rw [integral_character_sum Finset.univ I
    (fun i u => ∑ j : Fin 4, m i j * ((u : V) i * (u : V) j))
    (by intro i _; fun_prop)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have he : (fun u : UnitSphere => coordinateCharacter I u * (b i * (u : V) i)) =
        (fun u => b i * (coordinateCharacter I u * (u : V) i)) := by
      funext u; ring
    rw [he, integral_const_mul, integral_character_coordinate]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_character_sum Finset.univ I
      (fun j u => m i j * ((u : V) i * (u : V) j)) (by intro j _; fun_prop)]
    apply Finset.sum_congr rfl
    intro j _
    have he : (fun u : UnitSphere =>
        coordinateCharacter I u * (m i j * ((u : V) i * (u : V) j))) =
        (fun u => m i j * (coordinateCharacter I u * ((u : V) i * (u : V) j))) := by
      funext u; ring
    rw [he, integral_const_mul, integral_character_coordinate_mul I hI]

 theorem integral_character_quadraticSphere_high
    (I : Finset (Fin 4)) (hI : 3 ≤ I.card)
    (a : Real) (b : Fin 4 -> Real) (m : Fin 4 -> Fin 4 -> Real) :
    (∫ u : UnitSphere, coordinateCharacter I u * quadraticSphere a b m u
      ∂sphereVolume) = 0 := by
  have hn : I.Nonempty := Finset.card_pos.mp (by omega)
  rw [integral_character_quadraticSphere I hn]
  have hsingle (i : Fin 4) : I ≠ {i} := by intro he; subst I; simp at hI
  have hpair (i j : Fin 4) : I ≠ {i,j} := by
    intro he
    subst I
    have hc : ({i,j} : Finset (Fin 4)).card ≤ 2 := by
      calc
        _ ≤ ({j} : Finset (Fin 4)).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    omega
  simp [hsingle, hpair]

 theorem integral_character_quadraticSphere_singleton
    (k : Fin 4) (a : Real) (b : Fin 4 -> Real)
    (m : Fin 4 -> Fin 4 -> Real) :
    (∫ u : UnitSphere, coordinateCharacter {k} u * quadraticSphere a b m u
      ∂sphereVolume) = b k * coordinateMoment {k} := by
  rw [integral_character_quadraticSphere {k} (by simp)]
  have hs (i : Fin 4) : ({k} : Finset (Fin 4)) = {i} ↔ i = k := by
    simp [Finset.singleton_inj, eq_comm]
  have hp (i j : Fin 4) : ¬ (i ≠ j ∧ ({k} : Finset (Fin 4)) = {i,j}) := by
    rintro ⟨hij, he⟩
    have hc := congrArg Finset.card he
    simp [hij] at hc
  simp [hs, hp]

 theorem integral_character_quadraticSphere_pair
    (k l : Fin 4) (hkl : k ≠ l) (a : Real) (b : Fin 4 -> Real)
    (m : Fin 4 -> Fin 4 -> Real) :
    (∫ u : UnitSphere, coordinateCharacter {k,l} u * quadraticSphere a b m u
      ∂sphereVolume) = (m k l + m l k) * coordinateMoment {k,l} := by
  rw [integral_character_quadraticSphere {k,l} (by simp)]
  fin_cases k <;> fin_cases l <;> (try contradiction) <;>
    (simp (config := { decide := true }) [Fin.sum_univ_succ]
     try rw [Finset.pair_comm 1 0]
     try rw [Finset.pair_comm 2 0]
     try rw [Finset.pair_comm 3 0]
     try rw [Finset.pair_comm 2 1]
     try rw [Finset.pair_comm 3 1]
     try rw [Finset.pair_comm 3 2]
     ring)

end SoberonConvexBody.SphereGeometry
