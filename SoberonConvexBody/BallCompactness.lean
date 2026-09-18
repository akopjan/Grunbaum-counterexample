import SoberonConvexBody.BallReflection

/-!
# Compact localization of small low Walsh coefficients

Continuity is proved by dominated convergence. The exceptional sets are actual
affine hyperplanes of Lebesgue measure zero. No cell-volume smoothness is assumed.
-/
noncomputable section
namespace SoberonConvexBody.BallCompactness
open Set MeasureTheory Filter
open scoped BigOperators Topology
open Tensors SphereGeometry BallLocal BallReflection

abbrev Param := (Fin 4 -> E4) × (Fin 4 -> Real)
def cfg (p : Param) : HyperplaneCfg := ⟨p.1,p.2⟩
def param (c : HyperplaneCfg) : Param := (c.normal,c.offset)
@[simp] theorem cfg_param (c : HyperplaneCfg) : cfg (param c)=c := by cases c; rfl

private theorem continuousAt_finProd {X J : Type*} [TopologicalSpace X]
    (s : Finset J) (f : J -> X -> Real) (x : X)
    (hf : ∀ j ∈ s, ContinuousAt (f j) x) :
    ContinuousAt (fun y => ∏ j ∈ s, f j y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X => (1 : Real)) x)
  | @insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    exact (hf j (Finset.mem_insert_self _ _)).mul
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

private theorem continuousAt_finSum {X J : Type*} [TopologicalSpace X]
    (s : Finset J) (f : J -> X -> Real) (x : X)
    (hf : ∀ j ∈ s, ContinuousAt (f j) x) :
    ContinuousAt (fun y => ∑ j ∈ s, f j y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X => (0 : Real)) x)
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self _ _)).add
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

theorem continuousAt_closedSign {r : Real} (hr : r ≠ 0) : ContinuousAt closedSign r := by
  rcases lt_or_gt_of_ne hr with hn | hp
  · have he : closedSign =ᶠ[nhds r] (fun _ => (-1 : Real)) := by
      filter_upwards [isOpen_Iio.mem_nhds hn] with x hx
      exact if_neg (not_le_of_gt hx)
    have hv : closedSign r = -1 := if_neg (not_le_of_gt hn)
    change Tendsto closedSign (nhds r) (nhds (closedSign r))
    rw [hv]
    exact tendsto_const_nhds.congr' he.symm
  · have he : closedSign =ᶠ[nhds r] (fun _ => (1 : Real)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hp] with x hx
      exact if_pos hx.le
    have hv : closedSign r = 1 := if_pos hp.le
    change Tendsto closedSign (nhds r) (nhds (closedSign r))
    rw [hv]
    exact tendsto_const_nhds.congr' he.symm

theorem continuousAt_walsh (p : Param) (hp : UnitCfg (cfg p)) (I : Walsh4.Index) :
    ContinuousAt (fun p : Param => walsh ballMeasure (cfg p) I) p := by
  apply continuousAt_of_dominated
    (bound := fun _ : E4 => (1 : Real))
  · exact Filter.Eventually.of_forall (fun p =>
      (Cells.measurable_signCharacter (cfg p) I).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun p => Filter.Eventually.of_forall (fun x => by
      simp [Real.norm_eq_abs,Cells.signCharacter,Walsh4.abs_char]))
  · exact integrable_const _
  · have hae : ∀ᵐ x ∂ballMeasure, forall i : Fin 4, inner Real x (p.1 i) ≠ p.2 i := by
      apply ae_all_iff.mpr
      intro i
      apply ae_inner_ne
      intro hz
      have hh := hp i
      change norm (p.1 i)=1 at hh
      simp [hz] at hh
    filter_upwards [hae] with x hx
    have hfun : (fun p : Param => Cells.signCharacter (cfg p) I x) =
        (fun p => ∏ i ∈ I, closedSign (inner Real x (p.1 i)-p.2 i)) := by
      funext p
      simp [Cells.signCharacter_eq_prod,closedSign,cfg,sub_nonneg]
    rw [hfun]
    apply continuousAt_finProd
    intro i _
    have hc : Continuous (fun y : Param => inner Real x (y.1 i) - y.2 i) :=
      ((continuous_const.inner ((continuous_apply i).comp continuous_fst)).sub ((continuous_apply i).comp continuous_snd))
    exact ContinuousAt.comp (x := p) (continuousAt_closedSign (sub_ne_zero.mpr (hx i))) hc.continuousAt

/-- A convenient continuous defect, counting both orders of each pair. -/
def deviation (p : Param) : Real :=
  (∑ i : Fin 4, |p.2 i|)+
    ∑ i : Fin 4, ∑ j : Fin 4, if i=j then 0 else |inner Real (p.1 i) (p.1 j)|

theorem deviation_nonneg (p : Param) : 0 ≤ deviation p := by unfold deviation; positivity

theorem continuous_deviation : Continuous deviation := by
  unfold deviation
  refine Continuous.add ?_ ?_
  · exact continuous_finset_sum _ (fun i _ => (continuous_apply i).comp continuous_snd |>.abs)
  · refine continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ => ?_))
    by_cases h : i = j
    · simp [h]
      exact continuous_const
    · simp [h]
      exact ((continuous_apply i).comp continuous_fst).inner ((continuous_apply j).comp continuous_fst) |>.abs

theorem offset_le_deviation (p : Param) (i : Fin 4) : |p.2 i| ≤ deviation p := by
  have h : |p.2 i| ≤ ∑ j : Fin 4, |p.2 j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (p.2 j)) (Finset.mem_univ i)
  have hp : 0 ≤ ∑ j : Fin 4, ∑ k : Fin 4,
      if j=k then 0 else |inner Real (p.1 j) (p.1 k)| := by positivity
  unfold deviation
  linarith

theorem inner_le_deviation (p : Param) (i j : Fin 4) (hij : i ≠ j) :
    |inner Real (p.1 i) (p.1 j)| ≤ deviation p := by
  have h1 : |inner Real (p.1 i) (p.1 j)| ≤
      ∑ k : Fin 4, if i=k then 0 else |inner Real (p.1 i) (p.1 k)| := by
    have h := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 4)))
      (f := fun k => if i=k then (0 : Real) else |inner Real (p.1 i) (p.1 k)|)
      (fun k _ => by positivity) (Finset.mem_univ j)
    simpa [hij] using h
  have h2 : (∑ k : Fin 4, if i=k then 0 else |inner Real (p.1 i) (p.1 k)|) ≤
      ∑ l : Fin 4, ∑ k : Fin 4, if l=k then 0 else |inner Real (p.1 l) (p.1 k)| :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 4)))
      (f := fun l => ∑ k : Fin 4, if l=k then (0 : Real) else |inner Real (p.1 l) (p.1 k)|)
      (fun l _ => by positivity) (Finset.mem_univ i)
  have ho : 0 ≤ ∑ k : Fin 4, |p.2 k| := by positivity
  unfold deviation
  linarith

theorem deviation_eq_zero (p : Param) (hoff : forall i, p.2 i=0)
    (hn : IsONFrame p.1) : deviation p=0 := by
  unfold deviation
  simp only [hoff,abs_zero,Finset.sum_const_zero,zero_add]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i=j
  · simp [hij]
  · simp [hij,hn i j]

def lowResidual (p : Param) : Real :=
  ∑ I : Walsh4.Index, if I.Nonempty ∧ I.card ≤ 2 then |walsh ballMeasure (cfg p) I| else 0

theorem lowResidual_nonneg (p : Param) : 0 ≤ lowResidual p := by unfold lowResidual; positivity

theorem component_le_lowResidual (p : Param) (I : Walsh4.Index)
    (hI : I.Nonempty) (hcard : I.card ≤ 2) :
    |walsh ballMeasure (cfg p) I| ≤ lowResidual p := by
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset Walsh4.Index))
    (f := fun J => if J.Nonempty ∧ J.card ≤ 2 then |walsh ballMeasure (cfg p) J| else 0)
    (fun J _ => by positivity) (Finset.mem_univ I)
  simpa [lowResidual,hI,hcard] using h

theorem lowResidual_le (p : Param) (b : Real) (hb : 0 ≤ b)
    (h : forall I : Walsh4.Index, I.Nonempty -> I.card ≤ 2 -> |walsh ballMeasure (cfg p) I| ≤ b) :
    lowResidual p ≤ 16*b := by
  have hcard : Fintype.card Walsh4.Index=16 := by decide
  calc
    lowResidual p ≤ ∑ _I : Walsh4.Index, b := by
      apply Finset.sum_le_sum
      intro I _
      split_ifs with hI
      · exact h I hI.1 hI.2
      · exact hb
    _ = 16*b := by simp [hcard]

def compactConfigs : Set Param :=
  (Set.univ.pi (fun _ : Fin 4 => Metric.sphere (0 : E4) 1)) ×ˢ
    (Set.univ.pi (fun _ : Fin 4 => Set.Icc (-2 : Real) 2))

theorem isCompact_configs : IsCompact compactConfigs := by
  exact (isCompact_univ_pi (fun _ : Fin 4 => isCompact_sphere (0 : E4) 1)).prod
    (isCompact_univ_pi (fun _ : Fin 4 => isCompact_Icc))

theorem mem_compactConfigs (p : Param) :
    p ∈ compactConfigs ↔ UnitCfg (cfg p) ∧ forall i, |p.2 i| ≤ 2 := by
  simp only [compactConfigs, Set.mem_prod, Set.mem_univ_pi, Metric.mem_sphere,
    dist_zero_right, Set.mem_Icc, UnitCfg, cfg, abs_le]

theorem continuousOn_lowResidual : ContinuousOn lowResidual compactConfigs := by
  intro p hp
  have hunit := ((mem_compactConfigs p).mp hp).1
  have h : ContinuousAt lowResidual p := by
    apply continuousAt_finSum
    intro I _
    by_cases hI : I.Nonempty ∧ I.card ≤ 2
    · simpa only [if_pos hI] using (continuousAt_walsh p hunit I).abs
    · simpa only [if_neg hI] using (continuousAt_const : ContinuousAt (fun _ : Param => (0 : Real)) p)
  exact h.continuousWithinAt

/-- Compactness upgrades exact rigidity to qualitative localization. -/
theorem small_residual_small_deviation (zeta : Real) (hzeta : 0 < zeta) :
    ∃ r0 : Real, 0 < r0 ∧ forall p : Param,
      p ∈ compactConfigs -> lowResidual p < r0 -> deviation p < zeta := by
  let T : Set Param := compactConfigs ∩ {p | zeta ≤ deviation p}
  have hT : IsCompact T := isCompact_configs.inter_right
    (isClosed_le continuous_const continuous_deviation)
  have hpos : ∀ p ∈ T, 0 < lowResidual p := by
    intro p hp
    by_contra! hle
    have heq : lowResidual p=0 := le_antisymm hle (lowResidual_nonneg p)
    have hz : forall I : Walsh4.Index, I.Nonempty -> I.card ≤ 2 -> walsh ballMeasure (cfg p) I=0 := by
      intro I hI hcard
      have h := component_le_lowResidual p I hI hcard
      rw [heq] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    obtain ⟨hoff,hn⟩ := low_zero_rigidity (cfg p) (((mem_compactConfigs p).mp hp.1).1) hz
    have hd := deviation_eq_zero p hoff hn
    have hh := hp.2
    change zeta ≤ deviation p at hh
    linarith
  obtain ⟨r0,hr0,hmin⟩ := hT.exists_forall_le'
    (continuousOn_lowResidual.mono Set.inter_subset_left) hpos
  refine ⟨r0,hr0,?_⟩
  intro p hp hr
  by_contra! hn
  have h := hmin p ⟨hp,hn⟩
  linarith

def ballVolume : Real := ballMeasure.real Set.univ

theorem ballVolume_pos : 0 < ballVolume := by
  have hp : 0 < ballMeasure Set.univ := by
    simpa [ballMeasure] using Metric.measure_closedBall_pos (volume : Measure E4) (0 : E4) (by norm_num : (0 : Real)<1)
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)

theorem large_offset_single (a : E4) (ha : norm a=1) (t : Real) (ht : 2 < |t|) :
    |∫ x, single a t x ∂ballMeasure|=ballVolume := by
  have hbound : ∀ᵐ x ∂ballMeasure, |inner Real x a| ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have hxnorm : norm x ≤ 1 := by simpa [Metric.mem_closedBall,dist_zero_right] using hx
    have h := abs_real_inner_le_norm x a
    rw [ha,mul_one] at h
    exact h.trans hxnorm
  rcases lt_or_ge t 0 with hneg | hpos
  · rw [abs_of_neg hneg] at ht
    have he : single a t =ᵐ[ballMeasure] (fun _ => (1 : Real)) := by
      filter_upwards [hbound] with x hx
      have h := abs_le.mp hx
      exact if_pos (by linarith)
    rw [integral_congr_ae he]
    simp [ballVolume,integral_const,smul_eq_mul,abs_of_nonneg ENNReal.toReal_nonneg]
  · rw [abs_of_nonneg hpos] at ht
    have he : single a t =ᵐ[ballMeasure] (fun _ => (-1 : Real)) := by
      filter_upwards [hbound] with x hx
      have h := abs_le.mp hx
      exact if_neg (by linarith)
    rw [integral_congr_ae he]
    simp [ballVolume,integral_const,smul_eq_mul,abs_of_nonneg ENNReal.toReal_nonneg]

theorem offsets_bounded_of_small_low (c : HyperplaneCfg) (hc : UnitCfg c) (b : Real)
    (hb : b < ballVolume)
    (hs : forall i, |walsh ballMeasure c {i}| ≤ b) : forall i, |c.offset i| ≤ 2 := by
  intro i
  by_contra! ht
  have he := large_offset_single (c.normal i) (hc i) (c.offset i) ht
  have h := hs i
  have hwalsh : walsh ballMeasure c {i} = ∫ x, single (c.normal i) (c.offset i) x ∂ballMeasure := by
    simp [walsh,Cells.signCharacter_eq_prod,single,closedSign,sub_nonneg]
  rw [hwalsh,he] at h
  linarith

end SoberonConvexBody.BallCompactness
