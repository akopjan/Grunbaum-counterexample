import Mathlib

/-!
# Uniform scalar estimate for the positive root of a quadratic

This elementary calculation supplies the quadratic error for affine images
of a ball. It does not use an implicit-function or differentiation theorem.
-/
noncomputable section
namespace SoberonConvexBody.EllipsoidScalar

 def positiveRoot (a b c : Real) : Real :=
  (Real.sqrt (b^2 + a*(1-c)) - b) / a

 theorem sqrt_discriminant_gt_abs (a b c : Real) (ha : 0 < a) (hc : c < 1) :
    |b| < Real.sqrt (b^2+a*(1-c)) := by
  have hp : 0 < a*(1-c) := mul_pos ha (by linarith)
  have hdisc : 0 ≤ b^2+a*(1-c) := by positivity
  have hsq := Real.sq_sqrt hdisc
  have hn := Real.sqrt_nonneg (b^2+a*(1-c))
  have hb := sq_abs b
  nlinarith [abs_nonneg b]

 theorem positiveRoot_pos (a b c : Real) (ha : 0 < a) (hc : c < 1) :
    0 < positiveRoot a b c := by
  have h := sqrt_discriminant_gt_abs a b c ha hc
  have hb := le_abs_self b
  exact div_pos (by linarith) ha

 theorem positiveRoot_equation (a b c : Real) (ha : 0 < a) (hc : c < 1) :
    a * positiveRoot a b c ^ 2 + 2*b*positiveRoot a b c+c=1 := by
  have hdisc : 0 ≤ b^2+a*(1-c) := by
    have hp : 0 < a*(1-c) := mul_pos ha (by linarith)
    positivity
  have hs := Real.sq_sqrt hdisc
  have hm : a * positiveRoot a b c + b = Real.sqrt (b^2+a*(1-c)) := by
    unfold positiveRoot
    field_simp [ha.ne']
    ring
  have hs' : (a * positiveRoot a b c + b)^2 = b^2+a*(1-c) := by
    rw [hm]
    exact hs
  have hp : a * (a * positiveRoot a b c ^ 2 + 2*b*positiveRoot a b c+c-1) = 0 := by
    nlinarith [hs']
  have hz := (mul_eq_zero.mp hp).resolve_left ha.ne'
  linarith

 theorem quadratic_le_iff (a b c r : Real) (ha : 0 < a) (hc : c < 1)
    (hr : 0 ≤ r) :
    a*r^2+2*b*r+c ≤ 1 ↔ r ≤ positiveRoot a b c := by
  let rho := positiveRoot a b c
  have heq := positiveRoot_equation a b c ha hc
  change a*rho^2+2*b*rho+c=1 at heq
  have hs : a*rho+b=Real.sqrt (b^2+a*(1-c)) := by
    dsimp [rho,positiveRoot]
    field_simp [ha.ne']
    ring
  have hdisc := sqrt_discriminant_gt_abs a b c ha hc
  have hb := neg_abs_le b
  have hfac : 0 < a*r+a*rho+2*b := by
    have hmul := mul_nonneg (le_of_lt ha) hr
    nlinarith
  have hfactor : a*r^2+2*b*r+c-1 = (r-rho)*(a*r+a*rho+2*b) := by
    nlinarith [heq]
  constructor
  · intro h
    by_contra hn
    have hp : 0 < (r-rho)*(a*r+a*rho+2*b) :=
      mul_pos (by linarith) hfac
    linarith
  · intro h
    have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (le_of_lt hfac)
    linarith

 theorem root_bounds (a b c d : Real) (hd : 0 ≤ d) (hsmall : d ≤ 1/100)
    (ha : |a-1| ≤ d) (hb : |b| ≤ d) (hc0 : 0 ≤ c) (hc : c ≤ d^2) :
    1/2 ≤ positiveRoot a b c ∧ positiveRoot a b c ≤ 2 := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hdsq : d^2 ≤ 1/10000 := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsmall)]
  have hap : 0 < a := by linarith
  have hclt : c < 1 := by linarith
  constructor
  · apply (quadratic_le_iff a b c (1/2) hap hclt (by norm_num)).mp
    nlinarith
  · have hnot : ¬ 2 ≤ positiveRoot a b c := by
      intro h
      have he := (quadratic_le_iff a b c 2 hap hclt (by norm_num)).mpr h
      nlinarith
    exact le_of_lt (lt_of_not_ge hnot)

 theorem root_sq_error (a b c d : Real) (hd : 0 ≤ d) (hsmall : d ≤ 1/100)
    (ha : |a-1| ≤ d) (hb : |b| ≤ d) (hc0 : 0 ≤ c) (hc : c ≤ d^2) :
    |positiveRoot a b c ^ 2 - 1| ≤ 9*d ∧
      |positiveRoot a b c - 1| ≤ 9*d := by
  let rho := positiveRoot a b c
  obtain ⟨hrlo, hrhi⟩ := root_bounds a b c d hd hsmall ha hb hc0 hc
  change 1/2 ≤ rho at hrlo
  change rho ≤ 2 at hrhi
  have hr0 : 0 ≤ rho := by linarith
  have hr2 : rho^2 ≤ 4 := by nlinarith
  have ha' := abs_le.mp ha
  have hdsq : d^2 ≤ d := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsmall)]
  have heq := positiveRoot_equation a b c (by linarith : 0 < a) (by linarith : c < 1)
  change a*rho^2+2*b*rho+c=1 at heq
  have hid : rho^2-1 = -(a-1)*rho^2 - 2*b*rho-c := by nlinarith
  have hterm1 : |-(a-1)*rho^2| ≤ 4*d := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg rho)]
    have h := mul_le_mul ha hr2 (sq_nonneg rho) hd
    nlinarith
  have hterm2 : |2*b*rho| ≤ 4*d := by
    rw [abs_mul, abs_mul, abs_of_nonneg hr0]
    norm_num
    have h := mul_le_mul hb hrhi hr0 hd
    nlinarith
  have hx : |rho^2-1| ≤ 9*d := by
    have h1 := abs_le.mp hterm1
    have h2 := abs_le.mp hterm2
    rw [hid, abs_le]
    constructor <;> linarith [h1, h2, hc0, hc, hdsq]
  refine ⟨hx, ?_⟩
  have hid2 : rho^2-1 = (rho-1)*(rho+1) := by ring
  have hmul : |rho-1| ≤ |rho-1| * (rho+1) := by
    nlinarith [mul_nonneg (abs_nonneg (rho-1)) hr0]
  have heabs : |rho^2-1| = |rho-1| * (rho+1) := by
    rw [hid2, abs_mul, abs_of_nonneg (by linarith : 0 ≤ rho+1)]
  linarith [hmul, heabs, hx]

 theorem fourth_power_expansion (a b c d : Real) (hd : 0 ≤ d) (hsmall : d ≤ 1/100)
    (ha : |a-1| ≤ d) (hb : |b| ≤ d) (hc0 : 0 ≤ c) (hc : c ≤ d^2) :
    |positiveRoot a b c ^ 4 - (3-2*a-4*b)| ≤ 200*d^2 := by
  let rho := positiveRoot a b c
  obtain ⟨hx, hs⟩ := root_sq_error a b c d hd hsmall ha hb hc0 hc
  change |rho^2-1| ≤ 9*d at hx
  change |rho-1| ≤ 9*d at hs
  have ha' := abs_le.mp ha
  have hdsq : d^2 ≤ d := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsmall)]
  have heq := positiveRoot_equation a b c (by linarith : 0 < a) (by linarith : c < 1)
  change a*rho^2+2*b*rho+c=1 at heq
  have hid : rho^4-(3-2*a-4*b) =
      (rho^2-1)^2 - 2*(a-1)*(rho^2-1) - 4*b*(rho-1) - 2*c := by
    nlinarith [heq]
  have hx2 : (rho^2-1)^2 ≤ 81*d^2 := by
    have hh := mul_le_mul hx hx (abs_nonneg _) (by positivity : 0 ≤ 9*d)
    rw [← pow_two, sq_abs] at hh
    nlinarith
  have hax : |2*(a-1)*(rho^2-1)| ≤ 18*d^2 := by
    have hh := mul_le_mul ha hx (abs_nonneg _) hd
    rw [abs_mul, abs_mul]
    norm_num
    nlinarith
  have hbs : |4*b*(rho-1)| ≤ 36*d^2 := by
    have hh := mul_le_mul hb hs (abs_nonneg _) hd
    rw [abs_mul, abs_mul]
    norm_num
    nlinarith
  have h1 := abs_le.mp hax
  have h2 := abs_le.mp hbs
  rw [hid, abs_le]
  have hx2_nonneg : 0 ≤ (rho^2-1)^2 := sq_nonneg _
  constructor <;> linarith [hx2, hx2_nonneg, h1, h2, hc0, hc]

end SoberonConvexBody.EllipsoidScalar
