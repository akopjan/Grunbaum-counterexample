import SoberonConvexBody.TensorDefs

/-!
# Multilinearity and symmetry of the concrete tensors

All identities are proved from the displayed coordinate formulas.
-/

noncomputable section
namespace SoberonConvexBody.Tensors

theorem A_add_1 (tau : Real) (x y z v : E4) :
    A tau (x + v) y z = A tau x y z + A tau v y z := by
  simp only [A, A0, C, mForm, PiLp.add_apply]
  ring

theorem A_smul_1 (tau : Real) (a : Real) (x y z : E4) :
    A tau (a • x) y z = a * A tau x y z := by
  simp only [A, A0, C, mForm, PiLp.smul_apply, smul_eq_mul]
  ring

theorem A_add_2 (tau : Real) (x y z v : E4) :
    A tau x (y + v) z = A tau x y z + A tau x v z := by
  simp only [A, A0, C, mForm, PiLp.add_apply]
  ring

theorem A_smul_2 (tau : Real) (a : Real) (x y z : E4) :
    A tau x (a • y) z = a * A tau x y z := by
  simp only [A, A0, C, mForm, PiLp.smul_apply, smul_eq_mul]
  ring

theorem A_add_3 (tau : Real) (x y z v : E4) :
    A tau x y (z + v) = A tau x y z + A tau x y v := by
  simp only [A, A0, C, mForm, PiLp.add_apply]
  ring

theorem A_smul_3 (tau : Real) (a : Real) (x y z : E4) :
    A tau x y (a • z) = a * A tau x y z := by
  simp only [A, A0, C, mForm, PiLp.smul_apply, smul_eq_mul]
  ring

theorem A_swap_12 (tau : Real) (x y z : E4) :
    A tau x y z = A tau y x z := by
  unfold A A0 C mForm
  ring

theorem A_swap_23 (tau : Real) (x y z : E4) :
    A tau x y z = A tau x z y := by
  unfold A A0 C mForm
  ring

theorem B_add_1 (w x y z v : E4) :
    B (w + v) x y z = B w x y z + B v x y z := by
  simp only [B, nForm, mForm, PiLp.add_apply]
  ring

theorem B_smul_1 (a : Real) (w x y z : E4) :
    B (a • w) x y z = a * B w x y z := by
  simp only [B, nForm, mForm, PiLp.smul_apply, smul_eq_mul]
  ring

theorem B_add_2 (w x y z v : E4) :
    B w (x + v) y z = B w x y z + B w v y z := by
  simp only [B, nForm, mForm, PiLp.add_apply]
  ring

theorem B_smul_2 (a : Real) (w x y z : E4) :
    B w (a • x) y z = a * B w x y z := by
  simp only [B, nForm, mForm, PiLp.smul_apply, smul_eq_mul]
  ring

theorem B_add_3 (w x y z v : E4) :
    B w x (y + v) z = B w x y z + B w x v z := by
  simp only [B, nForm, mForm, PiLp.add_apply]
  ring

theorem B_smul_3 (a : Real) (w x y z : E4) :
    B w x (a • y) z = a * B w x y z := by
  simp only [B, nForm, mForm, PiLp.smul_apply, smul_eq_mul]
  ring

theorem B_add_4 (w x y z v : E4) :
    B w x y (z + v) = B w x y z + B w x y v := by
  simp only [B, nForm, mForm, PiLp.add_apply]
  ring

theorem B_smul_4 (a : Real) (w x y z : E4) :
    B w x y (a • z) = a * B w x y z := by
  simp only [B, nForm, mForm, PiLp.smul_apply, smul_eq_mul]
  ring

theorem B_swap_12 (w x y z : E4) :
    B w x y z = B x w y z := by
  unfold B nForm mForm
  ring

theorem B_swap_23 (w x y z : E4) :
    B w x y z = B w y x z := by
  unfold B nForm mForm
  ring

theorem B_swap_34 (w x y z : E4) :
    B w x y z = B w x z y := by
  unfold B nForm mForm
  ring

end SoberonConvexBody.Tensors
