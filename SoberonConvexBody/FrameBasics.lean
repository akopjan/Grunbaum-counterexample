import SoberonConvexBody.TensorParity

noncomputable section
namespace SoberonConvexBody
open scoped BigOperators

namespace Tensors

theorem IsONFrame.orthonormal {q : Fin 4 -> E4} (hq : IsONFrame q) :
    Orthonormal Real q := by
  constructor
  · exact hq.norm_eq_one
  · intro i j hij
    simpa [hij] using hq i j

/-- The given four vectors form an orthonormal basis, not merely a family. -/
def IsONFrame.toONBasis {q : Fin 4 -> E4} (hq : IsONFrame q) :
    OrthonormalBasis (Fin 4) Real E4 :=
  let b := basisOfOrthonormalOfCardEqFinrank hq.orthonormal (by simp [E4])
  b.toOrthonormalBasis (by
    simpa [b, coe_basisOfOrthonormalOfCardEqFinrank] using hq.orthonormal)

@[simp] theorem IsONFrame.toONBasis_apply {q : Fin 4 -> E4}
    (hq : IsONFrame q) (i : Fin 4) : hq.toONBasis i = q i := by
  simp [IsONFrame.toONBasis]

/-- Coordinates to ambient space. -/
def IsONFrame.toIsometry {q : Fin 4 -> E4} (hq : IsONFrame q) :
    E4 ≃ₗᵢ[Real] E4 := hq.toONBasis.repr.symm

theorem IsONFrame.toIsometry_apply {q : Fin 4 -> E4}
    (hq : IsONFrame q) (x : E4) :
    hq.toIsometry x = linearCombination4 q (x 0) (x 1) (x 2) (x 3) := by
  have h := hq.toONBasis.sum_repr_symm x
  simpa [IsONFrame.toIsometry, linearCombination4, Fin.sum_univ_succ,
    add_assoc] using h.symm

theorem IsONFrame.inner_toIsometry {q : Fin 4 -> E4}
    (hq : IsONFrame q) (x : E4) (i : Fin 4) :
    inner Real (hq.toIsometry x) (q i) = x i := by
  have h := hq.toONBasis.repr_apply_apply (hq.toIsometry x) i
  have hh : x i = inner Real (q i) (hq.toIsometry x) := by
    simpa [IsONFrame.toIsometry] using h
  simpa only [real_inner_comm] using hh.symm

end Tensors

end SoberonConvexBody
