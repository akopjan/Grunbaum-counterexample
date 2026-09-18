import SoberonConvexBody.TensorMultilinear

/-!
# Exact finite parity extraction

The five identities below are identities of polynomials before integration.
They isolate the fully mixed tensor coefficients. No orthonormality or
measure-theoretic hypothesis is needed for these algebraic identities.
-/

noncomputable section
namespace SoberonConvexBody.Tensors

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def twoSigns (f : Real -> Real) : Real := f 1 + f (-1)

def signAverage4 (f : Real -> Real -> Real -> Real -> Real) : Real :=
  (1 / 16 : Real) * twoSigns (fun a => twoSigns (fun b =>
    twoSigns (fun c => twoSigns (fun d => f a b c d))))

def linearCombination4 (q : Fin 4 -> E4) (a b c d : Real) : E4 :=
  a • q 0 + b • q 1 + c • q 2 + d • q 3

def tensorPolynomial (tau : Real) (x : E4) : Real :=
  A tau x x x + B x x x x

/-- Parity extraction for the coordinate set 123. -/
theorem signAverage4_high123 (tau : Real) (q : Fin 4 -> E4)
    (a b c d : Real) :
    signAverage4 (fun s0 s1 s2 s3 =>
      (s1 * s2 * s3) * tensorPolynomial tau
        (linearCombination4 q (s0 * a) (s1 * b) (s2 * c) (s3 * d))) =
      6 * (b * c * d) * A tau (q 1) (q 2) (q 3) := by
  simp (config := { maxSteps := 1000000 }) only [
    signAverage4, twoSigns, tensorPolynomial, linearCombination4, A_add_1,
    A_add_2, A_add_3, A_smul_1, A_smul_2, A_smul_3,
    A_swap_12, A_swap_23, B_add_1, B_add_2, B_add_3,
    B_add_4, B_smul_1, B_smul_2, B_smul_3, B_smul_4,
    B_swap_12, B_swap_23, B_swap_34]
  ring

/-- Parity extraction for the coordinate set 023. -/
theorem signAverage4_high023 (tau : Real) (q : Fin 4 -> E4)
    (a b c d : Real) :
    signAverage4 (fun s0 s1 s2 s3 =>
      (s0 * s2 * s3) * tensorPolynomial tau
        (linearCombination4 q (s0 * a) (s1 * b) (s2 * c) (s3 * d))) =
      6 * (a * c * d) * A tau (q 0) (q 2) (q 3) := by
  simp (config := { maxSteps := 1000000 }) only [
    signAverage4, twoSigns, tensorPolynomial, linearCombination4, A_add_1,
    A_add_2, A_add_3, A_smul_1, A_smul_2, A_smul_3,
    A_swap_12, A_swap_23, B_add_1, B_add_2, B_add_3,
    B_add_4, B_smul_1, B_smul_2, B_smul_3, B_smul_4,
    B_swap_12, B_swap_23, B_swap_34]
  ring

/-- Parity extraction for the coordinate set 013. -/
theorem signAverage4_high013 (tau : Real) (q : Fin 4 -> E4)
    (a b c d : Real) :
    signAverage4 (fun s0 s1 s2 s3 =>
      (s0 * s1 * s3) * tensorPolynomial tau
        (linearCombination4 q (s0 * a) (s1 * b) (s2 * c) (s3 * d))) =
      6 * (a * b * d) * A tau (q 0) (q 1) (q 3) := by
  simp (config := { maxSteps := 1000000 }) only [
    signAverage4, twoSigns, tensorPolynomial, linearCombination4, A_add_1,
    A_add_2, A_add_3, A_smul_1, A_smul_2, A_smul_3,
    A_swap_12, A_swap_23, B_add_1, B_add_2, B_add_3,
    B_add_4, B_smul_1, B_smul_2, B_smul_3, B_smul_4,
    B_swap_12, B_swap_23, B_swap_34]
  ring

/-- Parity extraction for the coordinate set 012. -/
theorem signAverage4_high012 (tau : Real) (q : Fin 4 -> E4)
    (a b c d : Real) :
    signAverage4 (fun s0 s1 s2 s3 =>
      (s0 * s1 * s2) * tensorPolynomial tau
        (linearCombination4 q (s0 * a) (s1 * b) (s2 * c) (s3 * d))) =
      6 * (a * b * c) * A tau (q 0) (q 1) (q 2) := by
  simp (config := { maxSteps := 1000000 }) only [
    signAverage4, twoSigns, tensorPolynomial, linearCombination4, A_add_1,
    A_add_2, A_add_3, A_smul_1, A_smul_2, A_smul_3,
    A_swap_12, A_swap_23, B_add_1, B_add_2, B_add_3,
    B_add_4, B_smul_1, B_smul_2, B_smul_3, B_smul_4,
    B_swap_12, B_swap_23, B_swap_34]
  ring

/-- Parity extraction for the coordinate set 0123. -/
theorem signAverage4_high0123 (tau : Real) (q : Fin 4 -> E4)
    (a b c d : Real) :
    signAverage4 (fun s0 s1 s2 s3 =>
      (s0 * s1 * s2 * s3) * tensorPolynomial tau
        (linearCombination4 q (s0 * a) (s1 * b) (s2 * c) (s3 * d))) =
      24 * (a * b * c * d) * B (q 0) (q 1) (q 2) (q 3) := by
  simp (config := { maxSteps := 1000000 }) only [
    signAverage4, twoSigns, tensorPolynomial, linearCombination4, A_add_1,
    A_add_2, A_add_3, A_smul_1, A_smul_2, A_smul_3,
    A_swap_12, A_swap_23, B_add_1, B_add_2, B_add_3,
    B_add_4, B_smul_1, B_smul_2, B_smul_3, B_smul_4,
    B_swap_12, B_swap_23, B_swap_34]
  ring

end SoberonConvexBody.Tensors
