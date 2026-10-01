import Wong.SmoothCoordinateEuler
import Wong.SmoothPolynomialRegularity

/-! Proved global Euler resolvent regularity, including the origin. No
growth hypothesis or division by a coordinate is used. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem coordinateEuler_shift_product_partial
    (s : Finset (Fin 3)) (i : Fin 3) (a b : ℝ) (u : Smooth) :
    partialDerivative i ((coordinateEuler s + a • (1 : Operator))
      ((coordinateEuler s + b • (1 : Operator)) u)) =
    (coordinateEuler s + (a + if i ∈ s then 1 else 0) • (1 : Operator))
      ((coordinateEuler s + (b + if i ∈ s then 1 else 0) • (1 : Operator))
        (partialDerivative i u)) := by
  rw [partialDerivative_coordinateEuler_shift, partialDerivative_coordinateEuler_shift]

theorem euler_resolvent_selected_third_partial_zero
    (s : Finset (Fin 3)) (u : Smooth) (p : RealPoly) (hp : p.totalDegree ≤ 2)
    (he : (coordinateEuler s + (0 : ℝ) • (1 : Operator))
      ((coordinateEuler s + (2 : ℝ) • (1 : Operator)) u) = polynomialSmooth p)
    (i j k : Fin 3) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    partialDerivative i (partialDerivative j (partialDerivative k u)) = 0 := by
  have hh := congrArg (fun v : Smooth =>
    partialDerivative i (partialDerivative j (partialDerivative k v))) he
  rw [smooth_polynomial_third_partials_zero p hp i j k] at hh
  simp only [coordinateEuler_shift_product_partial, hi, hj, hk, if_true] at hh
  norm_num only at hh
  have hinner := positive_coordinateEuler_shift_kernel s 3 (by norm_num)
    ((coordinateEuler s + (5 : ℝ) • (1 : Operator))
      (partialDerivative i (partialDerivative j (partialDerivative k u)))) hh
  exact positive_coordinateEuler_shift_kernel s 5 (by norm_num) _ hinner

theorem euler_resolvent_mixed_partial_zero
    (s : Finset (Fin 3)) (u : Smooth) (i j : Fin 3) (hi : i ∈ s) (hj : j ∉ s)
    (hu : partialDerivative i (partialDerivative j
      ((coordinateEuler s + (0 : ℝ) • (1 : Operator))
        ((coordinateEuler s + (2 : ℝ) • (1 : Operator)) u))) = 0) :
    partialDerivative i (partialDerivative j u) = 0 := by
  simp only [coordinateEuler_shift_product_partial, hi, hj, if_true, if_false] at hu
  norm_num only at hu
  have hinner := positive_coordinateEuler_shift_kernel s 1 (by norm_num)
    ((coordinateEuler s + (3 : ℝ) • (1 : Operator))
      (partialDerivative i (partialDerivative j u))) hu
  exact positive_coordinateEuler_shift_kernel s 3 (by norm_num) _ hinner

theorem smooth_quadratic_of_fullEuler_resolvent_polynomial (u : Smooth)
    (p : RealPoly) (hp : p.totalDegree ≤ 2)
    (he : (coordinateEuler Finset.univ + (0 : ℝ) • (1 : Operator))
      ((coordinateEuler Finset.univ + (2 : ℝ) • (1 : Operator)) u) =
      polynomialSmooth p) :
    ∃ q : RealPoly, q.totalDegree ≤ 2 ∧ polynomialSmooth q = u := by
  apply smooth_quadratic_of_third_partials_zero
  intro i j k
  have hh := congrArg (fun v : Smooth =>
    partialDerivative i (partialDerivative j (partialDerivative k v))) he
  rw [smooth_polynomial_third_partials_zero p hp i j k] at hh
  simp only [coordinateEuler_shift_product_partial, Finset.mem_univ, if_true] at hh
  norm_num only at hh
  have hinner := positive_coordinateEuler_shift_kernel Finset.univ 3 (by norm_num)
    ((coordinateEuler Finset.univ + (5 : ℝ) • (1 : Operator))
      (partialDerivative i (partialDerivative j (partialDerivative k u)))) hh
  exact positive_coordinateEuler_shift_kernel Finset.univ 5 (by norm_num) _ hinner

end Wong.SmoothModel

#print axioms Wong.SmoothModel.smooth_quadratic_of_fullEuler_resolvent_polynomial
