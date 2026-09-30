import Wong.PolynomialVisibleDerivativeBridge

/-! Exact visible derivatives retain affine degree bounds and hidden independence. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

theorem polynomialPartialEnd_pow_degree_le (i : Fin 3) (n : ℕ) (p : RealPoly) :
    ((polynomialPartialEnd i ^ n) p).totalDegree ≤ p.totalDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (Wong.PolynomialGradient.partial_totalDegree_le _ i).trans
      ((Nat.sub_le _ _).trans ih)

theorem visiblePolynomialDerivative_degree_le (a b : ℕ) (p : RealPoly) :
    (visiblePolynomialDerivative a b p).totalDegree ≤ p.totalDegree :=
  (polynomialPartialEnd_pow_degree_le 0 a _).trans
    (polynomialPartialEnd_pow_degree_le 1 b p)

theorem polynomial_partial_commute_pow (i j : Fin 3) (n : ℕ) (p : RealPoly) :
    pderiv i ((polynomialPartialEnd j ^ n) p) =
      (polynomialPartialEnd j ^ n) (pderiv i p) := by
  exact congrArg (fun T : Module.End ℝ RealPoly => T p)
    ((polynomialPartialEnd_commute i j).pow_right n).eq

theorem visiblePolynomialDerivative_hidden_partial_zero
    (a b : ℕ) (p : RealPoly) (hp : pderiv 2 p = 0) :
    pderiv 2 (visiblePolynomialDerivative a b p) = 0 := by
  unfold visiblePolynomialDerivative
  rw [polynomial_partial_commute_pow, polynomial_partial_commute_pow, hp]
  simp

theorem visiblePolynomialDerivative_actual_hidden_partial_zero
    (a b : ℕ) (p : RealPoly)
    (hp : partialDerivative 2 (polynomialSmooth p) = 0) :
    partialDerivative 2 (polynomialSmooth (visiblePolynomialDerivative a b p)) = 0 := by
  have hz : pderiv 2 p = 0 := polynomialSmooth_injective (by
    rw [← partialDerivative_polynomialSmooth, hp, polynomialSmooth_zero])
  rw [partialDerivative_polynomialSmooth,
    visiblePolynomialDerivative_hidden_partial_zero a b p hz, polynomialSmooth_zero]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visiblePolynomialDerivative_actual_hidden_partial_zero
