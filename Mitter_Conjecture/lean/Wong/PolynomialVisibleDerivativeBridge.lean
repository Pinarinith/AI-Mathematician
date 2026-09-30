import Wong.PolynomialVisibleExtraction

/-! The visible polynomial derivatives are genuine iterated partial derivatives
of the actual globally smooth evaluation, including every lower-degree term. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem polynomialSmooth_polynomialPartialEnd_pow (i : Fin 3) (n : ℕ) (p : RealPoly) :
    polynomialSmooth ((polynomialPartialEnd i ^ n) p) =
      (partialDerivative i ^ n) (polynomialSmooth p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rw [show polynomialPartialEnd i p = MvPolynomial.pderiv i p from rfl,
      ← partialDerivative_polynomialSmooth]

theorem polynomialSmooth_visiblePolynomialDerivative (a b : ℕ) (p : RealPoly) :
    polynomialSmooth (visiblePolynomialDerivative a b p) =
      (partialDerivative 0 ^ a) ((partialDerivative 1 ^ b) (polynomialSmooth p)) := by
  unfold visiblePolynomialDerivative
  rw [polynomialSmooth_polynomialPartialEnd_pow, polynomialSmooth_polynomialPartialEnd_pow]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.polynomialSmooth_visiblePolynomialDerivative
