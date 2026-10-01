import Wong.ConstantWongClosureActual
import Wong.GlobalRiccatiMomentAnalysis

/-! The actual Riccati estimate and actual finite operator closure discharge
all observation and eta derivative hypotheses for a constant-Wong model. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

theorem functionElementsAffine_of_constant_wong_quadratic_eta {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hW : WongConstant f) (Q : RealPoly) (hQ : Q.totalDegree ≤ 2)
    (heta : polynomialSmooth Q = eta f h) :
    FunctionElementsAffine (estimationAlgebra f h) := by
  apply constant_wong_polynomial_eta_functionElementsAffine f h hW
  · intro i
    refine ⟨pderiv i Q, ?_, ?_⟩
    · exact (Wong.PolynomialGradient.partial_totalDegree_le Q i).trans (by omega)
    · rw [← partialDerivative_polynomialSmooth, heta]
  · exact observations_affine_of_quadratic_eta f h Q hQ heta

end Wong.SmoothModel

#print axioms Wong.SmoothModel.functionElementsAffine_of_constant_wong_quadratic_eta
