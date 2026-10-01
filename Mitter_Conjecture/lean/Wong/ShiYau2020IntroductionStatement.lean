import Wong.ShiYau2020ModelReduction

/-! The introduction's Theorem1.1 states only Wong constancy, whereas the
body's Theorem3.7 additionally states observation affinity. The latter is
represented by ShiYau2020QuadraticClaim; its stronger conclusion implies
this separate literal introduction statement. -/
noncomputable section
namespace Wong.SmoothModel

/-- Literal Wong-only Theorem1.1 in the supplied2020 introduction. -/
def ShiYau2020WongQuadraticClaim : Prop :=
  ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    (∃ p : RealPoly, p.totalDegree = 2 ∧
      multiplication (polynomialSmooth p) ∈ estimationAlgebra f h) →
    WongConstant f

end Wong.SmoothModel
