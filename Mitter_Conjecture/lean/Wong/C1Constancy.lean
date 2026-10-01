import Wong.VisibleWongQuadraticAnalysis
import Wong.HiddenIndependentSectors

/-! The complete C1 constancy implication uses the actual visible radial
member and the whole hidden-independent function space. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

theorem c1_wongConstant_of_actual_affine_shape {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
      estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    WongConstant f := by
  have hw : wong f 0 1 = polynomialSmooth (C p.b₀ + C p.b₁ * X 0 + C p.b₂ * X 1) := by
    apply Subtype.ext
    funext x
    rw [hp]
    simp [polynomialSmooth, Wong.AffineParameters.matrix, Wong.AffineParameters.w12]
    ring
  obtain ⟨hb1, hb2⟩ := visible_affine_wong_slopes_zero_of_radial_quadratic
    f h hrank hx0 hx1 hq p.b₀ p.b₁ p.b₂ hw
  exact HiddenIndependent.affine_wongConstant_of_hiddenIndependent
    f h hrank hHF hx0 hx1 p hp hb1 hb2

end Wong.SmoothModel

#print axioms Wong.SmoothModel.c1_wongConstant_of_actual_affine_shape
