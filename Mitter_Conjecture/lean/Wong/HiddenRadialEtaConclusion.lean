import Wong.HiddenQuadraticBranchConstancy
import Wong.PureHiddenQuadraticEta
import Wong.ConstantWongRadialEta
import Wong.ConstantWongQuadraticEtaClosure

/-! Quadratic eta and observation affinity are derived from genuine Lie
words in the full-radial and whole pure-hidden branches. -/
noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

 theorem functionElementsAffine_of_full_radial_quadratic_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth fullRadialQuadraticPolynomial) ∈
      estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    FunctionElementsAffine (estimationAlgebra f h) := by
  obtain ⟨hW, _h02, _h12⟩ := full_radial_affine_wongConstant_and_mixed_zero
    f h hrank hx0 hx1 hq p hp
  obtain ⟨q, hqdeg, hqeta⟩ := quadratic_eta_of_constant_wong_full_radial_member
    f h hrank hW hq
  exact functionElementsAffine_of_constant_wong_quadratic_eta f h hW q hqdeg hqeta

 theorem functionElementsAffine_of_pure_hidden_square_whole_hessian_free {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hsquare : multiplication (hiddenShearTime * hiddenShearTime) ∈ estimationAlgebra f h)
    (hF : ∀ u : Smooth, multiplication u ∈ estimationAlgebra f h →
      ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 → partialDerivative i (partialDerivative j u) = 0)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    FunctionElementsAffine (estimationAlgebra f h) := by
  obtain ⟨hW, h02, h12⟩ := pure_hidden_square_affine_wongConstant_and_mixed_zero
    f h hrank hx0 hx1 hsquare hF p hp
  have hI := one_mem_estimationAlgebra_of_rank_two f h hrank
  have hword := hidden_coordinateEuler_eta_resolvent_mem f h hI hsquare h02 h12
  obtain ⟨q, hqdeg, hqeta⟩ := quadratic_eta_of_pure_hidden_function_hessians_and_euler_word
    f h hrank hx0 hx1 hW h02 h12 hF hword
  exact functionElementsAffine_of_constant_wong_quadratic_eta f h hW q hqdeg hqeta

end Wong.SmoothModel

#print axioms Wong.SmoothModel.functionElementsAffine_of_full_radial_quadratic_member
#print axioms Wong.SmoothModel.functionElementsAffine_of_pure_hidden_square_whole_hessian_free
