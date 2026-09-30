import Wong.FunctionQuadraticRankConstraints
import Wong.QuadraticFunctionWongConstraints

/-! Intrinsic rank-two function-element curvature constraints. These statements
retain all original smooth operators and assume no quadratic-freeness. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem function_element_hidden_partial_affine_hidden {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h) :
    ∃ g k : ℝ, partialDerivative 2 u = g • smoothOne +
      k • linearFunction (coordinateVector 2) := by
  obtain ⟨g, a, ha⟩ := function_element_partial_affine f h u hu 2
  obtain ⟨h₀, h₁⟩ := function_element_visible_hidden_mixed_partials f h hrank hx₀ hx₁ u hu
  have hcoef (i : Fin 3) (hi : partialDerivative 2 (partialDerivative i u) = 0) : a i = 0 := by
    rw [partialDerivative_commute_apply 2 i, ha, map_add, partialDerivative_const,
      partialDerivative_linearFunction, zero_add] at hi
    simpa [smoothOne] using congrArg (fun v : Smooth => v.1 (0 : State)) hi
  have ha₀ := hcoef 0 h₀
  have ha₁ := hcoef 1 h₁
  refine ⟨g, a 2, ?_⟩
  rw [ha]
  apply Subtype.ext
  funext x
  simp [linearFunction, coordinateVector, Fin.sum_univ_three, ha₀, ha₁]

theorem function_curvature_gradient_mem_of_adapted_rank_two {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h)
    (i : Fin 3) (hi : i = 0 ∨ i = 1) :
    multiplication (functionCurvatureGradient f u i) ∈ estimationAlgebra f h := by
  obtain ⟨c, a, ha⟩ := function_element_partial_affine f h u hu i
  have hxi : multiplication (linearFunction (coordinateVector i)) ∈ estimationAlgebra f h := by
    rcases hi with rfl | rfl
    · exact hx₀
    · exact hx₁
  have hz := function_element_hidden_visible_mixed_zero f h hrank hx₀ hx₁ u hu i hxi
  rw [ha, map_add, partialDerivative_const, partialDerivative_linearFunction, zero_add] at hz
  have ha₂ : a 2 = 0 := by
    simpa [smoothOne] using congrArg (fun v : Smooth => v.1 (0 : State)) hz
  apply function_curvature_gradient_mem_of_visible_hessian_row
    f h hx₀ hx₁ u hu i hi a _ ha₂
  intro j
  rw [partialDerivative_commute_apply i j, ha, map_add, partialDerivative_const,
    partialDerivative_linearFunction, zero_add]

theorem function_curvature_gradient_degree_le_two_of_rank_two {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h)
    (i : Fin 3) (hi : i = 0 ∨ i = 1) :
    ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = functionCurvatureGradient f u i :=
  function_element_polynomial_degree_le_two f h _
    (function_curvature_gradient_mem_of_adapted_rank_two f h hrank hx₀ hx₁ u hu i hi)

end Wong.SmoothModel

#print axioms Wong.SmoothModel.function_element_hidden_partial_affine_hidden
#print axioms Wong.SmoothModel.function_curvature_gradient_mem_of_adapted_rank_two
