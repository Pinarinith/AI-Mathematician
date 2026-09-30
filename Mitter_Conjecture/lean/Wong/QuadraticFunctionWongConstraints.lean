import Wong.CovariantWords
import Wong.RankStructure

/-!
# Curvature constraints from genuine quadratic function elements

The hypotheses below describe a constant visible Hessian row of a function
element. They do not assume quadratic-freeness or Wong affinity. The actual
double bracket leaves a genuine multiplication operator after subtracting
the admitted visible covariant derivatives. This is the operator step used
in Shi--Yau 2017, equations (3.6)--(3.7), without dropping scalar remainders.
-/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

def functionCurvatureGradient (f : Fin 3 → Smooth) (u : Smooth) (i : Fin 3) : Smooth :=
  ∑ j, smoothMul (partialDerivative j u) (wong f j i)

theorem visible_hessian_row_laplacian_derivative_zero
    (u : Smooth) (i : Fin 3) (H : Fin 3 → ℝ)
    (hH : ∀ j, partialDerivative i (partialDerivative j u) = H j • smoothOne) :
    partialDerivative i (∑ j, partialDerivative j (partialDerivative j u)) = 0 := by
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [partialDerivative_commute_apply i j, hH j, partialDerivative_const]

theorem lie_D_L0_function_of_constant_hessian_row {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (u : Smooth) (i : Fin 3) (H : Fin 3 → ℝ)
    (hH : ∀ j, partialDerivative i (partialDerivative j u) = H j • smoothOne) :
    ⁅D f i, ⁅L0 f h, multiplication u⁆⁆ =
      (∑ j, H j • D f j) + multiplication (functionCurvatureGradient f u i) := by
  have he : ⁅L0 f h, multiplication u⁆ =
      firstOrder f (fun j => partialDerivative j u)
        ((1 / 2 : ℝ) • (∑ j, partialDerivative j (partialDerivative j u))) := by
    rw [lie_L0_multiplication]
    simp only [firstOrder, multiplication_smul]
  rw [he, lie_D_firstOrder]
  have hz := visible_hessian_row_laplacian_derivative_zero u i H hH
  simp only [map_smul, hz, smul_zero, zero_add, firstOrder, hH,
    multiplication_smul, multiplication_smoothOne, smul_mul_assoc, one_mul,
    functionCurvatureGradient]

theorem function_curvature_gradient_mem_of_visible_hessian_row {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h)
    (i : Fin 3) (hi : i = 0 ∨ i = 1) (H : Fin 3 → ℝ)
    (hH : ∀ j, partialDerivative i (partialDerivative j u) = H j • smoothOne)
    (hhidden : H 2 = 0) :
    multiplication (functionCurvatureGradient f u i) ∈ estimationAlgebra f h := by
  have hD₀ := D_mem_of_coordinate_mem f h 0 hx₀
  have hD₁ := D_mem_of_coordinate_mem f h 1 hx₁
  have hDi : D f i ∈ estimationAlgebra f h := by
    rcases hi with rfl | rfl
    · exact hD₀
    · exact hD₁
  have hL : L0 f h ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hB := (estimationAlgebra f h).lie_mem hDi
    ((estimationAlgebra f h).lie_mem hL hu)
  rw [lie_D_L0_function_of_constant_hessian_row f h u i H hH] at hB
  have hsum : (∑ j, H j • D f j) ∈ estimationAlgebra f h := by
    rw [Fin.sum_univ_three, hhidden, zero_smul, add_zero]
    exact (estimationAlgebra f h).add_mem
      ((estimationAlgebra f h).smul_mem _ hD₀)
      ((estimationAlgebra f h).smul_mem _ hD₁)
  simpa only [add_sub_cancel_left] using (estimationAlgebra f h).sub_mem hB hsum

theorem function_curvature_gradient_degree_le_two {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h)
    (i : Fin 3) (hi : i = 0 ∨ i = 1) (H : Fin 3 → ℝ)
    (hH : ∀ j, partialDerivative i (partialDerivative j u) = H j • smoothOne)
    (hhidden : H 2 = 0) :
    ∃ p : RealPoly, p.totalDegree ≤ 2 ∧
      polynomialSmooth p = functionCurvatureGradient f u i :=
  function_element_polynomial_degree_le_two f h _
    (function_curvature_gradient_mem_of_visible_hessian_row
      f h hx₀ hx₁ u hu i hi H hH hhidden)

end Wong.SmoothModel

#print axioms Wong.SmoothModel.function_curvature_gradient_mem_of_visible_hessian_row
#print axioms Wong.SmoothModel.function_curvature_gradient_degree_le_two
