import Wong.ParameterCoefficient
import Wong.FirstOrderExtraction

/-!
# Polynomiality of actual first-order principal coefficients

This proves the first-order case of the external highest-coefficient structure
theorem directly from finite dimensionality. The coefficient functions are not
assumed to be function elements of the estimation algebra.
-/

noncomputable section
namespace Wong.SmoothModel

/-- Polarizing the direction and differentiating once more gives a uniform
coordinate nilpotence statement for every principal coefficient. -/
theorem firstOrder_uniform_partial_coefficient_nilpotence {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    ∃ k : ℕ, ∀ (a : Fin 3 → Smooth) (b : Smooth),
      firstOrder f a b ∈ estimationAlgebra f h →
      ∀ i j : Fin 3, (partialDerivative i ^ (k + 1)) (a j) = 0 := by
  obtain ⟨k, _, hk⟩ := firstOrder_uniform_directional_coefficient_nilpotence f h
  refine ⟨k, ?_⟩
  intro a b hab i j
  apply operatorPencil_nilpotent_coefficient (partialDerivative i) (partialDerivative j)
    (partialDerivative_commute i j) (a i) (a j) k
  intro t
  have hv := hk a b hab (coordinateVector i + t • coordinateVector j)
  simpa only [directionalDerivative_add, directionalDerivative_smul,
    coordinate_directionalDerivative, coefficientAlong_add, coefficientAlong_smul,
    coefficientAlong_coordinate] using hv

/-- Every first-order principal coefficient in the genuine finite-dimensional
smooth estimation algebra has an actual multivariate polynomial expression.
One common total-degree bound works for all such elements and all coefficients. -/
theorem firstOrder_coefficients_uniform_polynomial_degree {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    ∃ N : ℕ, ∀ (a : Fin 3 → Smooth) (b : Smooth),
      firstOrder f a b ∈ estimationAlgebra f h → ∀ j : Fin 3,
      ∃ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ N ∧
        ∀ x : State, MvPolynomial.eval x p = (a j).1 x := by
  obtain ⟨k, hk⟩ := firstOrder_uniform_partial_coefficient_nilpotence f h
  refine ⟨3 * k, ?_⟩
  intro a b hab j
  exact polynomial_of_partial_nilpotent k (a j) (fun i => hk a b hab i j)

end Wong.SmoothModel
