import Wong.FunctionQuadraticRankConstraints
import Wong.QuadraticFunctionWongConstraints
import Wong.NormalSymbolsRing
import Wong.SmoothGeometry

/-!
# Actual curvature constraints from a diagonal quadratic function element

This is a local, explicit version of the operator step in Shi--Yau 2020,
Lemma 3.2.  The diagonal multiplier is an actual member of the original E.
The affine-Wong consequences are stated as actual derivative identities,
without importing any published theorem or assuming membership of D₂.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Wong.SmoothModel

/-- The two terms of the mixed curvature derivative; no scalar remainder is
lost, since the expression is a genuine smooth multiplication coefficient. -/
theorem diagonal_function_curvature_mixed_partial
    (f : Fin 3 → Smooth) (u : Smooth) (a : State)
    (hu : ∀ j : Fin 3, partialDerivative j u =
      (2*a j) • linearFunction (coordinateVector j))
    (hW : ∀ r s i j : Fin 3,
      partialDerivative r (partialDerivative s (wong f i j)) = 0)
    (i k : Fin 3) :
    partialDerivative 2 (partialDerivative k (functionCurvatureGradient f u i)) =
      (2*a k) • partialDerivative 2 (wong f k i) +
        (2*a 2) • partialDerivative k (wong f 2 i) := by
  have hone (r : Fin 3) : partialDerivative r smoothOne = 0 := by
    simpa only [one_smul] using partialDerivative_const r 1
  simp only [functionCurvatureGradient, hu, map_sum, partialDerivative_smoothMul,
    map_smul, partialDerivative_linearFunction, map_add, hone, hW]
  apply Subtype.ext
  funext x
  fin_cases k <;> simp [smoothMul, smoothOne, coordinateVector,
    Fin.sum_univ_three, Pi.single_apply] <;> ring

/-- A nonzero hidden diagonal Hessian forces every mixed Wong entry to be
independent of the visible coordinates.  Quadratic-freeness is not assumed. -/
theorem diagonal_quadratic_hidden_coefficient_forces_mixed_visible_partials_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (huE : multiplication u ∈ estimationAlgebra f h)
    (a : State) (ha : a 2 ≠ 0)
    (hu : ∀ j : Fin 3, partialDerivative j u =
      (2*a j) • linearFunction (coordinateVector j))
    (hW : ∀ r s i j : Fin 3,
      partialDerivative r (partialDerivative s (wong f i j)) = 0)
    (h₀₁ : partialDerivative 2 (wong f 0 1) = 0) :
    ∀ i k : Fin 3, (i = 0 ∨ i = 1) → (k = 0 ∨ k = 1) →
      partialDerivative k (wong f 2 i) = 0 := by
  intro i k hi hk
  let H : Fin 3 → ℝ := fun j => (2*a j) * coordinateVector j i
  have hH (j : Fin 3) :
      partialDerivative i (partialDerivative j u) = H j • smoothOne := by
    rw [hu j, map_smul, partialDerivative_linearFunction, smul_smul]
  have hhidden : H 2 = 0 := by
    rcases hi with rfl | rfl <;> simp [H, coordinateVector]
  have hF := function_curvature_gradient_mem_of_visible_hessian_row
    f h hx₀ hx₁ u huE i hi H hH hhidden
  have hxk : multiplication (linearFunction (coordinateVector k)) ∈ estimationAlgebra f h := by
    rcases hk with rfl | rfl
    · exact hx₀
    · exact hx₁
  have hz := function_element_hidden_visible_mixed_zero f h hrank hx₀ hx₁
    (functionCurvatureGradient f u i) hF k hxk
  rw [diagonal_function_curvature_mixed_partial f u a hu hW i k] at hz
  have hki : partialDerivative 2 (wong f k i) = 0 := by
    rcases hk with rfl | rfl <;> rcases hi with rfl | rfl
    · simp
    · exact h₀₁
    · rw [wong_skew f 0 1, map_neg, h₀₁, neg_zero]
    · simp
  rw [hki, smul_zero, zero_add] at hz
  have hne : 2*a 2 ≠ 0 := mul_ne_zero (by norm_num) ha
  have he := congrArg (fun v : Smooth => (2*a 2)⁻¹ • v) hz
  simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] using he

end Wong.SmoothModel

#print axioms Wong.SmoothModel.diagonal_function_curvature_mixed_partial
#print axioms Wong.SmoothModel.diagonal_quadratic_hidden_coefficient_forces_mixed_visible_partials_zero
