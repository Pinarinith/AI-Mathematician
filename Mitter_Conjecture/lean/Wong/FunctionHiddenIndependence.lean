import Wong.RankTwoFunctionCurvature
import Wong.QuadraticHiddenLinearTail
import Wong.SmoothGeometry

/-!
# No hidden quadratic function implies actual hidden independence

The globally smooth first derivatives have Ocone's affine representations.
Their compatible visible Hessian integrates to a real binary quadratic.
Only genuinely admitted visible affine functions and constants are subtracted.
The proved gradient-word recovery then excludes the remaining hidden linear
term.  This supplies the weak function-space hypothesis without quadratic-free
assumptions and without classifying polynomial monomials by hand.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Wong.SmoothModel
open MvPolynomial

/-- A genuine function element with zero hidden second derivative has zero
hidden first derivative in an adapted rank-two algebra. -/
theorem function_hidden_partial_zero_of_hidden_second_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h)
    (hzz : partialDerivative 2 (partialDerivative 2 u) = 0) :
    partialDerivative 2 u = 0 := by
  obtain ⟨c₀, a₀, h₀⟩ := function_element_partial_affine f h u hu 0
  obtain ⟨c₁, a₁, h₁⟩ := function_element_partial_affine f h u hu 1
  obtain ⟨hz₀, hz₁⟩ := function_element_visible_hidden_mixed_partials
    f h hrank hx₀ hx₁ u hu
  have ha₀ : a₀ 2 = 0 := by
    rw [h₀, map_add, partialDerivative_const, partialDerivative_linearFunction, zero_add] at hz₀
    simpa [smoothOne] using congrArg (fun v : Smooth => v.1 (0 : State)) hz₀
  have ha₁ : a₁ 2 = 0 := by
    rw [h₁, map_add, partialDerivative_const, partialDerivative_linearFunction, zero_add] at hz₁
    simpa [smoothOne] using congrArg (fun v : Smooth => v.1 (0 : State)) hz₁
  have hcross : a₁ 0 = a₀ 1 := by
    have he := partialDerivative_commute_apply 0 1 u
    simp only [h₀, h₁, map_add, partialDerivative_const,
      partialDerivative_linearFunction, zero_add] at he
    simpa [smoothOne] using congrArg (fun v : Smooth => v.1 (0 : State)) he
  obtain ⟨g, k, hhidden⟩ := function_element_hidden_partial_affine_hidden
    f h hrank hx₀ hx₁ u hu
  have hk : k = 0 := by
    rw [hhidden, map_add, partialDerivative_const, map_smul,
      partialDerivative_linearFunction] at hzz
    simpa [smoothOne, coordinateVector] using
      congrArg (fun v : Smooth => v.1 (0 : State)) hzz
  have hg : partialDerivative 2 u = g • smoothOne := by
    simpa only [hk, zero_smul, add_zero] using hhidden
  let q : RealPoly := visibleBinaryQuadratic (a₀ 0/2) (a₀ 1/2) (a₁ 1/2) + C g * X 2
  have hq₀ : partialDerivative 0 (polynomialSmooth q) = linearFunction a₀ := by
    rw [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    simp [q, visibleBinaryQuadratic, polynomialSmooth, pderiv_X, linearFunction,
      Fin.sum_univ_three, ha₀] <;> ring
  have hq₁ : partialDerivative 1 (polynomialSmooth q) = linearFunction a₁ := by
    rw [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    simp [q, visibleBinaryQuadratic, polynomialSmooth, pderiv_X, linearFunction,
      Fin.sum_univ_three, ha₁, hcross] <;> ring
  have hq₂ : partialDerivative 2 (polynomialSmooth q) = g • smoothOne := by
    rw [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    simp [q, visibleBinaryQuadratic, polynomialSmooth, pderiv_X, smoothOne]
  let w : Smooth := u - polynomialSmooth q -
    c₀ • linearFunction (coordinateVector 0) - c₁ • linearFunction (coordinateVector 1)
  have hwpartials : ∀ i : Fin 3, partialDerivative i w = 0 := by
    intro i
    fin_cases i <;>
      simp [w, map_sub, map_smul, partialDerivative_linearFunction,
        h₀, h₁, hg, hq₀, hq₁, hq₂, coordinateVector] <;> abel
  obtain ⟨r, hr⟩ := (smooth_constant_iff_partials_zero w).mpr hwpartials
  have hw : w = r • smoothOne := by
    apply Subtype.ext
    funext x
    simpa [smoothOne] using hr x
  have heq : u - c₀ • linearFunction (coordinateVector 0) -
      c₁ • linearFunction (coordinateVector 1) - r • smoothOne = polynomialSmooth q := by
    calc
      _ = polynomialSmooth q + (w - r • smoothOne) := by dsimp [w]; abel
      _ = _ := by rw [hw]; simp
  have hrestE : multiplication (u - c₀ • linearFunction (coordinateVector 0) -
      c₁ • linearFunction (coordinateVector 1) - r • smoothOne) ∈ estimationAlgebra f h := by
    simp only [multiplication_sub, multiplication_smul]
    exact (estimationAlgebra f h).sub_mem
      ((estimationAlgebra f h).sub_mem
        ((estimationAlgebra f h).sub_mem hu ((estimationAlgebra f h).smul_mem c₀ hx₀))
        ((estimationAlgebra f h).smul_mem c₁ hx₁))
      ((estimationAlgebra f h).smul_mem r (smoothOne_mem_estimationAlgebra_of_rank_two f h hrank))
  rw [heq] at hrestE
  have hgzero := hidden_linear_tail_zero_of_visible_binary_quadratic_member
    f h hrank hx₀ hx₁ (a₀ 0/2) (a₀ 1/2) (a₁ 1/2) g hrestE
  rw [hg, hgzero, zero_smul]

/-- The exact global weak function-space assertion follows from absence of
hidden quadratic curvature in every genuine function element. -/
theorem function_elements_hidden_independent_of_hidden_second_partials_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hzz : ∀ u : Smooth, multiplication u ∈ estimationAlgebra f h →
      partialDerivative 2 (partialDerivative 2 u) = 0) :
    ∀ u : Smooth, multiplication u ∈ estimationAlgebra f h → partialDerivative 2 u = 0 := by
  intro u hu
  exact function_hidden_partial_zero_of_hidden_second_zero f h hrank hx₀ hx₁ u hu (hzz u hu)

end Wong.SmoothModel

#print axioms Wong.SmoothModel.function_hidden_partial_zero_of_hidden_second_zero
#print axioms Wong.SmoothModel.function_elements_hidden_independent_of_hidden_second_partials_zero
