import Wong.FunctionElements
import Wong.PolynomialGradient
import Wong.PolynomialSmooth
import Wong.PolynomialAffinity

/-!
# Ocone's theorem for the actual smooth estimation algebra

Finite dimensionality alone implies that every genuine function element is a
real multivariate polynomial of total degree at most two. Quadratic-freeness
then forces all such function elements to be affine. Every bridge in this
file uses the actual smooth multiplication and differentiation operators.
-/

noncomputable section
namespace Wong.SmoothModel
open Wong.PolynomialGradient

/-- The polynomial squared gradient is the true double commutator in the
original smooth operator algebra. -/
theorem polynomial_gradient_double_commutator {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (p : RealPoly) :
    multiplication (polynomialSmooth (gradientSquare p)) =
      ⁅⁅L0 f h, multiplication (polynomialSmooth p)⁆,
        multiplication (polynomialSmooth p)⁆ := by
  rw [double_lie_L0_multiplication]
  simp only [gradientSquare, polynomialSmooth_sum, pow_two, polynomialSmooth_mul,
    partialDerivative_polynomialSmooth]

/-- Ocone's degree-two bound is proved for actual polynomial function elements. -/
theorem polynomial_function_element_degree_le_two {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (p : RealPoly) (hp : multiplication (polynomialSmooth p) ∈ estimationAlgebra f h) :
    p.totalDegree ≤ 2 := by
  obtain ⟨N, hN⟩ := function_elements_uniform_polynomial_degree f h
  let S : Set RealPoly := {q | multiplication (polynomialSmooth q) ∈ estimationAlgebra f h}
  have hclosed : ∀ q ∈ S, gradientSquare q ∈ S := by
    intro q hq
    change multiplication (polynomialSmooth (gradientSquare q)) ∈ estimationAlgebra f h
    rw [polynomial_gradient_double_commutator f h]
    have hL : L0 f h ∈ estimationAlgebra f h :=
      LieSubalgebra.subset_lieSpan (Or.inl rfl)
    exact (estimationAlgebra f h).lie_mem
      ((estimationAlgebra f h).lie_mem hL hq) hq
  have hbound : ∀ q ∈ S, q.totalDegree ≤ N := by
    intro q hq
    obtain ⟨r, hr, he⟩ := hN (polynomialSmooth q) hq
    have hrq : r = q := MvPolynomial.funext he
    simpa only [hrq] using hr
  exact degree_le_two_of_gradient_closed S hclosed N hbound p hp

/-- Full Ocone function-element theorem, without assuming polynomiality or a
symbolic model: the hypotheses are those of the actual smooth estimation algebra. -/
theorem function_element_polynomial_degree_le_two {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = u := by
  obtain ⟨N, hN⟩ := function_elements_uniform_polynomial_degree f h
  obtain ⟨p, _, he⟩ := hN u hu
  have hpu : polynomialSmooth p = u := Subtype.ext (funext he)
  refine ⟨p, polynomial_function_element_degree_le_two f h p ?_, hpu⟩
  simpa only [hpu] using hu

/-- Quadratic-freeness now rules out the only nonaffine polynomial degree. -/
theorem quadraticFree_function_element_degree_le_one {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hq : QuadraticFree (estimationAlgebra f h))
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = u := by
  obtain ⟨p, hp, he⟩ := function_element_polynomial_degree_le_two f h u hu
  have hne : p.totalDegree ≠ 2 := by
    intro hd
    apply hq p hd
    refine ⟨multiplication u, hu, ?_⟩
    intro v x
    rw [← he]
    rfl
  exact ⟨p, by omega, he⟩

/-- Every true function element is affine under the manuscript's original
finite-dimensionality and quadratic-freeness hypotheses. -/
theorem quadraticFree_function_element_affine {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hq : QuadraticFree (estimationAlgebra f h))
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h) :
    ∃ c : ℝ, ∃ a : State, u = c • smoothOne + linearFunction a := by
  obtain ⟨p, hp, he⟩ := quadraticFree_function_element_degree_le_one f h hq u hu
  refine ⟨p.coeff 0, fun i => p.coeff (Finsupp.single i 1), ?_⟩
  rw [← he]
  apply Subtype.ext
  funext x
  simpa only [polynomialSmooth_apply, Submodule.coe_add, Submodule.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, smoothOne, mul_one, linearFunction] using
    Wong.PolynomialAffinity.eval_eq_affine p hp x

end Wong.SmoothModel
