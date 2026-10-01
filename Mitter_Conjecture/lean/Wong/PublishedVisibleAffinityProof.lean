import Wong.PublishedAffineStatement

/-!
# Internal proof of the visible affinity needed by the original main claim

The published 2017 Theorem 3.4 assumes finite dimensionality and adapted
linear rank two, but does not assume quadratic-freeness. The theorem below
is deliberately named and stated with the additional `QuadraticFree`
hypothesis of `QuadraticFreeMainClaim`. It is sufficient for that conditional claim
and is not presented as a proof of the stronger published theorem.

Its proof uses only the internally proved Ocone function-element theorem,
the actual covariant commutator, and the actual rank-two coefficient space.
No published affinity axiom or theorem depending on that axiom is imported.
-/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

/-- Even without quadratic-freeness, the visible Wong entry is an actual
polynomial of degree at most two, because its multiplication operator is
an actual Lie bracket of the two admitted covariant derivatives. -/
theorem visible_wong_polynomial_degree_le_two {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = wong f 0 1 :=
  function_element_polynomial_degree_le_two f h (wong f 0 1)
    (wong_mem_of_coordinate_mem f h 0 1 hx₀ hx₁)

/-- The original quadratic-free model gives visible affine coefficients,
and its rank-two condition removes the hidden linear coefficient. -/
theorem visible_wong_affine_of_quadraticFree {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    ∃ c a₀ a₁ : ℝ, wong f 0 1 = c • smoothOne +
      a₀ • linearFunction (coordinateVector 0) +
      a₁ • linearFunction (coordinateVector 1) :=
  function_element_adapted f h hrank hq hx₀ hx₁ (wong f 0 1)
    (wong_mem_of_coordinate_mem f h 0 1 hx₀ hx₁)

/-- The exact visible polynomial conclusion, proved internally under the
quadratic-free hypothesis already present in the frozen original main claim. -/
theorem visible_wong_published_polynomial_of_quadraticFree {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ pderiv 2 p = 0 ∧
      polynomialSmooth p = wong f 0 1 := by
  obtain ⟨c, a₀, a₁, he⟩ := visible_wong_affine_of_quadraticFree f h hrank hq hx₀ hx₁
  refine ⟨affineScalarPolynomial c ![a₀, a₁, 0],
    affineScalarPolynomial_degree_le_one _ _, ?_, ?_⟩
  · rw [pderiv_affineScalarPolynomial]
    simp
  · rw [polynomialSmooth_affineScalarPolynomial, he]
    apply Subtype.ext
    funext x
    simp [smoothOne, linearFunction, coordinateVector, Fin.sum_univ_three]
    ring

/-- In the actual smooth model the visible Wong entry has zero hidden
partial derivative, not merely a vanishing formal coefficient. -/
theorem visible_wong_hidden_partial_zero_of_quadraticFree {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    partialDerivative 2 (wong f 0 1) = 0 := by
  obtain ⟨p, _, hp, he⟩ :=
    visible_wong_published_polynomial_of_quadraticFree f h hrank hq hx₀ hx₁
  rw [← he, partialDerivative_polynomialSmooth, hp, polynomialSmooth_zero]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visible_wong_polynomial_degree_le_two
#print axioms Wong.SmoothModel.visible_wong_affine_of_quadraticFree
#print axioms Wong.SmoothModel.visible_wong_published_polynomial_of_quadraticFree
#print axioms Wong.SmoothModel.visible_wong_hidden_partial_zero_of_quadraticFree
