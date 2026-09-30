import Wong.RankStructure

/-!
# Function-element quadratic constraints from linear rank two

These statements use the actual smooth estimation algebra and Ocone's proved
quadratic degree bound. They assume neither quadratic-freeness nor any published
Wong-affinity theorem. In coordinates adapted to linear rank two, every function
element has zero visible-hidden mixed second derivatives.
-/

noncomputable section
namespace Wong.SmoothModel

/-- A polynomial of degree at most one has its genuine smooth affine form. -/
theorem polynomialSmooth_exists_affine_of_degree_le_one (p : RealPoly)
    (hp : p.totalDegree ≤ 1) :
    ∃ c : ℝ, ∃ a : State, polynomialSmooth p = c • smoothOne + linearFunction a := by
  refine ⟨p.coeff 0, fun i => p.coeff (Finsupp.single i 1), ?_⟩
  apply Subtype.ext
  funext x
  simpa only [polynomialSmooth_apply, Submodule.coe_add, Submodule.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, smoothOne, mul_one, linearFunction] using
    Wong.PolynomialAffinity.eval_eq_affine p hp x

/-- Ocone's degree bound alone makes every first derivative of a function element affine. -/
theorem function_element_partial_affine {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h) (i : Fin 3) :
    ∃ c : ℝ, ∃ a : State, partialDerivative i u = c • smoothOne + linearFunction a := by
  obtain ⟨p, hp, he⟩ := function_element_polynomial_degree_le_two f h u hu
  rw [← he, partialDerivative_polynomialSmooth]
  apply polynomialSmooth_exists_affine_of_degree_le_one
  have hd := Wong.PolynomialGradient.partial_totalDegree_le p i
  omega

/-- A visible derivative is a genuine function element, by commutation with the
covariant derivative supplied by the corresponding coordinate multiplier. -/
theorem function_element_partial_mem_of_coordinate_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (i : Fin 3)
    (hi : multiplication (linearFunction (coordinateVector i)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h) :
    multiplication (partialDerivative i u) ∈ estimationAlgebra f h := by
  rw [← lie_D_multiplication f i u]
  exact (estimationAlgebra f h).lie_mem (D_mem_of_coordinate_mem f h i hi) hu

/-- No visible-hidden quadratic term is compatible with adapted linear rank two.
No quadratic-freeness hypothesis is needed. -/
theorem function_element_hidden_visible_mixed_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h)
    (i : Fin 3)
    (hi : multiplication (linearFunction (coordinateVector i)) ∈ estimationAlgebra f h) :
    partialDerivative 2 (partialDerivative i u) = 0 := by
  obtain ⟨c, a, ha⟩ := function_element_partial_affine f h u hu i
  have hdu := function_element_partial_mem_of_coordinate_mem f h i hi u hu
  have hone := smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have haE : a ∈ linearCoefficientSpace (estimationAlgebra f h) := by
    change multiplication (linearFunction a) ∈ estimationAlgebra f h
    have hsub := (estimationAlgebra f h).sub_mem hdu
      ((estimationAlgebra f h).smul_mem c hone)
    simpa [ha] using hsub
  have ha₂ := rank_two_adapted_coefficient_zero (estimationAlgebra f h)
    hrank h₀ h₁ a haE
  rw [ha, map_add, partialDerivative_const, partialDerivative_linearFunction, ha₂]
  simp

/-- The two prohibited mixed quadratic terms, stated together for downstream use. -/
theorem function_element_visible_hidden_mixed_partials {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h) :
    partialDerivative 2 (partialDerivative 0 u) = 0 ∧
      partialDerivative 2 (partialDerivative 1 u) = 0 :=
  ⟨function_element_hidden_visible_mixed_zero f h hrank h₀ h₁ u hu 0 h₀,
    function_element_hidden_visible_mixed_zero f h hrank h₀ h₁ u hu 1 h₁⟩

/-- The same restriction is an identity of actual multivariate polynomials. -/
theorem polynomial_function_element_visible_hidden_mixed_partials {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : RealPoly) (hp : multiplication (polynomialSmooth p) ∈ estimationAlgebra f h) :
    MvPolynomial.pderiv 2 (MvPolynomial.pderiv 0 p) = 0 ∧
      MvPolynomial.pderiv 2 (MvPolynomial.pderiv 1 p) = 0 := by
  obtain ⟨h₀p, h₁p⟩ := function_element_visible_hidden_mixed_partials
    f h hrank h₀ h₁ (polynomialSmooth p) hp
  constructor
  · apply polynomialSmooth_injective
    simpa only [partialDerivative_polynomialSmooth, polynomialSmooth_zero] using h₀p
  · apply polynomialSmooth_injective
    simpa only [partialDerivative_polynomialSmooth, polynomialSmooth_zero] using h₁p

/-- An exact degree formulation of the assertion that every function element is affine. -/
def FunctionElementsAffine (E : LieSubalgebra ℝ Operator) : Prop :=
  ∀ u : Smooth, multiplication u ∈ E →
    ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = u

/-- An affine function-element space excludes every actual quadratic multiplier.
This implication needs neither finite-dimensionality nor a filtering generator. -/
theorem quadraticFree_of_functionElementsAffine (E : LieSubalgebra ℝ Operator)
    (haff : FunctionElementsAffine E) : QuadraticFree E := by
  intro p hp hmem
  obtain ⟨A, hA, haction⟩ := hmem
  have hAeq : A = multiplication (polynomialSmooth p) := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    exact haction u x
  have hpE : multiplication (polynomialSmooth p) ∈ E := hAeq ▸ hA
  obtain ⟨q, hq, he⟩ := haff (polynomialSmooth p) hpE
  have hqp : q = p := polynomialSmooth_injective he
  rw [hqp, hp] at hq
  omega

/-- For the actual finite-dimensional filtering algebra, Ocone's internally proved
bound makes quadratic-freeness exactly equivalent to affine function elements. -/
theorem quadraticFree_iff_functionElementsAffine {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)] :
    QuadraticFree (estimationAlgebra f h) ↔ FunctionElementsAffine (estimationAlgebra f h) := by
  constructor
  · intro hq u hu
    exact quadraticFree_function_element_degree_le_one f h hq u hu
  · exact quadraticFree_of_functionElementsAffine (estimationAlgebra f h)

end Wong.SmoothModel
