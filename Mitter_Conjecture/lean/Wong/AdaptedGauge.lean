import Wong.GlobalGauge
import Wong.AffineGaugeRepresentative
import Wong.NormalFormAlgebra
import Wong.FirstOrderPolynomial

/-!
# Actual adapted gauge representatives

The algebra after a gauge is the image of the original estimation algebra.
Its filtering generator retains the original potential. Function-element
and first-order coefficient statements are transported from that original
algebra, with no assertion that recomputing eta gives the same operator.
-/

noncomputable section
namespace Wong.SmoothModel

def AdaptedFunctionSpace (E : LieSubalgebra ℝ Operator) : Prop :=
  ∀ u : Smooth, multiplication u ∈ E →
    ∃ c a₀ a₁ : ℝ, u = c • smoothOne +
      a₀ • linearFunction (coordinateVector 0) + a₁ • linearFunction (coordinateVector 1)

theorem adaptedFunctionSpace_estimation {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    AdaptedFunctionSpace (estimationAlgebra f h) :=
  function_element_adapted f h hrank hq hx₀ hx₁

theorem adaptedFunctionSpace_gauge (Λ : Smooth) (E : LieSubalgebra ℝ Operator)
    (hE : AdaptedFunctionSpace E) : AdaptedFunctionSpace (gaugeAlgebra Λ E) := by
  intro u hu
  exact hE u ((multiplication_mem_gaugeAlgebra Λ E u).mp hu)

theorem exists_triangular_gauge (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    ∃ Λ : Smooth, gaugeDrift Λ f = triangularDrift p :=
  exists_gaugeDrift_of_wong_eq f (triangularDrift p) (triangularDrift_wong_eq f p hform)

theorem filteringOperator_mem_gaugeAlgebra (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (f : Fin 3 → Smooth) (V : Smooth)
    (hL : filteringOperator f V ∈ E) :
    filteringOperator (gaugeDrift Λ f) V ∈ gaugeAlgebra Λ E := by
  exact ⟨filteringOperator f V, hL, gaugeConjugation_filteringOperator f V Λ⟩

theorem D_mem_gaugeAlgebra (Λ : Smooth) (E : LieSubalgebra ℝ Operator)
    (f : Fin 3 → Smooth) (i : Fin 3) (hD : D f i ∈ E) :
    D (gaugeDrift Λ f) i ∈ gaugeAlgebra Λ E := by
  exact ⟨D f i, hD, gaugeConjugation_D Λ f i⟩

theorem gaugeConjugation_firstOrder (Λ : Smooth) (f a : Fin 3 → Smooth) (b : Smooth) :
    gaugeConjugation Λ (firstOrder f a b) = firstOrder (gaugeDrift Λ f) a b := by
  simp only [firstOrder, map_add, map_sum, map_mul,
    gaugeConjugation_multiplication, gaugeConjugation_D]

theorem firstOrder_mem_gaugeAlgebra_iff (Λ : Smooth) (E : LieSubalgebra ℝ Operator)
    (f a : Fin 3 → Smooth) (b : Smooth) :
    firstOrder (gaugeDrift Λ f) a b ∈ gaugeAlgebra Λ E ↔ firstOrder f a b ∈ E := by
  constructor
  · rintro ⟨A, hA, he⟩
    have he' : gaugeConjugation Λ A = gaugeConjugation Λ (firstOrder f a b) :=
      he.trans (gaugeConjugation_firstOrder Λ f a b).symm
    exact (gaugeConjugation Λ).injective he' ▸ hA
  · intro hab
    exact ⟨firstOrder f a b, hab, gaugeConjugation_firstOrder Λ f a b⟩

theorem firstOrder_gauge_coefficients_uniform_polynomial_degree {m : ℕ}
    (Λ : Smooth) (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    ∃ N : ℕ, ∀ (a : Fin 3 → Smooth) (b : Smooth),
      firstOrder (gaugeDrift Λ f) a b ∈ gaugeAlgebra Λ (estimationAlgebra f h) →
      ∀ j : Fin 3, ∃ p : RealPoly, p.totalDegree ≤ N ∧
        ∀ x : State, MvPolynomial.eval x p = (a j).1 x := by
  obtain ⟨N, hN⟩ := firstOrder_coefficients_uniform_polynomial_degree f h
  refine ⟨N, ?_⟩
  intro a b hab j
  exact hN a b ((firstOrder_mem_gaugeAlgebra_iff Λ _ f a b).mp hab) j

end Wong.SmoothModel
