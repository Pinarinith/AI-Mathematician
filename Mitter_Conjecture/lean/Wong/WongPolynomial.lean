import Wong.GeneratorCommutator
import Wong.FirstOrderPolynomial
import Wong.RankStructure
import Wong.SmoothGeometry

/-!
# Actual polynomiality of every Wong entry in adapted coordinates

Only the two stated coordinate multiplier memberships are used here. They
give `D₀,D₁` in the actual algebra, so the first-order commutator formulas
give the first two polynomial Wong rows. Antisymmetry supplies the final row.
Polynomiality and its uniform degree bound are conclusions, not hypotheses.
-/

noncomputable section
namespace Wong.SmoothModel

theorem wong_uniform_polynomial_degree_of_coordinate_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    ∃ N : ℕ, ∀ i j : Fin 3, ∃ p : MvPolynomial (Fin 3) ℝ,
      p.totalDegree ≤ N ∧ ∀ x : State, MvPolynomial.eval x p = (wong f i j).1 x := by
  obtain ⟨N, hN⟩ := firstOrder_coefficients_uniform_polynomial_degree f h
  have row₀ := hN (wong f 0) (generatorRemainder f h 0)
    (firstOrder_wong_mem_of_D_mem f h 0 (D_mem_of_coordinate_mem f h 0 h₀))
  have row₁ := hN (wong f 1) (generatorRemainder f h 1)
    (firstOrder_wong_mem_of_D_mem f h 1 (D_mem_of_coordinate_mem f h 1 h₁))
  refine ⟨N, ?_⟩
  intro i j
  fin_cases i
  · exact row₀ j
  · exact row₁ j
  · fin_cases j
    · obtain ⟨p, hp, he⟩ := row₀ 2
      refine ⟨-p, ?_, ?_⟩
      · simpa using hp
      · intro x
        rw [MvPolynomial.eval_neg, he]
        exact (congrArg (fun u : Smooth => u.1 x) (wong_skew f 0 2)).symm
    · obtain ⟨p, hp, he⟩ := row₁ 2
      refine ⟨-p, ?_, ?_⟩
      · simpa using hp
      · intro x
        rw [MvPolynomial.eval_neg, he]
        exact (congrArg (fun u : Smooth => u.1 x) (wong_skew f 1 2)).symm
    · refine ⟨0, ?_, ?_⟩
      · simp
      · simp

/-- Smooth-function equality form of the preceding actual polynomiality result. -/
theorem wong_polynomialSmooth_of_coordinate_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (i j : Fin 3) : ∃ p : RealPoly, polynomialSmooth p = wong f i j := by
  obtain ⟨_, hpoly⟩ := wong_uniform_polynomial_degree_of_coordinate_mem f h h₀ h₁
  obtain ⟨p, _, hp⟩ := hpoly i j
  refine ⟨p, Subtype.ext (funext hp)⟩

end Wong.SmoothModel
