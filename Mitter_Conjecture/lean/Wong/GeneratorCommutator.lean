import Wong.FirstOrderExtraction

/-!
# The actual generator commutator and its Wong principal coefficients

The formula below identifies the coefficients of the genuine first-order
operator `[L₀,Dᵢ]`. The potential derivative is retained, including its sign.
Membership is asserted only when the specified `Dᵢ` belongs to the algebra.
-/

noncomputable section
namespace Wong.SmoothModel

theorem lie_D_square_D (f : Fin 3 → Smooth) (i j : Fin 3) :
    ⁅D f j * D f j, D f i⁆ =
      (2 : ℝ) • (multiplication (wong f i j) * D f j) +
        multiplication (partialDerivative j (wong f i j)) := by
  rw [operator_lie_mul_left, lie_D_D, D_mul_multiplication]
  simp only [two_smul]
  abel

/-- The precise zero-order remainder of the generator commutator. -/
def generatorRemainder {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3) : Smooth :=
  (1 / 2 : ℝ) • ((∑ j, partialDerivative j (wong f i j)) + partialDerivative i (eta f h))

theorem lie_L0_D {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) (i : Fin 3) :
    ⁅L0 f h, D f i⁆ =
      (∑ j, multiplication (wong f i j) * D f j) +
        multiplication (generatorRemainder f h i) := by
  have heta : ⁅multiplication (eta f h), D f i⁆ =
      -multiplication (partialDerivative i (eta f h)) := by
    rw [← lie_skew, lie_D_multiplication]
  simp only [L0, sub_lie, smul_lie, sum_lie, lie_D_square_D, heta,
    smul_neg, sub_neg_eq_add, Finset.smul_sum, smul_add, smul_smul,
    generatorRemainder, multiplication_smul, multiplication_add, multiplication_sum]
  norm_num
  rw [Finset.sum_add_distrib]
  abel

/-- The principal coefficient tuple of `[L₀,Dᵢ]` is exactly the corresponding Wong row. -/
theorem lie_L0_D_eq_firstOrder {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3) :
    ⁅L0 f h, D f i⁆ = firstOrder f (wong f i) (generatorRemainder f h i) :=
  lie_L0_D f h i

theorem firstOrder_wong_mem_of_D_mem {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (i : Fin 3) (hi : D f i ∈ estimationAlgebra f h) :
    firstOrder f (wong f i) (generatorRemainder f h i) ∈ estimationAlgebra f h := by
  rw [← lie_L0_D_eq_firstOrder]
  exact (estimationAlgebra f h).lie_mem (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hi

/-- Every Wong row attached to an admitted covariant derivative has a uniform
    vanishing higher directional derivative of its directional coefficient. -/
theorem wong_row_directional_nilpotence {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)] :
    ∃ k : ℕ, 0 < k ∧ ∀ i : Fin 3, D f i ∈ estimationAlgebra f h →
      ∀ v : State, (directionalDerivative v ^ k) (coefficientAlong (wong f i) v) = 0 := by
  obtain ⟨k, hk, hnil⟩ := firstOrder_uniform_directional_coefficient_nilpotence f h
  refine ⟨k, hk, ?_⟩
  intro i hi v
  exact hnil (wong f i) (generatorRemainder f h i)
    (firstOrder_wong_mem_of_D_mem f h i hi) v

end Wong.SmoothModel
