import Wong.DirectionalExtraction
import Wong.PrincipalExtraction

/-!
# Genuine highest-coefficient extraction for first-order operators

For an actual first-order operator in the smooth estimation algebra, the
principal coefficient in direction `v` is obtained by one commutator with
the linear multiplier in direction `v`. The uniform order bound and the
proved factorial identity then annihilate a common higher directional
derivative. No coefficient is assumed to be a function element of the Lie
algebra, and no a priori polynomiality is assumed.
-/

noncomputable section
namespace Wong.SmoothModel

/-- A genuine first-order operator written in the drift-dependent frame. -/
def firstOrder (f a : Fin 3 → Smooth) (b : Smooth) : Operator :=
  (∑ i, multiplication (a i) * D f i) + multiplication b

/-- The principal scalar coefficient in a constant direction. -/
def coefficientAlong (a : Fin 3 → Smooth) (v : State) : Smooth := ∑ i, v i • a i

theorem directionalDerivative_add (v w : State) :
    directionalDerivative (v + w) = directionalDerivative v + directionalDerivative w := by
  simp [directionalDerivative, add_smul, Finset.sum_add_distrib]

theorem directionalDerivative_smul (c : ℝ) (v : State) :
    directionalDerivative (c • v) = c • directionalDerivative v := by
  simp [directionalDerivative, Finset.smul_sum, smul_smul]

theorem coefficientAlong_add (a : Fin 3 → Smooth) (v w : State) :
    coefficientAlong a (v + w) = coefficientAlong a v + coefficientAlong a w := by
  simp [coefficientAlong, add_smul, Finset.sum_add_distrib]

theorem coefficientAlong_smul (a : Fin 3 → Smooth) (c : ℝ) (v : State) :
    coefficientAlong a (c • v) = c • coefficientAlong a v := by
  simp [coefficientAlong, Finset.smul_sum, smul_smul]

@[simp] theorem coefficientAlong_coordinate (a : Fin 3 → Smooth) (i : Fin 3) :
    coefficientAlong a (coordinateVector i) = a i := by
  simp [coefficientAlong, coordinateVector, Pi.single_apply, ite_smul]

/-- One linear-multiplier commutator extracts exactly the directional
    principal coefficient; the zero-order remainder disappears. -/
theorem commuteWithLinear_firstOrder (f a : Fin 3 → Smooth) (b : Smooth) (v : State) :
    commuteWithMultiplier (linearFunction v) (firstOrder f a b) =
      multiplication (coefficientAlong a v) := by
  simp only [commuteWithMultiplier_apply, firstOrder, add_lie, sum_lie,
    operator_lie_mul_left, lie_D_multiplication, lie_multiplication_multiplication,
    partialDerivative_linearFunction, multiplication_smul, multiplication_smoothOne,
    zero_mul, add_zero, mul_smul_comm, mul_one, coefficientAlong,
    multiplication_sum]

/-- A second linear-multiplier commutator kills every first-order operator. -/
theorem commuteWithLinear_firstOrder_twice (f a : Fin 3 → Smooth) (b : Smooth) (v : State) :
    (commuteWithMultiplier (linearFunction v) ^ 2) (firstOrder f a b) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Wong.AdjointIteration.end_pow_succ_apply]
  rw [pow_one, commuteWithLinear_firstOrder]
  exact lie_multiplication_multiplication (coefficientAlong a v) (linearFunction v)

/-- Finite dimensionality of the actual estimation algebra imposes a common
    positive directional derivative order on all first-order principal
    coefficients. This is derived from the concrete operators and their Lie
    algebra, rather than taken as a structural assumption. -/
theorem firstOrder_uniform_directional_coefficient_nilpotence {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    ∃ k : ℕ, 0 < k ∧ ∀ (a : Fin 3 → Smooth) (b : Smooth),
      firstOrder f a b ∈ estimationAlgebra f h → ∀ v : State,
        (directionalDerivative v ^ k) (coefficientAlong a v) = 0 := by
  obtain ⟨N, hN⟩ := estimationAlgebra_uniform_order_bound f h
  refine ⟨N + 1, Nat.zero_lt_succ N, ?_⟩
  intro a b hA v
  let δ : Module.End ℝ Operator := commuteWithMultiplier (linearFunction v)
  let T : Module.End ℝ Operator := LieAlgebra.ad ℝ Operator (L0 f h)
  let H : Module.End ℝ Operator := LieAlgebra.ad ℝ Operator (directionD f v)
  have hDT : ∀ A, δ (T A) = T (δ A) + H A := by
    intro A
    change commuteWithMultiplier (linearFunction v) ⁅L0 f h, A⁆ =
      ⁅L0 f h, commuteWithMultiplier (linearFunction v) A⁆ + ⁅directionD f v, A⁆
    rw [commuteWithMultiplier_lie]
    simp only [commuteWithMultiplier_apply, lie_L0_linearFunction]
  have hDH : ∀ A, δ (H A) = H (δ A) := by
    intro A
    change commuteWithMultiplier (linearFunction v) ⁅directionD f v, A⁆ =
      ⁅directionD f v, commuteWithMultiplier (linearFunction v) A⁆
    rw [commuteWithMultiplier_lie]
    simp only [commuteWithMultiplier_apply, lie_directionD_linearFunction,
      scalar_identity_lie, add_zero]
  have hv : (δ ^ 2) (firstOrder f a b) = 0 :=
    commuteWithLinear_firstOrder_twice f a b v
  have hz : (δ ^ ((N + 1) + 1)) ((T ^ (N + 1)) (firstOrder f a b)) = 0 := by
    rw [Module.End.pow_apply]
    apply iterate_commuteWithMultiplier_eq_zero
    apply orderSpace_le_succ N
    apply hN
    exact ad_L0_pow_mem_estimationAlgebra f h hA (N + 1)
  have hH := Wong.PrincipalExtraction.extracted_power_zero δ T H hDT hDH
    (firstOrder f a b) hv (N + 1) hz
  change (H ^ (N + 1)) (commuteWithMultiplier (linearFunction v) (firstOrder f a b)) = 0 at hH
  rw [commuteWithLinear_firstOrder] at hH
  apply multiplication_injective
  rw [multiplication_zero, ← ad_directionD_pow_multiplication f v (coefficientAlong a v) (N + 1)]
  exact hH

end Wong.SmoothModel
