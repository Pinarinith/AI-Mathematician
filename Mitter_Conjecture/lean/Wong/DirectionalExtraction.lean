import Wong.DifferentialOrder
import Wong.AdjointIteration

/-!
# From the actual finite-dimensional estimation algebra to vanishing derivatives

Right commutation with a homogeneous linear multiplier lowers differential
order. The identities below connect that filtration to genuine repeated
coordinate-direction derivatives of smooth function elements.
-/

noncomputable section
namespace Wong.SmoothModel
open scoped ContDiff

/-- A constant directional partial derivative on real three-space. -/
def directionalDerivative (v : State) : Operator := ∑ i, v i • partialDerivative i

/-- The directional operator is the actual Fréchet derivative evaluated
    on the constant vector, rather than a formal substitute for it. -/
theorem directionalDerivative_apply (v : State) (u : Smooth) (x : State) :
    (directionalDerivative v u).1 x = fderiv ℝ u.1 x v := by
  have hv : (∑ i, v i • coordinateVector i) = v := by
    funext j
    simp [coordinateVector, Pi.single_apply]
  calc
    (directionalDerivative v u).1 x =
        ∑ i, v i • (fderiv ℝ u.1 x (coordinateVector i)) := by
      simp [directionalDerivative, partialDerivative]
    _ = fderiv ℝ u.1 x (∑ i, v i • coordinateVector i) := by
      simp only [map_sum, map_smul]
    _ = fderiv ℝ u.1 x v := by rw [hv]

/-- The associated covariant directional derivative. -/
def directionD (f : Fin 3 → Smooth) (v : State) : Operator := ∑ i, v i • D f i

@[simp] theorem multiplication_smoothOne : multiplication smoothOne = (1 : Operator) := by
  apply LinearMap.ext
  intro u
  exact (smoothMul_comm smoothOne u).trans (smoothMul_one u)

@[simp] theorem partialDerivative_const (i : Fin 3) (c : ℝ) :
    partialDerivative i (c • smoothOne) = 0 := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun _ : State => c * 1) x (coordinateVector i) = 0
  simp

/-- The genuine derivative of a homogeneous linear scalar function. -/
theorem partialDerivative_linearFunction (i : Fin 3) (v : State) :
    partialDerivative i (linearFunction v) = v i • smoothOne := by
  let l : State →L[ℝ] ℝ := ∑ j, v j • (ContinuousLinearMap.proj j : State →L[ℝ] ℝ)
  have hl : (linearFunction v).1 = l := by
    funext x
    simp [linearFunction, l]
  apply Subtype.ext
  funext x
  change fderiv ℝ (linearFunction v).1 x (coordinateVector i) = v i * 1
  rw [hl, ContinuousLinearMap.fderiv]
  simp [l, coordinateVector, Pi.single_apply, mul_ite]

/-- The filtering generator and a linear multiplier yield the covariant
    derivative in the same direction. -/
theorem lie_L0_linearFunction {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (v : State) : ⁅L0 f h, multiplication (linearFunction v)⁆ = directionD f v := by
  rw [lie_L0_multiplication]
  simp only [partialDerivative_linearFunction, partialDerivative_const,
    Finset.sum_const_zero, multiplication_zero, smul_zero, add_zero,
    multiplication_smul, multiplication_smoothOne, smul_mul_assoc, one_mul, directionD]

/-- Covariant and ordinary directional derivatives have the same action on
    multiplication commutators. -/
theorem lie_directionD_multiplication (f : Fin 3 → Smooth) (v : State) (u : Smooth) :
    ⁅directionD f v, multiplication u⁆ = multiplication (directionalDerivative v u) := by
  simp only [directionD, directionalDerivative, sum_lie, smul_lie,
    lie_D_multiplication, LinearMap.sum_apply, LinearMap.smul_apply,
    multiplication_sum, multiplication_smul]

/-- Two commutations of `L₀` with the same linear multiplier give a scalar
    identity operator, hence a central element. -/
theorem lie_directionD_linearFunction (f : Fin 3 → Smooth) (v : State) :
    ⁅directionD f v, multiplication (linearFunction v)⁆ =
      (∑ i, v i * v i) • (1 : Operator) := by
  simp only [directionD, sum_lie, smul_lie, lie_D_multiplication,
    partialDerivative_linearFunction, multiplication_smul,
    multiplication_smoothOne, smul_smul, Finset.sum_smul]

@[simp] theorem lie_scalar_identity (A : Operator) (c : ℝ) :
    ⁅A, c • (1 : Operator)⁆ = 0 := by
  apply LinearMap.ext
  intro u
  change A (c • u) - c • A u = 0
  rw [map_smul, sub_self]

/-- Right commutation is a derivation of the actual operator Lie bracket. -/
theorem commuteWithMultiplier_lie (u : Smooth) (A B : Operator) :
    commuteWithMultiplier u ⁅A, B⁆ =
      ⁅A, commuteWithMultiplier u B⁆ + ⁅commuteWithMultiplier u A, B⁆ := by
  change ⁅⁅A, B⁆, multiplication u⁆ =
    ⁅A, ⁅B, multiplication u⁆⁆ + ⁅⁅A, multiplication u⁆, B⁆
  rw [lie_lie, sub_eq_add_neg, lie_skew]

@[simp] theorem scalar_identity_lie (c : ℝ) (A : Operator) :
    ⁅c • (1 : Operator), A⁆ = 0 := by
  rw [← lie_skew]
  simp only [lie_scalar_identity, neg_zero]

/-- Coordinate directions recover the coordinate partial operators exactly. -/
@[simp] theorem coordinate_directionalDerivative (i : Fin 3) :
    directionalDerivative (coordinateVector i) = partialDerivative i := by
  simp [directionalDerivative, coordinateVector, Pi.single_apply, ite_smul]

/-- Iteration of the covariant adjoint on multipliers is genuine repeated
    ordinary directional differentiation. -/
theorem ad_directionD_pow_multiplication (f : Fin 3 → Smooth) (v : State)
    (u : Smooth) (n : ℕ) :
    ((LieAlgebra.ad ℝ Operator (directionD f v)) ^ n) (multiplication u) =
      multiplication ((directionalDerivative v ^ n) u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Wong.AdjointIteration.end_pow_succ_apply, ih, LieAlgebra.ad_apply,
      lie_directionD_multiplication, Wong.AdjointIteration.end_pow_succ_apply]

/-- Powers of the actual generator adjoint remain in the generated algebra. -/
theorem ad_L0_pow_mem_estimationAlgebra {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) {A : Operator} (hA : A ∈ estimationAlgebra f h) (n : ℕ) :
    ((LieAlgebra.ad ℝ Operator (L0 f h)) ^ n) A ∈ estimationAlgebra f h := by
  have hL : L0 f h ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  induction n with
  | zero => simpa using hA
  | succ n ih =>
    rw [Wong.AdjointIteration.end_pow_succ_apply, LieAlgebra.ad_apply]
    exact (estimationAlgebra f h).lie_mem hL ih

/-- A common finite differential-order bound forces all smooth function
    elements to have one uniformly vanishing directional derivative order. -/
theorem function_elements_uniform_directional_nilpotence {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    ∃ k : ℕ, 0 < k ∧ ∀ u : Smooth, multiplication u ∈ estimationAlgebra f h →
      ∀ v : State, (directionalDerivative v ^ k) u = 0 := by
  obtain ⟨N, hN⟩ := estimationAlgebra_uniform_order_bound f h
  refine ⟨N + 1, Nat.zero_lt_succ N, ?_⟩
  intro u hu v
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
  have hδu : δ (multiplication u) = 0 := by
    exact lie_multiplication_multiplication u (linearFunction v)
  have hz : (δ ^ (N + 1)) ((T ^ (N + 1)) (multiplication u)) = 0 := by
    rw [Module.End.pow_apply]
    apply iterate_commuteWithMultiplier_eq_zero
    apply hN
    exact ad_L0_pow_mem_estimationAlgebra f h hu (N + 1)
  have hH := Wong.AdjointIteration.extracted_power_zero δ T H hDT hDH
    (multiplication u) hδu (N + 1) hz
  apply multiplication_injective
  rw [multiplication_zero, ← ad_directionD_pow_multiplication f v u (N + 1)]
  exact hH

/-- The coordinate-specialized vanishing statement needed to reconstruct
    function elements as genuine multivariate polynomials. -/
theorem function_elements_uniform_partial_nilpotence {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    ∃ k : ℕ, 0 < k ∧ ∀ u : Smooth, multiplication u ∈ estimationAlgebra f h →
      ∀ i : Fin 3, (partialDerivative i ^ k) u = 0 := by
  obtain ⟨k, hk, hderiv⟩ := function_elements_uniform_directional_nilpotence f h
  refine ⟨k, hk, ?_⟩
  intro u hu i
  simpa only [coordinate_directionalDerivative] using hderiv u hu (coordinateVector i)

end Wong.SmoothModel
