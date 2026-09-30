import Wong.EulerHiddenPolynomial

/-!
# The Euler bridge for genuine transformed Lie algebras

Gauge and orthogonal conjugation need not leave an algebra in the literal
`estimationAlgebra f h` presentation. The following entry points apply to
any actual finite-dimensional Lie subalgebra whose elements have finite
order; transformed-algebra containment can be discharged independently.
-/
noncomputable section
namespace Wong.SmoothModel
set_option maxHeartbeats 800000

theorem finiteOrderLieAlgebra_hiddenEuler_ad_common_annihilator
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E) :
    ∃ Q : Polynomial ℝ, Q ≠ 0 ∧ ∀ P ∈ E,
      (Polynomial.aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) P = 0 := by
  let T := LieAlgebra.ad ℝ Operator (hiddenEuler + multiplication B)
  let N := commuteWithMultiplier B
  have hTN : Commute T N := by
    dsimp [T, N]
    rw [right_multiplier_eq_neg_ad]
    exact (LieAlgebra.commute_ad_of_commute
      ((hiddenEuler_commute_multiplier B hB).add_left (Commute.refl _))).neg_right
  have hT : ∀ P ∈ E.toSubmodule, T P ∈ E.toSubmodule := by
    intro P hP
    exact E.lie_mem hJ hP
  obtain ⟨n, hn⟩ := finiteDimensional_uniform_order_bound E.toSubmodule (fun P hP => hfinite hP)
  have hN : ∀ P ∈ E.toSubmodule, (N ^ (n + 1)) P = 0 := by
    intro P hP
    simpa only [N, Module.End.pow_apply] using iterate_commuteWithMultiplier_eq_zero (hn hP) B
  have heq : T + N = LieAlgebra.ad ℝ Operator hiddenEuler := by
    apply LinearMap.ext
    intro P
    change ⁅hiddenEuler + multiplication B, P⁆ + ⁅P, multiplication B⁆ = ⁅hiddenEuler, P⁆
    rw [add_lie, ← lie_skew P (multiplication B)]
    abel
  obtain ⟨Q, hQ, hQP⟩ := Wong.EulerFiniteModule.common_annihilator_of_commuting_nilpotent
    T N hTN E.toSubmodule hT (n + 1) (Nat.succ_pos n) hN
  exact ⟨Q, hQ, fun P hP => by simpa only [heq] using hQP P hP⟩

/-- The globally uniform hidden derivative conclusion for an arbitrary
actual finite-order Lie algebra, including gauge-transformed algebras. -/
theorem finiteOrderLieAlgebra_uniform_hidden_nilpotence
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E) :
    ∃ N : ℕ, ∀ p : NormalForm, normalAction p ∈ E →
      ∀ α, (partialDerivative 2 ^ N) (p α) = 0 := by
  obtain ⟨Q, hQ, hkill⟩ := finiteOrderLieAlgebra_hiddenEuler_ad_common_annihilator E hfinite B hB hJ
  obtain ⟨N, hN⟩ := actual_uniform_hidden_degree_bound E.toSubmodule
  refine ⟨N, ?_⟩
  intro p hp
  exact hN p hp (fun α =>
    euler_annihilator_hidden_coefficient_nilpotence Q hQ p (hkill _ hp) α)

/-- Nonzero scaling of the Euler part is normalized inside the same actual
Lie algebra, with the potential rescaled by the reciprocal. -/
theorem normalized_hiddenEuler_mem (E : LieSubalgebra ℝ Operator)
    (c : ℝ) (hc : c ≠ 0) (B : Smooth)
    (hJ : c • hiddenEuler + multiplication B ∈ E) :
    hiddenEuler + multiplication (c⁻¹ • B) ∈ E := by
  have hscaled := E.smul_mem c⁻¹ hJ
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul,
    multiplication_smul] using hscaled

end Wong.SmoothModel
