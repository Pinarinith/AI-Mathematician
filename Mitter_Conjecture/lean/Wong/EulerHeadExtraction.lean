import Wong.EulerSpectral

/-!
# Actual extraction of the pure hidden second derivative

The remainder may have arbitrary visible differential order, but its hidden
derivative index is at most one. Hidden polynomiality is discharged by the
actual finite Euler module theorem, rather than assumed in the final result.
-/
noncomputable section
namespace Wong.SmoothModel
open Polynomial
set_option maxHeartbeats 1000000

theorem partialDerivative_pow_mem_orderSpace (i : Fin 3) (n : ℕ) :
    partialDerivative i ^ n ∈ orderSpace n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    rw [← multiplication_smoothOne]
    exact multiplication_mem_orderSpace_zero _
  | succ n ih =>
    simpa only [pow_succ', Nat.add_comm 1 n] using
      mul_mem_orderSpace (partialDerivative_mem_orderSpace_one i) ih

/-- The normal form of a pure hidden derivative with constant scalar coefficient. -/
def normalHiddenHead (n : ℕ) (c : ℝ) : NormalForm :=
  Finsupp.single (Finsupp.single 2 n) (c • smoothOne)

@[simp] theorem normalAction_hiddenHead (n : ℕ) (c : ℝ) :
    normalAction (normalHiddenHead n c) = c • partialDerivative 2 ^ n := by
  simp only [normalHiddenHead, normalAction_single, multiplication_smul,
    multiplication_smoothOne, smul_mul_assoc, one_mul]
  congr 1
  simp [multiPartial]

theorem normalHiddenHead_hidden_independent (n : ℕ) (c : ℝ) (α : MultiIndex) :
    partialDerivative 2 (normalHiddenHead n c α) = 0 := by
  classical
  have hOne : partialDerivative 2 smoothOne = 0 := by
    simpa only [one_smul] using partialDerivative_const 2 1
  simp [normalHiddenHead, Finsupp.single_apply, apply_ite, hOne]

/-- Removing a hidden-independent normal form from an algebra element
preserves the common hidden polynomiality established by the Euler bridge. -/
theorem euler_remainder_hidden_nilpotence (E : LieSubalgebra ℝ Operator)
    [FiniteDimensional ℝ E] (hfinite : E ≤ finiteOrderAlgebra)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (core r : NormalForm) (hcore : ∀ α, partialDerivative 2 (core α) = 0)
    (hP : normalAction (core + r) ∈ E) :
    ∃ n, ∀ α, (partialDerivative 2 ^ n) (r α) = 0 := by
  obtain ⟨n, hn⟩ := finiteOrderLieAlgebra_uniform_hidden_nilpotence E hfinite B hB hJ
  have hp := hn (core + r) hP
  refine ⟨n + 1, ?_⟩
  intro α
  have hbig := end_power_zero_mono (partialDerivative 2) ((core + r) α)
    (Nat.le_succ n) (hp α)
  have hsmall := end_power_zero_mono (partialDerivative 2) (core α)
    (show 1 ≤ n + 1 by omega) (by simpa only [pow_one] using hcore α)
  simpa only [Finsupp.add_apply, map_add, hsmall, zero_add] using hbig

/-- A finite-order remainder with hidden index at most one has no weight
minus two; its actual spectral decomposition therefore isolates the pure head. -/
theorem hidden_second_head_mem_of_polynomial_remainder
    (E : LieSubalgebra ℝ Operator) (hfinite : E ≤ finiteOrderAlgebra)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (r : NormalForm) (n : ℕ)
    (hpoly : ∀ α, (partialDerivative 2 ^ n) (r α) = 0)
    (hr : ∀ α, 1 < α 2 → r α = 0) (c : ℝ)
    (hP : c • partialDerivative 2 ^ 2 + normalAction r ∈ E) :
    c • partialDerivative 2 ^ 2 ∈ E := by
  classical
  let s := normalEulerWeights n 1
  have hnots : (-2 : ℤ) ∉ s := by
    intro hw
    have hb := normalEulerWeights_lower_bound n 1 (-2) hw
    norm_num at hb
  have hann := normalEuler_integer_annihilator_with_bound r n 1 hpoly hr
  obtain ⟨q, hsum, heigen⟩ := Wong.EulerSpectral.integer_spectral_decomposition
    (LieAlgebra.ad ℝ Operator hiddenEuler) s (normalAction r) hann
  let wpart : ℤ → Operator := fun w =>
    if w = -2 then c • partialDerivative 2 ^ 2
    else (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) (q w)) (normalAction r)
  have hsum' : (∑ w ∈ insert (-2) s, wpart w) =
      c • partialDerivative 2 ^ 2 + normalAction r := by
    rw [Finset.sum_insert hnots]
    have heach : (∑ w ∈ s, wpart w) =
        ∑ w ∈ s, (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) (q w)) (normalAction r) := by
      apply Finset.sum_congr rfl
      intro w hw
      simp only [wpart, ite_eq_right_iff]
      intro he
      exact False.elim (hnots (he ▸ hw))
    rw [heach, hsum]
    simp [wpart]
  have heigen' (w : ℤ) (hw : w ∈ insert (-2) s) :
      ⁅hiddenEuler, wpart w⁆ = (w : ℝ) • wpart w := by
    rcases Finset.mem_insert.mp hw with hw | hw
    · subst w
      simp only [wpart, ite_true, lie_smul]
      rw [euler_lie_pow hiddenEuler (partialDerivative 2) (-1) (by simp) 2]
      norm_num
      module
    · have hwne : w ≠ -2 := fun he => hnots (he ▸ hw)
      simpa only [wpart, ite_eq_right hwne, LieAlgebra.ad_apply] using heigen w hw
  have hheadfinite : c • partialDerivative 2 ^ 2 ∈ finiteOrderAlgebra :=
    finiteOrderAlgebra.smul_mem c ⟨2, partialDerivative_pow_mem_orderSpace 2 2⟩
  have hrfinite : normalAction r ∈ finiteOrderAlgebra := by
    have hh := finiteOrderAlgebra.sub_mem (hfinite hP) hheadfinite
    simpa only [add_sub_cancel_left] using hh
  have hfinite' (w : ℤ) (_hw : w ∈ insert (-2) s) : wpart w ∈ finiteOrderAlgebra := by
    by_cases hw2 : w = -2
    · simpa only [wpart, ite_eq_left hw2] using hheadfinite
    · simpa only [wpart, ite_eq_right hw2] using
        hiddenEuler_polynomial_mem_finiteOrderAlgebra (q w) (normalAction r) hrfinite
  have hmem : (∑ w ∈ insert (-2) s, wpart w) ∈ E := by rwa [hsum']
  obtain ⟨Q, hQ, hQE⟩ := actual_euler_weight_projection E B hB hJ
    (insert (-2) s) wpart heigen' hfinite' hmem (-2) (Finset.mem_insert_self _ _)
  simpa only [wpart, ite_true] using hQE

/-- The genuine Sector-I minus-two projection. All hidden polynomiality
needed for the projection is derived from finite dimensionality and J. -/
theorem hidden_second_derivative_mem (E : LieSubalgebra ℝ Operator)
    [FiniteDimensional ℝ E] (hfinite : E ≤ finiteOrderAlgebra)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (r : NormalForm) (hr : ∀ α, 1 < α 2 → r α = 0)
    (c : ℝ) (hc : c ≠ 0)
    (hP : c • partialDerivative 2 ^ 2 + normalAction r ∈ E) :
    partialDerivative 2 ^ 2 ∈ E := by
  have hnormal : normalAction (normalHiddenHead 2 c + r) ∈ E := by
    simpa only [map_add, normalAction_hiddenHead] using hP
  obtain ⟨n, hn⟩ := euler_remainder_hidden_nilpotence E hfinite B hB hJ
    (normalHiddenHead 2 c) r (normalHiddenHead_hidden_independent 2 c) hnormal
  have hhead := hidden_second_head_mem_of_polynomial_remainder E hfinite B hB hJ r n hn hr c hP
  have hscaled := E.smul_mem c⁻¹ hhead
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hscaled

end Wong.SmoothModel
