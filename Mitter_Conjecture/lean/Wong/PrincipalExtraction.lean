import Wong.AdjointIteration

/-!
# Extraction from a first-order seed

Unlike the multiplier seed, the first-order seed need not be killed by `δ`.
It suffices that `δ² v = 0`. One extra multiplier commutator then extracts
the directional derivatives of its principal coefficient. No commutation
between `T` and `H` is assumed.
-/

noncomputable section
namespace Wong.PrincipalExtraction
open Wong.AdjointIteration

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

theorem overdiagonal_zero (δ T H : Module.End ℝ M)
    (hDT : ∀ v, δ (T v) = T (δ v) + H v)
    (hDH : ∀ v, δ (H v) = H (δ v))
    (v : M) (hv : (δ ^ 2) v = 0) (n : ℕ) :
    (δ ^ (n + 2)) ((T ^ n) v) = 0 := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [end_pow_succ_apply T n, power_T δ T H hDT hDH (n + 2)]
    rw [end_pow_succ_apply δ (n + 2), ih]
    simp

/-- Exact all-orders extraction of a first-order seed. -/
theorem diagonal_power (δ T H : Module.End ℝ M)
    (hDT : ∀ v, δ (T v) = T (δ v) + H v)
    (hDH : ∀ v, δ (H v) = H (δ v))
    (v : M) (hv : (δ ^ 2) v = 0) (n : ℕ) :
    (δ ^ (n + 1)) ((T ^ n) v) =
      ((n + 1).factorial : ℝ) • ((H ^ n) (δ v)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [end_pow_succ_apply T n, power_T δ T H hDT hDH (n + 1)]
    rw [overdiagonal_zero δ T H hDT hDH v hv n, map_zero, zero_add, ih,
      map_smul, smul_smul, end_pow_succ_apply H n]
    congr 1
    simp [Nat.factorial_succ]

theorem extracted_power_zero (δ T H : Module.End ℝ M)
    (hDT : ∀ v, δ (T v) = T (δ v) + H v)
    (hDH : ∀ v, δ (H v) = H (δ v))
    (v : M) (hv : (δ ^ 2) v = 0) (n : ℕ)
    (hz : (δ ^ (n + 1)) ((T ^ n) v) = 0) : (H ^ n) (δ v) = 0 := by
  rw [diagonal_power δ T H hDT hDH v hv n] at hz
  have hn : ((n + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
  have h := congrArg (fun z : M => ((n + 1).factorial : ℝ)⁻¹ • z) hz
  simpa [smul_smul, hn] using h

end Wong.PrincipalExtraction
