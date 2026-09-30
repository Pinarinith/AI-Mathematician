import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Exact iterated commutator extraction

If `δ T = T δ + H` and `δ H = H δ`, then on a vector killed by `δ`,
the diagonal iterate `δⁿ Tⁿ` is `n! Hⁿ`. No commutation of `H` with `T`
is required. This is the convention appropriate to `δ(A) = [A,M_linear]`.
For the left-adjoint convention, replace `H` by `-H`.
-/

noncomputable section
namespace Wong.AdjointIteration

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

theorem end_pow_succ_apply (A : Module.End ℝ M) (n : ℕ) (v : M) :
    (A ^ (n + 1)) v = A ((A ^ n) v) := by
  rw [pow_succ']
  rfl

/-- Commuting a power of `δ` through one occurrence of `T`. -/
theorem power_T (δ T H : Module.End ℝ M)
    (hDT : ∀ v, δ (T v) = T (δ v) + H v)
    (hDH : ∀ v, δ (H v) = H (δ v)) (k : ℕ) (v : M) :
    (δ ^ (k + 1)) (T v) =
      T ((δ ^ (k + 1)) v) + ((k + 1 : ℕ) : ℝ) • H ((δ ^ k) v) := by
  induction k with
  | zero => simpa using hDT v
  | succ k ih =>
    calc
      _ = δ ((δ ^ (k + 1)) (T v)) := end_pow_succ_apply δ (k + 1) (T v)
      _ = δ (T ((δ ^ (k + 1)) v) + ((k + 1 : ℕ) : ℝ) • H ((δ ^ k) v)) := by
        rw [ih]
      _ = T (δ ((δ ^ (k + 1)) v)) + H ((δ ^ (k + 1)) v) +
          ((k + 1 : ℕ) : ℝ) • H (δ ((δ ^ k) v)) := by
        rw [map_add, map_smul, hDT, hDH]
      _ = T ((δ ^ (k + 1 + 1)) v) +
          ((k + 1 + 1 : ℕ) : ℝ) • H ((δ ^ (k + 1)) v) := by
        rw [← end_pow_succ_apply δ (k + 1), ← end_pow_succ_apply δ k]
        simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
        abel

/-- One more multiplier commutator than generator commutators always annihilates the vector. -/
theorem overdiagonal_zero (δ T H : Module.End ℝ M)
    (hDT : ∀ v, δ (T v) = T (δ v) + H v)
    (hDH : ∀ v, δ (H v) = H (δ v))
    (v : M) (hv : δ v = 0) (n : ℕ) :
    (δ ^ (n + 1)) ((T ^ n) v) = 0 := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [end_pow_succ_apply T n, power_T δ T H hDT hDH (n + 1)]
    rw [end_pow_succ_apply δ (n + 1), ih]
    simp

/-- The factorial extraction identity, valid without `H T = T H`. -/
theorem diagonal_power (δ T H : Module.End ℝ M)
    (hDT : ∀ v, δ (T v) = T (δ v) + H v)
    (hDH : ∀ v, δ (H v) = H (δ v))
    (v : M) (hv : δ v = 0) (n : ℕ) :
    (δ ^ n) ((T ^ n) v) = (n.factorial : ℝ) • ((H ^ n) v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [end_pow_succ_apply T n, power_T δ T H hDT hDH n]
    rw [overdiagonal_zero δ T H hDT hDH v hv n, map_zero, zero_add, ih,
      map_smul, smul_smul, end_pow_succ_apply H n]
    congr 1
    simp [Nat.factorial_succ]

/-- If the outer commutator power vanishes, the extracted directional power vanishes. -/
theorem extracted_power_zero (δ T H : Module.End ℝ M)
    (hDT : ∀ v, δ (T v) = T (δ v) + H v)
    (hDH : ∀ v, δ (H v) = H (δ v))
    (v : M) (hv : δ v = 0) (n : ℕ)
    (hz : (δ ^ n) ((T ^ n) v) = 0) : (H ^ n) v = 0 := by
  rw [diagonal_power δ T H hDT hDH v hv n] at hz
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h := congrArg (fun z : M => (n.factorial : ℝ)⁻¹ • z) hz
  simpa [smul_smul, hn] using h

end Wong.AdjointIteration
