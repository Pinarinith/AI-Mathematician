import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Verified algebraic components of the visible-entry argument

These theorems verify the coordinate normalization, the actual one-variable
polynomial recurrence underlying the homogeneous two-variable symbols, and
the mixed-derivative elimination. They do not assume the Wong constancy
conclusion. The passage from differential operators to these symbols and
the cited structure theorems are not formalized in this file.
-/

namespace Wong.Visible

noncomputable section

open Polynomial

/-- The last two differentiated visible-slot identities force the visible slope to vanish. -/
theorem singleAxisElimination (b k h l s : ℝ)
    (h₁ : 0 = -h * k - 2 * l ^ 2 + (1 / 2 : ℝ) * s)
    (h₂ : 0 = -4 * b ^ 2 - 4 * l ^ 2 - 2 * k * h + s) :
    b = 0 := by
  nlinarith [sq_nonneg b]

/-- The explicit orientation-preserving normalization sends the visible slope to the second axis. -/
theorem rotationSlope (b₁ b₂ ρ y₁ y₂ : ℝ) (hρ : ρ ≠ 0)
    (hsq : ρ ^ 2 = b₁ ^ 2 + b₂ ^ 2) :
    b₁ * ((b₂ * y₁ + b₁ * y₂) / ρ) +
        b₂ * ((-b₁ * y₁ + b₂ * y₂) / ρ) = ρ * y₂ := by
  calc
    _ = ((b₁ ^ 2 + b₂ ^ 2) * y₂) / ρ := by ring
    _ = (ρ ^ 2 * y₂) / ρ := by rw [hsq]
    _ = ρ * y₂ := by field_simp [hρ]

/-- The normalization has determinant one, so it preserves the visible two-form coefficient. -/
theorem rotationDet (b₁ b₂ ρ : ℝ) (hρ : ρ ≠ 0)
    (hsq : ρ ^ 2 = b₁ ^ 2 + b₂ ^ 2) :
    (b₂ / ρ) * (b₂ / ρ) - (b₁ / ρ) * (-b₁ / ρ) = 1 := by
  field_simp [hρ]
  nlinarith [hsq]

/-- The same normalization preserves the Euclidean quadratic form. -/
theorem rotationPreservesSquares (b₁ b₂ ρ y₁ y₂ : ℝ) (hρ : ρ ≠ 0)
    (hsq : ρ ^ 2 = b₁ ^ 2 + b₂ ^ 2) :
    ((b₂ * y₁ + b₁ * y₂) / ρ) ^ 2 +
        ((-b₁ * y₁ + b₂ * y₂) / ρ) ^ 2 = y₁ ^ 2 + y₂ ^ 2 := by
  calc
    _ = ((b₁ ^ 2 + b₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2)) / ρ ^ 2 := by ring
    _ = (ρ ^ 2 * (y₁ ^ 2 + y₂ ^ 2)) / ρ ^ 2 := by rw [hsq]
    _ = y₁ ^ 2 + y₂ ^ 2 := by field_simp [hρ]

/-- A nonzero slope vector has the strictly positive normalization parameter used above. -/
theorem existsNormalization (b₁ b₂ : ℝ) (h : b₁ ≠ 0 ∨ b₂ ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 = b₁ ^ 2 + b₂ ^ 2 := by
  have hpos : 0 < b₁ ^ 2 + b₂ ^ 2 := by
    rcases h with h | h
    · have : 0 < b₁ ^ 2 := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg b₂]
    · have : 0 < b₂ ^ 2 := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg b₁]
  exact ⟨Real.sqrt (b₁ ^ 2 + b₂ ^ 2), Real.sqrt_pos.2 hpos,
    Real.sq_sqrt (le_of_lt hpos)⟩

/-- A homogeneous symbol is encoded after factoring its power of `ξ₁` and setting `z = ξ₂/ξ₁`.
Only exponents zero, one, and two occur in `z`. No division is used in the proof. -/
structure Quad where
  c₀ : ℝ
  c₁ : ℝ
  c₂ : ℝ

def Quad.poly (q : Quad) : ℝ[X] :=
  C q.c₀ + C q.c₁ * X + C q.c₂ * X ^ 2

theorem Quad.coeff_two (q : Quad) : q.poly.coeff 2 = q.c₂ := by
  simp [Quad.poly]

/-- Exact coefficient action of `b (lam + γ z) d/dz`. -/
def Quad.step (b lam γ : ℝ) (q : Quad) : Quad where
  c₀ := b * lam * q.c₁
  c₁ := b * γ * q.c₁ + 2 * b * lam * q.c₂
  c₂ := 2 * b * γ * q.c₂

theorem Quad.step_poly (b lam γ : ℝ) (q : Quad) :
    (q.step b lam γ).poly = C b * (C lam + C γ * X) * derivative q.poly := by
  simp only [Quad.poly, Quad.step, derivative_add, derivative_C,
    derivative_C_mul_X, derivative_C_mul_X_sq, zero_add]
  simp only [map_add, map_mul, C_ofNat]
  ring

def visibleSymbols (b lam γ : ℝ) : ℕ → Quad
  | 0 => ⟨0, b * lam, b * γ⟩
  | n + 1 => (visibleSymbols b lam γ n).step b lam γ

/-- The tracked top coefficient is never contaminated by the other two slots. -/
theorem trackedCoefficient (b lam γ : ℝ) (n : ℕ) :
    (visibleSymbols b lam γ n).c₂ = 2 ^ n * (b * γ) ^ (n + 1) := by
  induction n with
  | zero => simp [visibleSymbols]
  | succ n ih =>
    simp only [visibleSymbols, Quad.step, ih, pow_succ]
    ring

theorem trackedCoefficient_ne_zero (b lam γ : ℝ) (hb : b ≠ 0) (hγ : γ ≠ 0)
    (n : ℕ) : (visibleSymbols b lam γ n).c₂ ≠ 0 := by
  rw [trackedCoefficient]
  exact mul_ne_zero (pow_ne_zero n (by norm_num))
    (pow_ne_zero (n + 1) (mul_ne_zero hb hγ))

theorem visibleSymbols_recurrence (b lam γ : ℝ) (n : ℕ) :
    (visibleSymbols b lam γ (n + 1)).poly =
      C b * (C lam + C γ * X) * derivative (visibleSymbols b lam γ n).poly := by
  exact Quad.step_poly b lam γ _

/-- Every iterate of the genuine polynomial recurrence is nonzero when the mixed slope is nonzero. -/
theorem visibleSymbols_poly_ne_zero (b lam γ : ℝ) (hb : b ≠ 0) (hγ : γ ≠ 0)
    (n : ℕ) : (visibleSymbols b lam γ n).poly ≠ 0 := by
  intro hzero
  have hc := congrArg (fun p : ℝ[X] => p.coeff 2) hzero
  rw [Quad.coeff_two, coeff_zero] at hc
  exact trackedCoefficient_ne_zero b lam γ hb hγ n hc

end

end Wong.Visible
