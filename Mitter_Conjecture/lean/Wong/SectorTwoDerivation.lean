import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The sector-II polynomial derivation never kills the visible momentum

This proves an algebraic part of the manuscript directly, without assuming
existence of integral curves or a Wronskian representation.  The derivation
acts on the actual multivariate polynomial ring in `x,t,ξ,ζ`.  When the
quadratic coefficient is nonzero, a polynomial substitution restricts it
to the rational hidden trajectory, and a two-coefficient recurrence proves
nonvanishing at every iterate.  The connection to the highest-weight part
of the actual smooth differential-operator Lie words is a separate task.
-/

noncomputable section
namespace Wong.SectorTwo
open MvPolynomial

abbrev Symbols := MvPolynomial (Fin 4) ℝ
abbrev Restricted := MvPolynomial (Fin 3) ℝ

/-- Variable order: visible position, hidden position, visible momentum,
hidden momentum. -/
def dynamics (a k : ℝ) : Derivation ℝ Symbols Symbols :=
  mkDerivation ℝ ![X 2, X 3 - C a * X 1 ^ 2,
    C k * X 0 * X 3, C (2 * a) * X 1 * X 3]

/-- Identification with the four formal partial derivatives in the paper. -/
theorem dynamics_apply (a k : ℝ) (p : Symbols) :
    dynamics a k p = X 2 * pderiv 0 p + (X 3 - C a * X 1 ^ 2) * pderiv 1 p +
      C k * X 0 * X 3 * pderiv 2 p + C (2 * a) * X 1 * X 3 * pderiv 3 p := by
  let D : Derivation ℝ Symbols Symbols :=
    (X 2 : Symbols) • pderiv 0 + (X 3 - C a * X 1 ^ 2 : Symbols) • pderiv 1 +
      (C k * X 0 * X 3 : Symbols) • pderiv 2 +
      (C (2 * a) * X 1 * X 3 : Symbols) • pderiv 3
  have hd : dynamics a k = D := by
    apply derivation_ext
    intro i
    fin_cases i <;> simp [dynamics, D, smul_eq_mul]
  exact congrArg (fun d : Derivation ℝ Symbols Symbols => d p) hd

/-- Variable order: visible position, visible momentum, reciprocal time. -/
def restrictedDynamics (c : ℝ) : Derivation ℝ Restricted Restricted :=
  mkDerivation ℝ ![X 1, C c * X 2 ^ 2 * X 0, -(X 2 ^ 2)]

def trajectory (a : ℝ) : Symbols →ₐ[ℝ] Restricted :=
  aeval ![X 0, C (-1 / a) * X 2, X 1, C (2 / a) * X 2 ^ 2]

/-- Derivations intertwine on every polynomial once they intertwine on
the variables.  This is the full polynomial induction, not an assumed
chain rule for the substitution used below. -/
theorem derivation_intertwines {ι κ : Type*}
    (D : Derivation ℝ (MvPolynomial ι ℝ) (MvPolynomial ι ℝ))
    (E : Derivation ℝ (MvPolynomial κ ℝ) (MvPolynomial κ ℝ))
    (φ : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial κ ℝ)
    (hX : ∀ i, φ (D (X i)) = E (φ (X i)))
    (p : MvPolynomial ι ℝ) : φ (D p) = E (φ p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [derivation_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

theorem trajectory_intertwines (a k : ℝ) (ha : a ≠ 0) (p : Symbols) :
    trajectory a (dynamics a k p) =
      restrictedDynamics (2 * k / a) (trajectory a p) := by
  apply derivation_intertwines
  intro i
  fin_cases i <;>
    simp [dynamics, restrictedDynamics, trajectory, Derivation.leibniz,
      Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, derivation_C]
  · have hr : 2 / a - a * (-1 / a) ^ 2 = -(-1 / a) := by
      field_simp
      ring
    have he := congrArg (fun r : ℝ => C r * X 2 ^ 2 : ℝ → Restricted) hr
    simp only [map_sub, map_mul, map_pow, map_neg] at he
    simp only [div_eq_mul_inv, map_mul, map_neg, map_ofNat] at he ⊢
    convert he using 1 <;> ring
  · simp only [div_eq_mul_inv, map_mul, map_ofNat]
    ring
  · have hr : (2 * a) * (-1 / a) * (2 / a) = -(2 / a) * 2 := by
      field_simp
    have he := congrArg (fun r : ℝ => C r * X 2 ^ 3 : ℝ → Restricted) hr
    simp only [map_mul, map_neg, map_ofNat] at he
    simp only [div_eq_mul_inv, map_mul, map_neg, map_ofNat] at he ⊢
    convert he using 1 <;> ring

/-- Coefficients after removing the alternating signs. -/
def coefficients (c : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | n + 1 =>
    (((n + 1 : ℕ) : ℝ) * (coefficients c n).1 + c * (coefficients c n).2,
      (coefficients c n).1 + (n : ℝ) * (coefficients c n).2)

theorem coefficients_nonnegative (c : ℝ) (hc : 0 < c) (n : ℕ) :
    0 ≤ (coefficients c n).1 ∧ 0 ≤ (coefficients c n).2 := by
  induction n with
  | zero => norm_num [coefficients]
  | succ n ih =>
    obtain ⟨hu, hv⟩ := ih
    constructor <;> dsimp only [coefficients] <;> positivity

theorem coefficients_first_positive (c : ℝ) (hc : 0 < c) (n : ℕ) :
    0 < (coefficients c (n + 1)).1 := by
  induction n with
  | zero => simpa [coefficients] using hc
  | succ n ih =>
    have hn := coefficients_nonnegative c hc (n + 1)
    dsimp [coefficients]
    have hpos : (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by positivity
    have hp := mul_pos hpos ih
    have hq := mul_nonneg hc.le hn.2
    exact add_pos_of_pos_of_nonneg hp hq

theorem coefficients_nonzero (c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    (coefficients c n).1 ≠ 0 ∨ (coefficients c n).2 ≠ 0 := by
  by_cases hpos : 0 < c
  · cases n with
    | zero => simp [coefficients]
    | succ n => exact Or.inl (ne_of_gt (coefficients_first_positive c hpos n))
  · have hneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hc
    induction n with
    | zero => simp [coefficients]
    | succ n ih =>
      by_contra h
      push Not at h
      have h₁ : (((n + 1 : ℕ) : ℝ) * (coefficients c n).1 +
          c * (coefficients c n).2) = 0 := h.1
      have h₂ : (coefficients c n).1 + (n : ℝ) * (coefficients c n).2 = 0 := h.2
      have hdet : (n : ℝ) * (n + 1) - c ≠ 0 := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hp : (0 : ℝ) ≤ (n : ℝ) * (n + 1) := by positivity
        linarith
      have hv : (coefficients c n).2 = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left hdet
        push_cast at h₁
        nlinarith [h₁, h₂]
      have hu : (coefficients c n).1 = 0 := by simpa [hv] using h₂
      exact ih.elim (fun h => h hu) (fun h => h hv)

def restrictedWord (c : ℝ) (n : ℕ) : Restricted :=
  C ((-1 : ℝ) ^ (n + 1) * (coefficients c n).1) * X 2 ^ (n + 1) * X 0 +
    C ((-1 : ℝ) ^ n * (coefficients c n).2) * X 2 ^ n * X 1

theorem restrictedWord_zero (c : ℝ) : restrictedWord c 0 = X 1 := by
  simp [restrictedWord, coefficients]

theorem restrictedWord_step (c : ℝ) (n : ℕ) :
    restrictedDynamics c (restrictedWord c n) = restrictedWord c (n + 1) := by
  simp only [restrictedWord, restrictedDynamics, coefficients, map_add,
    Derivation.leibniz, Derivation.leibniz_pow, derivation_C,
    mkDerivation_X, smul_eq_mul, nsmul_eq_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    mul_zero, add_zero, Nat.add_sub_cancel]
  simp only [map_mul, map_add, map_pow, map_neg, map_one, pow_succ, Nat.cast_add,
    Nat.cast_one]
  cases n with
  | zero => norm_num; ring
  | succ n => simp [Nat.cast_add, pow_succ, map_add, map_natCast]; ring

theorem restrictedWord_eq_iterate (c : ℝ) (n : ℕ) :
    (restrictedDynamics c)^[n] (X 1) = restrictedWord c n := by
  induction n with
  | zero => exact (restrictedWord_zero c).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, restrictedWord_step]

theorem restrictedWord_nonzero (c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    restrictedWord c n ≠ 0 := by
  intro h
  have hu := congrArg (eval ![1, 0, 1]) h
  have hv := congrArg (eval ![0, 1, 1]) h
  simp [restrictedWord] at hu hv
  exact (coefficients_nonzero c hc n).elim (fun hn => hn hu) (fun hn => hn hv)

theorem trajectory_iterate (a k : ℝ) (ha : a ≠ 0) (n : ℕ) (p : Symbols) :
    trajectory a ((dynamics a k)^[n] p) =
      (restrictedDynamics (2 * k / a))^[n] (trajectory a p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', trajectory_intertwines a k ha, ih,
      Function.iterate_succ_apply']

theorem momentum_iterates_nonzero_of_quadratic (a k : ℝ)
    (ha : a ≠ 0) (hk : k ≠ 0) (n : ℕ) :
    (dynamics a k)^[n] (X 2) ≠ 0 := by
  intro h
  have hh := congrArg (trajectory a) h
  rw [trajectory_iterate a k ha] at hh
  have hvar : trajectory a (X 2) = X 1 := by simp [trajectory]
  rw [hvar, restrictedWord_eq_iterate, map_zero] at hh
  exact restrictedWord_nonzero (2 * k / a)
    (div_ne_zero (mul_ne_zero (by norm_num) hk) ha) n hh

/-- With zero quadratic coefficient, the hidden momentum is invariant. -/
theorem zero_quadratic_even_step (k : ℝ) (n : ℕ) :
    dynamics 0 k ((C k * X 3) ^ n * X 2) =
      (C k * X 3) ^ (n + 1) * X 0 := by
  simp [dynamics, Derivation.leibniz, Derivation.leibniz_pow,
    derivation_C, smul_eq_mul, pow_succ]
  ring

theorem zero_quadratic_odd_step (k : ℝ) (n : ℕ) :
    dynamics 0 k ((C k * X 3) ^ n * X 0) =
      (C k * X 3) ^ n * X 2 := by
  simp [dynamics, Derivation.leibniz, Derivation.leibniz_pow,
    derivation_C, smul_eq_mul]

theorem zero_quadratic_even_iterates (k : ℝ) (n : ℕ) :
    (dynamics 0 k)^[2 * n] (X 2) = (C k * X 3) ^ n * X 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      zero_quadratic_even_step, zero_quadratic_odd_step]

theorem zero_quadratic_odd_iterates (k : ℝ) (n : ℕ) :
    (dynamics 0 k)^[2 * n + 1] (X 2) = (C k * X 3) ^ (n + 1) * X 0 := by
  rw [Function.iterate_succ_apply', zero_quadratic_even_iterates,
    zero_quadratic_even_step]

theorem momentum_iterates_nonzero_of_zero_quadratic (k : ℝ)
    (hk : k ≠ 0) (n : ℕ) : (dynamics 0 k)^[n] (X 2) ≠ 0 := by
  have hc : (C k * X 3 : Symbols) ≠ 0 := mul_ne_zero (C_ne_zero.mpr hk) (X_ne_zero 3)
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n
  · rw [hr, zero_quadratic_even_iterates]
    exact mul_ne_zero (pow_ne_zero _ hc) (X_ne_zero 2)
  · rw [hr, zero_quadratic_odd_iterates]
    exact mul_ne_zero (pow_ne_zero _ hc) (X_ne_zero 0)

/-- The complete all-orders nonvanishing statement for the precise
sector-II highest-weight derivation, for every real quadratic coefficient. -/
theorem momentum_iterates_nonzero (a k : ℝ) (hk : k ≠ 0) (n : ℕ) :
    (dynamics a k)^[n] (X 2) ≠ 0 := by
  by_cases ha : a = 0
  · subst a
    exact momentum_iterates_nonzero_of_zero_quadratic k hk n
  · exact momentum_iterates_nonzero_of_quadratic a k ha hk n

end Wong.SectorTwo
