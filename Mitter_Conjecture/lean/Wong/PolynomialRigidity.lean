import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Polynomial rigidity used by the low-degree Sector II argument

This file proves the polynomial Wronskian step independently of the smooth
operator and integral-curve constructions. It does not assert that those
constructions or the complete Wong-matrix theorem have been formalized.
-/

namespace Wong
open Polynomial

variable {K : Type*} [Field K]

/-- A constant nonzero Wronskian forces the first polynomial's second
    derivative to vanish. No characteristic-zero hypothesis is needed here. -/
theorem second_derivative_eq_zero_of_wronskian_constant
    (p q : K[X]) {c : K} (hc : c ≠ 0)
    (hW : wronskian p q = C c) : p.derivative.derivative = 0 := by
  have hp : p ≠ 0 := by
    intro h
    have : (0 : K[X]) = C c := by simpa [h] using hW
    exact hc (by simpa using congrArg (fun r : K[X] => r.coeff 0) this.symm)
  have hRel : p * q.derivative.derivative = p.derivative.derivative * q := by
    have hd := congrArg derivative hW
    simp only [wronskian, derivative_sub, derivative_mul, derivative_C] at hd
    exact (sub_eq_zero.mp (by linear_combination hd))
  have hProd : C c * p.derivative.derivative =
      p * (q.derivative * p.derivative.derivative -
        p.derivative * q.derivative.derivative) := by
    rw [← hW, wronskian]
    calc
      (p * q.derivative - p.derivative * q) * p.derivative.derivative =
          p * q.derivative * p.derivative.derivative -
            p.derivative * (p.derivative.derivative * q) := by ring
      _ = p * q.derivative * p.derivative.derivative -
            p.derivative * (p * q.derivative.derivative) := by rw [← hRel]
      _ = p * (q.derivative * p.derivative.derivative -
            p.derivative * q.derivative.derivative) := by ring
  have hDvd : p ∣ p.derivative.derivative := by
    refine ⟨C c⁻¹ * (q.derivative * p.derivative.derivative -
      p.derivative * q.derivative.derivative), ?_⟩
    calc
      p.derivative.derivative = C c⁻¹ * (C c * p.derivative.derivative) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
      _ = C c⁻¹ * (p * (q.derivative * p.derivative.derivative -
            p.derivative * q.derivative.derivative)) := by rw [hProd]
      _ = p * (C c⁻¹ * (q.derivative * p.derivative.derivative -
            p.derivative * q.derivative.derivative)) := by ring
  exact eq_zero_of_dvd_of_degree_lt hDvd
    (lt_of_le_of_lt (degree_derivative_le (p := p.derivative)) (degree_derivative_lt hp))

/-- Both polynomial solutions have zero acceleration when their Wronskian
    is a nonzero constant. -/
theorem second_derivatives_eq_zero_of_wronskian_constant
    (p q : K[X]) {c : K} (hc : c ≠ 0)
    (hW : wronskian p q = C c) :
    p.derivative.derivative = 0 ∧ q.derivative.derivative = 0 := by
  constructor
  · exact second_derivative_eq_zero_of_wronskian_constant p q hc hW
  · apply second_derivative_eq_zero_of_wronskian_constant q p (neg_ne_zero.mpr hc)
    rw [← wronskian_neg_eq, hW, C_neg]

/-- In characteristic zero, both members of the fundamental pair are affine. -/
theorem natDegrees_le_one_of_wronskian_constant [CharZero K]
    (p q : K[X]) {c : K} (hc : c ≠ 0)
    (hW : wronskian p q = C c) : p.natDegree ≤ 1 ∧ q.natDegree ≤ 1 := by
  obtain ⟨hpp, hqq⟩ := second_derivatives_eq_zero_of_wronskian_constant p q hc hW
  constructor
  · have hd := (Polynomial.derivative_eq_zero.mp hpp)
    rw [natDegree_derivative] at hd
    exact Nat.sub_eq_zero_iff_le.mp hd
  · have hd := (Polynomial.derivative_eq_zero.mp hqq)
    rw [natDegree_derivative] at hd
    exact Nat.sub_eq_zero_iff_le.mp hd

/-- The nonzero constant Wronskian is an explicit constant-coefficient linear
    combination of the two polynomials. This avoids an implicit change of basis. -/
theorem constant_combination_of_wronskian_constant [CharZero K]
    (p q : K[X]) {c : K} (hc : c ≠ 0)
    (hW : wronskian p q = C c) :
    C (q.coeff 1) * p - C (p.coeff 1) * q = C c := by
  obtain ⟨hpp, hqq⟩ := second_derivatives_eq_zero_of_wronskian_constant p q hc hW
  have hp' : p.derivative = C (p.coeff 1) := by
    simpa [coeff_derivative] using eq_C_of_derivative_eq_zero hpp
  have hq' : q.derivative = C (q.coeff 1) := by
    simpa [coeff_derivative] using eq_C_of_derivative_eq_zero hqq
  simpa only [wronskian, hp', hq', mul_comm p] using hW

/-- The common acceleration coefficient in `u'' = z u` vanishes at each
    point if a polynomial fundamental pair has constant nonzero Wronskian.
    This is precisely the contradiction used along the manuscript's local
    hidden trajectory, without requiring the trajectory itself polynomial. -/
theorem pointwise_acceleration_eq_zero_of_wronskian_constant
    (p q : K[X]) {c : K} (hc : c ≠ 0)
    (hW : wronskian p q = C c) (a z : K)
    (hp : p.derivative.derivative.eval a = z * p.eval a)
    (hq : q.derivative.derivative.eval a = z * q.eval a) : z = 0 := by
  obtain ⟨hpp, hqq⟩ := second_derivatives_eq_zero_of_wronskian_constant p q hc hW
  by_contra hz
  have hp0 : p.eval a = 0 := by
    have : z * p.eval a = 0 := by simpa [hpp] using hp.symm
    exact (mul_eq_zero.mp this).resolve_left hz
  have hq0 : q.eval a = 0 := by
    have : z * q.eval a = 0 := by simpa [hqq] using hq.symm
    exact (mul_eq_zero.mp this).resolve_left hz
  have hval := congrArg (fun r : K[X] => r.eval a) hW
  simp only [wronskian, eval_sub, eval_mul, eval_C, hp0, hq0,
    zero_mul, mul_zero, sub_self] at hval
  exact hc hval.symm

end Wong
