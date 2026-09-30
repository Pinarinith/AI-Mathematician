import Wong.DirectionalExtraction
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Analytic and polynomial bridges for actual function elements

These lemmas concern genuine smooth functions, not formal generators.
The polynomiality theorem in one variable is proved from vanishing derivatives
using ordinary differentiation and the mean-value theorem.
-/

noncomputable section
namespace Wong.FunctionElements
open Polynomial
open scoped ContDiff

/-- A real polynomial has an antiderivative with the expected degree bound. -/
theorem exists_polynomial_antiderivative (p : ℝ[X]) :
    ∃ q : ℝ[X], q.derivative = p ∧ q.natDegree ≤ p.natDegree + 1 := by
  let q : ℝ[X] := ∑ j ∈ p.support,
    monomial (j + 1) (p.coeff j / (j + 1 : ℝ))
  refine ⟨q, ?_, ?_⟩
  · dsimp [q]
    rw [derivative_sum]
    simp only [derivative_monomial_succ]
    have hc : ∀ j : ℕ, p.coeff j / (j + 1 : ℝ) * (j + 1 : ℝ) = p.coeff j := by
      intro j
      exact div_mul_cancel₀ _ (by positivity)
    simp_rw [hc]
    exact p.sum_monomial_eq
  · apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans
      (Nat.add_le_add_right (le_natDegree_of_mem_supp j hj) 1)

/-- Global smooth functions with vanishing `(n+1)`st derivative are actual
polynomial functions of degree at most `n`. -/
theorem polynomial_of_iteratedDeriv_eq_zero (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hz : iteratedDeriv (n + 1) f = 0) :
    ∃ p : ℝ[X], p.natDegree ≤ n ∧ ∀ x, p.eval x = f x := by
  induction n generalizing f with
  | zero =>
    refine ⟨C (f 0), by simp, ?_⟩
    intro x
    simp only [eval_C]
    apply is_const_of_deriv_eq_zero (hf.differentiable (by simp)) _ 0 x
    intro y
    have hy := congrFun hz y
    simpa only [Nat.zero_add, iteratedDeriv_one, Pi.zero_apply] using hy
  | succ n ih =>
    have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
    have hzd : iteratedDeriv (n + 1) (deriv f) = 0 := by
      simpa only [iteratedDeriv_succ'] using hz
    obtain ⟨p, hp, he⟩ := ih (deriv f) hd hzd
    obtain ⟨q, hq, hqd⟩ := exists_polynomial_antiderivative p
    refine ⟨q + C (f 0 - q.eval 0),
      natDegree_add_le_of_degree_le (hqd.trans (Nat.add_le_add_right hp 1)) (by simp), ?_⟩
    have hc : ∀ x, f x - q.eval x = f 0 - q.eval 0 := by
      intro x
      apply is_const_of_deriv_eq_zero
        ((hf.differentiable (by simp)).sub q.differentiable) _ x 0
      intro y
      rw [deriv_sub ((hf.differentiable (by simp)).differentiableAt)
        q.differentiableAt, Polynomial.deriv, hq, he, sub_self]
    intro x
    simp only [eval_add, eval_C]
    linarith [hc x]

/-- Uniformly bounded univariate polynomials are determined by a fixed finite grid. -/
theorem polynomial_interpolation_formula (n : ℕ) (f : ℝ → ℝ)
    (hf : ∃ p : ℝ[X], p.natDegree ≤ n ∧ ∀ x, p.eval x = f x) (x : ℝ) :
    f x = ∑ j ∈ Finset.range (n + 1), f (j : ℝ) *
      (Lagrange.basis (Finset.range (n + 1)) (fun j : ℕ => (j : ℝ)) j).eval x := by
  obtain ⟨p, hp, he⟩ := hf
  have hi : Set.InjOn (fun j : ℕ => (j : ℝ)) (Finset.range (n + 1)) := by
    intro i _ j _ hij
    exact Nat.cast_injective hij
  have hd : p.degree < ↑(Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt (degree_le_natDegree (p := p))
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hp))
  have h := congrArg (fun q : ℝ[X] => q.eval x) (Lagrange.eq_interpolate hi hd)
  simpa only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, he] using h

/-- Substitute a single coordinate into an ordinary polynomial. -/
def coordinatePolynomial (i : Fin 3) (p : ℝ[X]) : MvPolynomial (Fin 3) ℝ :=
  p.eval₂ MvPolynomial.C (MvPolynomial.X i)

@[simp] theorem eval_coordinatePolynomial (i : Fin 3) (p : ℝ[X]) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (coordinatePolynomial i p) = p.eval (x i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [coordinatePolynomial, Polynomial.eval₂_add,
      map_add, Polynomial.eval_add] at *; rw [hp, hq]
  | monomial j a => simp [coordinatePolynomial, Polynomial.eval₂_monomial]

theorem totalDegree_coordinatePolynomial (i : Fin 3) (p : ℝ[X]) :
    (coordinatePolynomial i p).totalDegree ≤ p.natDegree := by
  unfold coordinatePolynomial
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa using Polynomial.le_natDegree_of_mem_supp j hj)

def lagrangeFactor (n j : ℕ) (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  coordinatePolynomial i
    (Lagrange.basis (Finset.range (n + 1)) (fun k : ℕ => (k : ℝ)) j)

theorem lagrangeFactor_degree (n j : ℕ) (i : Fin 3) (hj : j ∈ Finset.range (n + 1)) :
    (lagrangeFactor n j i).totalDegree ≤ n := by
  apply (totalDegree_coordinatePolynomial i _).trans
  rw [Lagrange.natDegree_basis (by
    intro a _ b _ h; exact Nat.cast_injective h) hj, Finset.card_range]
  exact Nat.le_refl _

end Wong.FunctionElements

namespace Wong.SmoothModel
open scoped ContDiff

/-- Restrict an actual smooth function to a coordinate line. -/
def coordinateSlice (u : Smooth) (x : State) (i : Fin 3) : ℝ → ℝ :=
  fun t => u.1 (Function.update x i t)

theorem coordinateSlice_smooth (u : Smooth) (x : State) (i : Fin 3) :
    ContDiff ℝ ∞ (coordinateSlice u x i) :=
  (smooth u).comp (contDiff_update ∞ x i)

theorem deriv_coordinateSlice (u : Smooth) (x : State) (i : Fin 3) :
    deriv (coordinateSlice u x i) = coordinateSlice (partialDerivative i u) x i := by
  funext t
  exact (((smooth u).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    t (hasDerivAt_update x i t)).deriv

theorem iteratedDeriv_coordinateSlice (n : ℕ) (u : Smooth) (x : State) (i : Fin 3) :
    iteratedDeriv n (coordinateSlice u x i) =
      coordinateSlice ((partialDerivative i ^ n) u) x i := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ', deriv_coordinateSlice, ih, pow_succ]
    rfl

/-- The operator nilpotence statement from the finite-order argument yields
actual bounded-degree polynomials on each coordinate line. -/
theorem coordinateSlice_polynomial_of_nilpotent (n : ℕ) (u : Smooth)
    (hu : ∀ i, (partialDerivative i ^ (n + 1)) u = 0) (x : State) (i : Fin 3) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧ ∀ t, p.eval t = coordinateSlice u x i t := by
  apply Wong.FunctionElements.polynomial_of_iteratedDeriv_eq_zero n _
    (coordinateSlice_smooth u x i)
  rw [iteratedDeriv_coordinateSlice, hu]
  rfl

open Wong.FunctionElements

/-- The exact interpolation formula on any coordinate line. -/
theorem coordinate_interpolation_of_nilpotent (n : ℕ) (u : Smooth)
    (hu : ∀ i, (partialDerivative i ^ (n + 1)) u = 0) (x : State) (i : Fin 3) :
    u.1 x = ∑ j ∈ Finset.range (n + 1),
      u.1 (Function.update x i (j : ℝ)) *
        MvPolynomial.eval x (lagrangeFactor n j i) := by
  have h := polynomial_interpolation_formula n (coordinateSlice u x i)
    (coordinateSlice_polynomial_of_nilpotent n u hu x i) (x i)
  simpa only [coordinateSlice, Function.update_eq_self, lagrangeFactor,
    eval_coordinatePolynomial] using h

/-- A fixed three-dimensional integer grid, independent of the evaluation point. -/
def interpolationGrid (a b c : ℕ) : State := ![(a : ℝ), (b : ℝ), (c : ℝ)]

theorem update_all_coordinates (x : State) (a b c : ℕ) :
    Function.update (Function.update (Function.update x 0 (a : ℝ)) 1 (b : ℝ)) 2 (c : ℝ) =
      interpolationGrid a b c := by
  funext i
  fin_cases i <;> simp [interpolationGrid]

/-- Tensor-product Lagrange interpolation is a genuine multivariate polynomial. -/
def tensorInterpolant (n : ℕ) (u : Smooth) : MvPolynomial (Fin 3) ℝ :=
  ∑ a ∈ Finset.range (n + 1),
    (∑ b ∈ Finset.range (n + 1),
      (∑ c ∈ Finset.range (n + 1),
        MvPolynomial.C (u.1 (interpolationGrid a b c)) * lagrangeFactor n c 2) *
      lagrangeFactor n b 1) * lagrangeFactor n a 0

theorem eval_tensorInterpolant (n : ℕ) (u : Smooth)
    (hu : ∀ i, (partialDerivative i ^ (n + 1)) u = 0) (x : State) :
    MvPolynomial.eval x (tensorInterpolant n u) = u.1 x := by
  have h2 (a b : ℕ) :
      (∑ c ∈ Finset.range (n + 1),
        u.1 (interpolationGrid a b c) * MvPolynomial.eval x (lagrangeFactor n c 2)) =
      u.1 (Function.update (Function.update x 0 (a : ℝ)) 1 (b : ℝ)) := by
    have h := (coordinate_interpolation_of_nilpotent n u hu
      (Function.update (Function.update x 0 (a : ℝ)) 1 (b : ℝ)) 2).symm
    simpa only [update_all_coordinates, lagrangeFactor, eval_coordinatePolynomial,
      Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide),
      Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)] using h
  have h1 (a : ℕ) :
      (∑ b ∈ Finset.range (n + 1),
        (∑ c ∈ Finset.range (n + 1),
          u.1 (interpolationGrid a b c) * MvPolynomial.eval x (lagrangeFactor n c 2)) *
          MvPolynomial.eval x (lagrangeFactor n b 1)) =
      u.1 (Function.update x 0 (a : ℝ)) := by
    simp_rw [h2]
    have h := (coordinate_interpolation_of_nilpotent n u hu
      (Function.update x 0 (a : ℝ)) 1).symm
    simpa only [lagrangeFactor, eval_coordinatePolynomial,
      Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide)] using h
  simp only [tensorInterpolant, map_sum, map_mul, MvPolynomial.eval_C]
  simp_rw [h1]
  exact (coordinate_interpolation_of_nilpotent n u hu x 0).symm

theorem totalDegree_tensorInterpolant (n : ℕ) (u : Smooth) :
    (tensorInterpolant n u).totalDegree ≤ 3 * n := by
  unfold tensorInterpolant
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a ha
  have h0 := lagrangeFactor_degree n a 0 ha
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have h1 : (∑ b ∈ Finset.range (n + 1),
      (∑ c ∈ Finset.range (n + 1),
        MvPolynomial.C (u.1 (interpolationGrid a b c)) * lagrangeFactor n c 2) *
      lagrangeFactor n b 1).totalDegree ≤ 2 * n := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro b hb
    have hb' := lagrangeFactor_degree n b 1 hb
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have h2 : (∑ c ∈ Finset.range (n + 1),
        MvPolynomial.C (u.1 (interpolationGrid a b c)) * lagrangeFactor n c 2).totalDegree ≤ n := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro c hc
      apply (MvPolynomial.totalDegree_mul _ _).trans
      simpa using lagrangeFactor_degree n c 2 hc
    omega
  omega

/-- The analytic operator condition supplies an actual polynomial expression,
with a uniform total-degree bound. -/
theorem polynomial_of_partial_nilpotent (n : ℕ) (u : Smooth)
    (hu : ∀ i, (partialDerivative i ^ (n + 1)) u = 0) :
    ∃ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ 3 * n ∧
      ∀ x : State, MvPolynomial.eval x p = u.1 x :=
  ⟨tensorInterpolant n u, totalDegree_tensorInterpolant n u, eval_tensorInterpolant n u hu⟩

/-- Ocone's polynomiality step for the genuine finite-dimensional estimation
algebra. The conclusion is proved from the original analytic assumptions. -/
theorem function_elements_uniform_polynomial_degree {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)] :
    ∃ N : ℕ, ∀ u : Smooth, multiplication u ∈ estimationAlgebra f h →
      ∃ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ N ∧
        ∀ x : State, MvPolynomial.eval x p = u.1 x := by
  obtain ⟨k, hk, hkz⟩ := function_elements_uniform_partial_nilpotence f h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk)
  exact ⟨3 * n, fun u hu => polynomial_of_partial_nilpotent n u (hkz u hu)⟩

end Wong.SmoothModel
