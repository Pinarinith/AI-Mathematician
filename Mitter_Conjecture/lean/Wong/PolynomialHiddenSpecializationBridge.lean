import Wong.PolynomialHiddenSpecialization

/-! Polynomial restriction is the actual state-coordinate slice, and fixes
every polynomial with vanishing hidden derivative. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

theorem eval_polynomialHiddenSpecialization (t : ℝ) (p : RealPoly) (x : State) :
    eval x (polynomialHiddenSpecialization t p) = eval ![x 0, x 1, t] p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, polynomialHiddenSpecialization_X]
    fin_cases i <;> simp

theorem polynomialHiddenSpecialization_eq_self_of_hidden_partial_zero
    (t : ℝ) (p : RealPoly) (hp : pderiv 2 p = 0) :
    polynomialHiddenSpecialization t p = p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs₂ : s 2 = 0 := by
    by_contra hn
    exact (mem_support_iff.mp hs)
      (polynomial_coeff_zero_of_partial_zero p 2 hp s (by omega))
  rw [polynomialHiddenSpecialization_monomial, monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_three, hs₂, pow_zero, mul_one]
  ring

end Wong.SmoothModel

#print axioms Wong.SmoothModel.polynomialHiddenSpecialization_eq_self_of_hidden_partial_zero
