import Wong.PolynomialVisibleExtraction

/-! Restrict a genuine real polynomial to a fixed hidden-coordinate plane.
The total-degree bound and visible derivative identities are preserved. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

def polynomialHiddenSpecialization (t : ℝ) : RealPoly →ₐ[ℝ] RealPoly :=
  aeval ![X 0, X 1, C t]

@[simp] theorem polynomialHiddenSpecialization_C (t c : ℝ) :
    polynomialHiddenSpecialization t (C c) = C c := by
  simp [polynomialHiddenSpecialization, algebraMap_eq]

@[simp] theorem polynomialHiddenSpecialization_X (t : ℝ) (i : Fin 3) :
    polynomialHiddenSpecialization t (X i) = if i=2 then C t else X i := by
  fin_cases i <;> simp [polynomialHiddenSpecialization]

theorem polynomialHiddenSpecialization_monomial (t c : ℝ) (s : Fin 3 →₀ ℕ) :
    polynomialHiddenSpecialization t (monomial s c) =
      C (c * t^(s 2)) * X 0^(s 0) * X 1^(s 1) := by
  rw [polynomialHiddenSpecialization, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, algebraMap_eq, map_mul, map_pow]
  change C c * (X 0^(s 0) * X 1^(s 1) * C t^(s 2)) =
    C c * C t^(s 2) * X 0^(s 0) * X 1^(s 1)
  ring

theorem polynomialHiddenSpecialization_degree_le (t : ℝ) (p : RealPoly) :
    (polynomialHiddenSpecialization t p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => arg 1; rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro s hs
  rw [polynomialHiddenSpecialization_monomial]
  have hdeg : s 0 + s 1 ≤ s.degree := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
    omega
  calc
    _ ≤ (C (p.coeff s * t^(s 2)) * X 0^(s 0) : RealPoly).totalDegree +
        (X 1^(s 1) : RealPoly).totalDegree := totalDegree_mul _ _
    _ ≤ (C (p.coeff s * t^(s 2)) : RealPoly).totalDegree +
        (X 0^(s 0) : RealPoly).totalDegree + (X 1^(s 1) : RealPoly).totalDegree :=
      Nat.add_le_add_right (totalDegree_mul _ _) _
    _ = s 0 + s 1 := by simp only [totalDegree_C, totalDegree_X_pow, zero_add]
    _ ≤ p.totalDegree := hdeg.trans (le_totalDegree hs)

theorem polynomialHiddenSpecialization_visible_partial (t : ℝ) (p : RealPoly)
    (j : Fin 3) (hj : j ≠ 2) :
    pderiv j (polynomialHiddenSpecialization t p) =
      polynomialHiddenSpecialization t (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, pderiv_mul, polynomialHiddenSpecialization_X, hp]
    fin_cases i <;> fin_cases j <;> simp_all [pderiv_X]

theorem polynomialHiddenSpecialization_hidden_partial_zero (t : ℝ) (p : RealPoly) :
    pderiv 2 (polynomialHiddenSpecialization t p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    simp only [map_mul, pderiv_mul, hp, zero_mul, zero_add]
    fin_cases i <;> simp [pderiv_X]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.polynomialHiddenSpecialization_degree_le
#print axioms Wong.SmoothModel.polynomialHiddenSpecialization_visible_partial
