import Wong.PolynomialSmooth

/-! Subtracting the exact top homogeneous component lowers the genuine total
degree. The result includes all lower-degree coefficients, without approximation. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

theorem polynomial_sub_top_component_degree_le (p : RealPoly) (d : ℕ)
    (hd : 0 < d) (hp : p.totalDegree ≤ d) :
    (p - homogeneousComponent d p).totalDegree ≤ d-1 := by
  classical
  apply Finset.sup_le
  intro s hs
  have hcs := mem_support_iff.mp hs
  by_contra hnot
  change ¬ s.degree ≤ d-1 at hnot
  have hsd : d ≤ s.degree := by omega
  by_cases heq : s.degree = d
  · simp only [coeff_sub, coeff_homogeneousComponent, heq, ite_true, sub_self] at hcs
    exact hcs rfl
  · have hgt : p.totalDegree < s.degree := by omega
    have hz : p.coeff s = 0 := coeff_eq_zero_of_totalDegree_lt hgt
    simp only [coeff_sub, coeff_homogeneousComponent, heq, ite_false, hz, sub_self] at hcs
    exact hcs rfl

theorem polynomial_sub_hidden_top_power_degree_le (p : RealPoly) (l : ℕ) (c : ℝ)
    (hl : 0 < l) (hp : p.totalDegree = l)
    (htop : homogeneousComponent l p = C c * X 2 ^ l) :
    (p - C c * X 2 ^ l).totalDegree ≤ l-1 := by
  rw [← htop]
  exact polynomial_sub_top_component_degree_le p l hl hp.le

end Wong.SmoothModel

#print axioms Wong.SmoothModel.polynomial_sub_hidden_top_power_degree_le
