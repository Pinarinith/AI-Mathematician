import Wong.PolynomialVisibleExtraction

/-! Degree growth of genuine visible polynomial products. This is the pure
polynomial step of the visible curvature-gradient argument, not a new
assumption about which products belong to an estimation Lie algebra. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

theorem hidden_independent_polynomial_has_maximal_visible_partial
    (p : RealPoly) (hp : 2 ≤ p.totalDegree) (hhidden : pderiv 2 p = 0) :
    ∃ i : Fin 3, (i = 0 ∨ i = 1) ∧
      (pderiv i p).totalDegree = p.totalDegree-1 := by
  by_cases h₀ : (pderiv 0 p).totalDegree = p.totalDegree-1
  · exact ⟨0, Or.inl rfl, h₀⟩
  by_cases h₁ : (pderiv 1 p).totalDegree = p.totalDegree-1
  · exact ⟨1, Or.inr rfl, h₁⟩
  let q := homogeneousComponent p.totalDegree p
  have hq₀ : pderiv 0 q = 0 :=
    top_partial_zero_of_degree_not_maximal p _ rfl (by omega) 0 h₀
  have hq₁ : pderiv 1 q = 0 :=
    top_partial_zero_of_degree_not_maximal p _ rfl (by omega) 1 h₁
  have hq₂ : pderiv 2 q = 0 := by
    have hz : homogeneousComponent (p.totalDegree-1) (pderiv 2 p) = 0 := by
      rw [hhidden, map_zero]
    rw [Wong.PolynomialGradient.partial_homogeneousComponent] at hz
    simpa only [show p.totalDegree-1+1=p.totalDegree by omega] using hz
  have hqshape := homogeneous_eq_hidden_power_of_visible_partials_zero
    q p.totalDegree (homogeneousComponent_isHomogeneous _ _) hq₀ hq₁
  have hcoeff : q.coeff (Finsupp.single 2 p.totalDegree) = 0 :=
    polynomial_coeff_zero_of_partial_zero q 2 hq₂ _ (by simp; omega)
  have hqne : q ≠ 0 := Wong.PolynomialGradient.topComponent_ne_zero p (by
    intro hz
    simp [hz] at hp)
  exfalso
  apply hqne
  rw [hqshape, hcoeff, map_zero, zero_mul]

theorem hidden_independent_polynomial_degree_le_one_of_product_bounds
    (p : RealPoly) (hhidden : pderiv 2 p = 0)
    (h₀ : (pderiv 0 p * p).totalDegree ≤ 2)
    (h₁ : (pderiv 1 p * p).totalDegree ≤ 2) : p.totalDegree ≤ 1 := by
  by_contra hnot
  have hp : 2 ≤ p.totalDegree := by omega
  obtain ⟨i, hi, hdeg⟩ := hidden_independent_polynomial_has_maximal_visible_partial p hp hhidden
  have hprod : (pderiv i p * p).totalDegree ≤ 2 := by
    rcases hi with rfl | rfl
    · exact h₀
    · exact h₁
  have hpne : p ≠ 0 := by intro hz; simp [hz] at hp
  have hdpne : pderiv i p ≠ 0 := by
    intro hz
    simp [hz] at hdeg
    omega
  rw [totalDegree_mul_of_isDomain hdpne hpne, hdeg] at hprod
  omega

end Wong.SmoothModel

#print axioms Wong.SmoothModel.hidden_independent_polynomial_degree_le_one_of_product_bounds
