import Wong.MainStatement
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

noncomputable section
namespace Wong.PolynomialAffinity
open MvPolynomial

theorem monomial_degree_le_one (d : Fin 3 →₀ ℕ) (hd : d.degree ≤ 1) :
    d = 0 ∨ ∃ i, d = Finsupp.single i 1 := by
  by_cases hzero : d = 0
  · exact Or.inl hzero
  · right
    have hdeg : d.degree = 1 := by
      have : d.degree ≠ 0 := fun h => hzero ((Finsupp.degree_eq_zero_iff d).mp h)
      omega
    have hr : d ∈ Set.range (fun i : Fin 3 => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]
      exact hdeg
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, hi.symm⟩

/-- Every real three-variable polynomial of total degree at most one is
exactly its constant term plus its three linear monomials. -/
theorem polynomial_eq_affine (p : MvPolynomial (Fin 3) ℝ) (hp : p.totalDegree ≤ 1) :
    p = C (p.coeff 0) + ∑ i : Fin 3, monomial (Finsupp.single i 1)
      (p.coeff (Finsupp.single i 1)) := by
  ext d
  by_cases hd0 : d = 0
  · subst d
    simp
  by_cases hd1 : ∃ i : Fin 3, d = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := hd1
    simp [Finsupp.single_eq_single_iff, Ne.symm hd0]
  · have hc : p.coeff d = 0 := by
      by_contra hc
      have hdeg : d.degree ≤ 1 := (le_totalDegree (mem_support_iff.mpr hc)).trans hp
      exact (monomial_degree_le_one d hdeg).elim hd0 hd1
    have hne : ∀ i : Fin 3, Finsupp.single i 1 ≠ d :=
      fun i hi => hd1 ⟨i, hi.symm⟩
    simp [coeff_C, coeff_monomial, Ne.symm hd0, hne, hc]

/-- The corresponding evaluated affine formula. -/
theorem eval_eq_affine (p : MvPolynomial (Fin 3) ℝ) (hp : p.totalDegree ≤ 1)
    (x : Fin 3 → ℝ) :
    eval x p = p.coeff 0 + ∑ i, p.coeff (Finsupp.single i 1) * x i := by
  conv_lhs => rw [polynomial_eq_affine p hp]
  simp [eval_monomial]

end Wong.PolynomialAffinity
