import Wong.PolynomialSmooth
import Mathlib.Tactic

/-!
# Visible derivative extraction of a nonlinear polynomial

Repeated derivatives in the two admitted visible directions either reach a
quadratic polynomial or reach a polynomial whose highest homogeneous part
is a nonzero pure power of the hidden coordinate. All statements below are
identities of real multivariate polynomials, without an operator assumption.
-/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

def polynomialPartialEnd (i : Fin 3) : Module.End ℝ RealPoly := (pderiv i).toLinearMap

def visiblePolynomialDerivative (a b : ℕ) (p : RealPoly) : RealPoly :=
  (polynomialPartialEnd 0 ^ a) ((polynomialPartialEnd 1 ^ b) p)

theorem polynomialPartialEnd_commute (i j : Fin 3) :
    Commute (polynomialPartialEnd i) (polynomialPartialEnd j) := by
  apply LinearMap.ext
  intro p
  apply polynomialSmooth_injective
  change polynomialSmooth (pderiv i (pderiv j p)) =
    polynomialSmooth (pderiv j (pderiv i p))
  rw [← partialDerivative_polynomialSmooth, ← partialDerivative_polynomialSmooth,
    ← partialDerivative_polynomialSmooth, ← partialDerivative_polynomialSmooth]
  exact partialDerivative_commute_apply i j (polynomialSmooth p)

theorem visiblePolynomialDerivative_succ_left (a b : ℕ) (p : RealPoly) :
    visiblePolynomialDerivative (a+1) b p =
      visiblePolynomialDerivative a b (pderiv 0 p) := by
  unfold visiblePolynomialDerivative
  rw [pow_succ, Module.End.mul_apply]
  have he := congrArg (fun T : Module.End ℝ RealPoly => T p)
    ((polynomialPartialEnd_commute 0 1).pow_right b).eq
  change (polynomialPartialEnd 0 ^ a)
      (polynomialPartialEnd 0 ((polynomialPartialEnd 1 ^ b) p)) = _
  exact congrArg (polynomialPartialEnd 0 ^ a) he

theorem visiblePolynomialDerivative_succ_right (a b : ℕ) (p : RealPoly) :
    visiblePolynomialDerivative a (b+1) p =
      visiblePolynomialDerivative a b (pderiv 1 p) := by
  unfold visiblePolynomialDerivative
  rw [pow_succ, Module.End.mul_apply]
  rfl

theorem polynomial_coeff_zero_of_partial_zero (p : RealPoly) (i : Fin 3)
    (hp : pderiv i p = 0) (s : Fin 3 →₀ ℕ) (hs : 0 < s i) : p.coeff s = 0 := by
  let t := s - Finsupp.single i 1
  have hback : t + Finsupp.single i 1 = s := by
    ext j
    by_cases hj : j = i
    · subst j
      simp only [t, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · simp [t, hj]
  have he := congrArg (fun q : RealPoly => q.coeff t) hp
  rw [coeff_pderiv, hback] at he
  have ht : (t i : ℝ) + 1 ≠ 0 := by positivity
  exact (mul_eq_zero.mp he).resolve_right ht

theorem homogeneous_eq_hidden_power_of_visible_partials_zero
    (q : RealPoly) (d : ℕ) (hq : q.IsHomogeneous d)
    (h₀ : pderiv 0 q = 0) (h₁ : pderiv 1 q = 0) :
    q = C (q.coeff (Finsupp.single 2 d)) * X 2 ^ d := by
  rw [C_mul_X_pow_eq_monomial]
  ext s
  by_cases hs : s = Finsupp.single 2 d
  · subst s
    simp
  have hcs : q.coeff s = 0 := by
    by_cases hd : s.degree = d
    · by_cases hsz₀ : s 0 = 0
      · by_cases hsz₁ : s 1 = 0
        · exfalso
          apply hs
          have hs₂ : s 2 = d := by
            simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_three, hsz₀, hsz₁,
              zero_add] using hd
          ext i
          fin_cases i <;> simp [hsz₀, hsz₁, hs₂]
        · exact polynomial_coeff_zero_of_partial_zero q 1 h₁ s (by omega)
      · exact polynomial_coeff_zero_of_partial_zero q 0 h₀ s (by omega)
    · exact hq.coeff_eq_zero hd
  simp [coeff_monomial, Ne.symm hs, hcs]

theorem top_partial_zero_of_degree_not_maximal (p : RealPoly) (d : ℕ)
    (hp : p.totalDegree = d) (hd : 0 < d) (i : Fin 3)
    (hne : (pderiv i p).totalDegree ≠ d-1) :
    pderiv i (homogeneousComponent d p) = 0 := by
  have hbound : (pderiv i p).totalDegree ≤ d-1 := by
    simpa only [hp] using Wong.PolynomialGradient.partial_totalDegree_le p i
  have hlt : (pderiv i p).totalDegree < d-1 := by omega
  have hzero := homogeneousComponent_eq_zero (d-1) (pderiv i p) hlt
  rw [Wong.PolynomialGradient.partial_homogeneousComponent] at hzero
  simpa only [show d-1+1=d by omega] using hzero

def VisiblePolynomialExtractionShape (q : RealPoly) : Prop :=
  q.totalDegree = 2 ∨
    ∃ (l : ℕ) (c : ℝ), 3 ≤ l ∧ c ≠ 0 ∧ q.totalDegree = l ∧
      homogeneousComponent l q = C c * X 2 ^ l

theorem visible_polynomial_derivative_extract_of_degree (d : ℕ) :
    ∀ p : RealPoly, p.totalDegree = d → 2 ≤ d →
      ∃ a b : ℕ, VisiblePolynomialExtractionShape (visiblePolynomialDerivative a b p) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro p hp hd
    by_cases he : d = 2
    · refine ⟨0, 0, Or.inl ?_⟩
      simp [visiblePolynomialDerivative, hp, he]
    have hd₃ : 3 ≤ d := by omega
    by_cases h₀ : (pderiv 0 p).totalDegree = d-1
    · obtain ⟨a, b, hab⟩ := ih (d-1) (by omega) (pderiv 0 p) h₀ (by omega)
      exact ⟨a+1, b, by simpa only [visiblePolynomialDerivative_succ_left] using hab⟩
    by_cases h₁ : (pderiv 1 p).totalDegree = d-1
    · obtain ⟨a, b, hab⟩ := ih (d-1) (by omega) (pderiv 1 p) h₁ (by omega)
      exact ⟨a, b+1, by simpa only [visiblePolynomialDerivative_succ_right] using hab⟩
    let q := homogeneousComponent d p
    have hq₀ : pderiv 0 q = 0 := top_partial_zero_of_degree_not_maximal p d hp (by omega) 0 h₀
    have hq₁ : pderiv 1 q = 0 := top_partial_zero_of_degree_not_maximal p d hp (by omega) 1 h₁
    have hqhom : q.IsHomogeneous d := homogeneousComponent_isHomogeneous d p
    have hqshape := homogeneous_eq_hidden_power_of_visible_partials_zero q d hqhom hq₀ hq₁
    have hpne : p ≠ 0 := by intro hz; simp [hz] at hp; omega
    have hqne : q ≠ 0 := by
      simpa only [q, ← hp] using Wong.PolynomialGradient.topComponent_ne_zero p hpne
    have hc : q.coeff (Finsupp.single 2 d) ≠ 0 := by
      intro hz
      apply hqne
      rw [hqshape, hz, map_zero, zero_mul]
    refine ⟨0, 0, Or.inr ⟨d, q.coeff (Finsupp.single 2 d), hd₃, hc, ?_, ?_⟩⟩
    · simpa [visiblePolynomialDerivative] using hp
    · simpa [visiblePolynomialDerivative, q] using hqshape

theorem visible_polynomial_derivative_extract (p : RealPoly) (hp : 2 ≤ p.totalDegree) :
    ∃ a b : ℕ, VisiblePolynomialExtractionShape (visiblePolynomialDerivative a b p) :=
  visible_polynomial_derivative_extract_of_degree p.totalDegree p rfl hp

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visible_polynomial_derivative_extract
