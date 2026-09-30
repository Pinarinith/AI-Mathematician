import Wong.EulerHeadExtraction
import Wong.NormalSymbolsBracket
import Wong.NormalSymbolsOrderBridge
import Wong.NormalSymbolsPrincipal
import Wong.SharpDifferentialOrder

/-!
# Pure hidden principal symbols attached to actual smooth normal operators

These are consequences of the proved genuine principal-symbol bracket bridge,
not a replacement symbolic Lie algebra or an assumed correspondence.
-/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial
set_option maxHeartbeats 1000000

def pureHiddenSymbol (n : ℕ) (u : Smooth) : SmoothSymbol :=
  monomial (Finsupp.single 2 n) u

def HasPureHiddenPrincipal (n : ℕ) (u : Smooth) (p : NormalForm) : Prop :=
  NormalDegreeLE n p ∧ normalSymbol n p = pureHiddenSymbol n u

@[simp] theorem pureHiddenSymbol_coefficientDerivative (i : Fin 3) (n : ℕ) (u : Smooth) :
    symbolCoefficientDerivative i (pureHiddenSymbol n u) =
      pureHiddenSymbol n (partialDerivative i u) := by
  exact symbolCoefficientDerivative_monomial i _ u

theorem pureHiddenSymbol_pderiv_other (i : Fin 3) (hi : i ≠ 2) (n : ℕ) (u : Smooth) :
    pderiv i (pureHiddenSymbol n u) = 0 := by
  simp [pureHiddenSymbol, pderiv_monomial, hi]

@[simp] theorem pureHiddenSymbol_pderiv_hidden (n : ℕ) (u : Smooth) :
    pderiv 2 (pureHiddenSymbol (n + 1) u) = pureHiddenSymbol n (u * (n + 1 : ℕ)) := by
  simp [pureHiddenSymbol]

theorem symbolFirstCorrection_pure_hidden (m n : ℕ) (u v : Smooth) :
    symbolFirstCorrection (pureHiddenSymbol (m + 1) u) (pureHiddenSymbol n v) =
      pureHiddenSymbol (m + n) ((u * (m + 1 : ℕ)) * partialDerivative 2 v) := by
  classical
  rw [symbolFirstCorrection, Finset.sum_eq_single 2]
  · rw [pureHiddenSymbol_pderiv_hidden, pureHiddenSymbol_coefficientDerivative]
    simp only [pureHiddenSymbol, monomial_mul_monomial, ← Finsupp.single_add]
  · intro i hi hi2
    rw [pureHiddenSymbol_pderiv_other i hi2, zero_mul]
  · simp

/-- Exact one-direction Poisson formula, valid for arbitrary smooth coefficients. -/
theorem symbolPoisson_pure_hidden (m n : ℕ) (u v : Smooth) :
    symbolPoisson (pureHiddenSymbol (m + 1) u) (pureHiddenSymbol (n + 1) v) =
      pureHiddenSymbol (m + n + 1)
        ((u * (m + 1 : ℕ)) * partialDerivative 2 v -
          (v * (n + 1 : ℕ)) * partialDerivative 2 u) := by
  rw [symbolPoisson, symbolFirstCorrection_pure_hidden, symbolFirstCorrection_pure_hidden]
  rw [show m + (n + 1) = m + n + 1 by omega,
    show n + (m + 1) = m + n + 1 by omega]
  exact (map_sub (monomial (Finsupp.single 2 (m + n + 1))) _ _).symm

/-- The pure hidden principal term is preserved under genuine brackets
with exactly the differentiated leading coefficient shown by Poisson calculus. -/
theorem pure_hidden_principal_bracket (p q : NormalForm) (m n : ℕ) (u v : Smooth)
    (hp : HasPureHiddenPrincipal (m + 1) u p)
    (hq : HasPureHiddenPrincipal (n + 1) v q) :
    HasPureHiddenPrincipal (m + n + 1)
      ((u * (m + 1 : ℕ)) * partialDerivative 2 v -
        (v * (n + 1 : ℕ)) * partialDerivative 2 u) (normalBracket p q) := by
  refine ⟨?_, ?_⟩
  · apply normalDegreeLE_of_action_order
    rw [normalAction_bracket]
    have hb := lie_mem_orderSpace_sharp
      (action_order_of_normalDegreeLE p (m + 1) hp.1)
      (action_order_of_normalDegreeLE q (n + 1) hq.1)
    simpa only [show m + 1 + (n + 1) - 1 = m + n + 1 by omega] using hb
  · rw [normalSymbol_bracket p q m n hp.1 hq.1, hp.2, hq.2,
      symbolPoisson_pure_hidden]

theorem pure_hidden_principal_single (n : ℕ) (u : Smooth) :
    HasPureHiddenPrincipal n u (Finsupp.single (Finsupp.single 2 n) u) := by
  classical
  refine ⟨?_, ?_⟩
  · intro α hα
    have hne : Finsupp.single 2 n ≠ α := by
      intro he
      rw [← he, Finsupp.degree_single] at hα
      omega
    simp [hne]
  · simp only [normalSymbol_single, Finsupp.degree_single, ite_true]
    rfl

theorem normalSymbol_zero_of_lower_order (p : NormalForm) (n m : ℕ)
    (hp : NormalDegreeLE n p) (hnm : n < m) : normalSymbol m p = 0 := by
  apply MvPolynomial.ext
  intro α
  rw [normalSymbol_coeff, AddMonoidAlgebra.coeff_zero]
  split_ifs with hα
  · exact hp α (by omega)
  · rfl

theorem pure_hidden_principal_add_lower (p q : NormalForm) (n : ℕ) (u : Smooth)
    (hp : HasPureHiddenPrincipal (n + 1) u p) (hq : NormalDegreeLE n q) :
    HasPureHiddenPrincipal (n + 1) u (p + q) := by
  refine ⟨?_, ?_⟩
  · intro α hα
    simp only [Finsupp.add_apply, hp.1 α hα, hq α (by omega), zero_add]
  · have hz := normalSymbol_zero_of_lower_order q n (n + 1) hq (Nat.lt_succ_self n)
    rw [normalSymbol_add, hp.2, hz, add_zero]

theorem pure_hidden_principal_smul (p : NormalForm) (n : ℕ) (u : Smooth) (c : ℝ)
    (hp : HasPureHiddenPrincipal n u p) : HasPureHiddenPrincipal n (c • u) (c • p) := by
  classical
  refine ⟨?_, ?_⟩
  · intro α hα
    simp only [Finsupp.smul_apply, hp.1 α hα, smul_zero]
  · rw [normalSymbol_smul, hp.2]
    simp only [pureHiddenSymbol, smul_monomial]

end Wong.SmoothModel
