import Wong.NormalSymbolsComposition

/-! The full genuine normal-form product differs from its commutative symbol
product and the first Leibniz correction by at least two ordinary orders. -/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

/-- Total-symbol form of actual operator composition. -/
def symbolCompose (p q : SmoothSymbol) : SmoothSymbol :=
  normalTotalSymbol (normalCompose (normalTotalSymbol.symm p) (normalTotalSymbol.symm q))

/-- This symbol product acts by genuine composition on globally smooth functions. -/
theorem symbolCompose_action (p q : SmoothSymbol) :
    normalAction (normalTotalSymbol.symm (symbolCompose p q)) =
      normalAction (normalTotalSymbol.symm p) * normalAction (normalTotalSymbol.symm q) := by
  simp only [symbolCompose, LinearEquiv.symm_apply_apply, normalAction_compose]

/-- The coefficientwise finite expansion follows from the already proved actual composition. -/
theorem symbolCompose_expansion (p q : SmoothSymbol) :
    symbolCompose p q = ∑ α ∈ p.support, C (p.coeff α) * symbolLeftMultiPartial α q := by
  classical
  change normalTotalSymbol ((normalTotalSymbol.symm p).sum
    (fun α u => normalLeftMultiplier u (normalLeftMultiPartial α (normalTotalSymbol.symm q)))) = _
  simp only [Finsupp.sum, map_sum, normalTotalSymbol_leftMultiplier]
  rfl

theorem symbolFirstCorrection_C_mul (u : Smooth) (p q : SmoothSymbol) :
    symbolFirstCorrection (C u * p) q = C u * symbolFirstCorrection p q := by
  simp only [symbolFirstCorrection, pderiv_mul, pderiv_C, zero_mul, zero_add,
    mul_assoc, Finset.mul_sum]

theorem symbolFirstCorrection_sum {ι : Type*} (s : Finset ι) (p : ι → SmoothSymbol)
    (q : SmoothSymbol) :
    symbolFirstCorrection (∑ i ∈ s, p i) q = ∑ i ∈ s, symbolFirstCorrection (p i) q := by
  classical
  simp only [symbolFirstCorrection, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- The operator-composition remainder after the first Leibniz correction. -/
def symbolCompositionRemainder (p q : SmoothSymbol) : SmoothSymbol :=
  symbolCompose p q - p * q - symbolFirstCorrection p q

theorem symbolCompositionRemainder_expansion (p q : SmoothSymbol) :
    symbolCompositionRemainder p q =
      ∑ α ∈ p.support, C (p.coeff α) * symbolMultiRemainder α q := by
  classical
  have hp : p = ∑ α ∈ p.support, C (p.coeff α) * monomial α 1 := by
    simpa only [C_mul_monomial, mul_one] using p.as_sum
  unfold symbolCompositionRemainder
  rw [symbolCompose_expansion]
  conv_lhs => arg 1; arg 2; arg 1; rw [hp]
  conv_lhs => arg 2; arg 1; rw [hp]
  simp only [Finset.sum_mul, symbolFirstCorrection_sum, symbolFirstCorrection_C_mul,
    ← Finset.sum_sub_distrib, symbolMultiRemainder, mul_sub, mul_assoc]

/-- At most `m+n-2` remains after subtracting the first two composition terms.
    Integer orders make the assertion exact also in orders zero and one. -/
theorem symbolCompositionRemainder_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : SymbolOrderLE m p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE (m + n - 2) (symbolCompositionRemainder p q) := by
  classical
  rw [symbolCompositionRemainder_expansion]
  apply SymbolOrderLE.sum
  intro α hα
  have hdeg : (α.degree : ℤ) ≤ m := by
    by_contra hh
    exact (mem_support_iff.mp hα) (hp α (by omega))
  have hb := (SymbolOrderLE.C (p.coeff α)).mul (symbolMultiRemainder_order α q n hq)
  apply hb.mono
  omega

/-- The correction has one fewer momentum factor than the ordinary product. -/
theorem symbolFirstCorrection_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : SymbolOrderLE m p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE (m + n - 1) (symbolFirstCorrection p q) := by
  apply SymbolOrderLE.sum
  intro i _
  have hh := (hp.pderiv i).mul (hq.coefficientDerivative i)
  convert hh using 1; ring

/-- Genuine composition adds the ordinary differential-order bounds. -/
theorem symbolCompose_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : SymbolOrderLE m p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE (m + n) (symbolCompose p q) := by
  have he : symbolCompose p q = p * q + symbolFirstCorrection p q +
      symbolCompositionRemainder p q := by unfold symbolCompositionRemainder; ring
  rw [he]
  exact ((hp.mul hq).add ((symbolFirstCorrection_order p q m n hp hq).mono (by omega))).add
    ((symbolCompositionRemainder_order p q m n hp hq).mono (by omega))

end Wong.SmoothModel
