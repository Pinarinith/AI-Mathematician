import Wong.NormalSymbolsOrder

/-! Composition of actual normal forms up to the first two highest orders.
The error estimates are proved from repeated genuine left differentiation. -/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

/-- Induction by adding one derivative to a finite nonnegative multi-index. -/
theorem multiIndex_induction (P : MultiIndex → Prop) (hzero : P 0)
    (hstep : ∀ α i, P α → P (α + Finsupp.single i 1)) (α : MultiIndex) : P α := by
  classical
  have hall : ∀ n : ℕ, ∀ β : MultiIndex, β.degree = n → P β := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro β hn
      by_cases hb : β = 0
      · simpa [hb] using hzero
      have hi : ∃ i, β i ≠ 0 := by
        by_contra hh
        push Not at hh
        exact hb (Finsupp.ext hh)
      obtain ⟨i, hi⟩ := hi
      have hle : Finsupp.single i 1 ≤ β := by
        rw [Finsupp.single_le_iff]
        omega
      let γ := β - Finsupp.single i 1
      have he : γ + Finsupp.single i 1 = β := tsub_add_cancel_of_le hle
      have hdeg : γ.degree + 1 = n := by
        rw [← Finsupp.degree_single i (1 : ℕ), ← map_add, he, hn]
      have hp : P γ := ih γ.degree (by omega) γ rfl
      simpa [he] using hstep γ i hp
  exact hall α.degree α rfl

/-- Multi-index recursion agrees with the genuine normal-form derivative action. -/
theorem normalLeftMultiPartial_shift (α : MultiIndex) (i : Fin 3) (p : NormalForm) :
    normalLeftMultiPartial (α + Finsupp.single i 1) p =
      normalLeftPartial i (normalLeftMultiPartial α p) := by
  apply normalAction_injective
  rw [normalAction_leftMultiPartial, normalAction_leftPartial,
    normalAction_leftMultiPartial, multiPartial_shift]
  exact mul_assoc _ _ _

/-- The total symbol of actual left composition by a constant derivative monomial. -/
def symbolLeftMultiPartial (α : MultiIndex) (p : SmoothSymbol) : SmoothSymbol :=
  normalTotalSymbol (normalLeftMultiPartial α (normalTotalSymbol.symm p))

@[simp] theorem symbolLeftMultiPartial_zero (p : SmoothSymbol) :
    symbolLeftMultiPartial 0 p = p := by
  simp [symbolLeftMultiPartial, normalLeftMultiPartial]

theorem symbolLeftMultiPartial_shift (α : MultiIndex) (i : Fin 3) (p : SmoothSymbol) :
    symbolLeftMultiPartial (α + Finsupp.single i 1) p =
      symbolCoefficientDerivative i (symbolLeftMultiPartial α p) +
        X i * symbolLeftMultiPartial α p := by
  rw [symbolLeftMultiPartial, normalLeftMultiPartial_shift, normalTotalSymbol_leftPartial]
  rfl

/-- The first Leibniz correction in operator composition. -/
def symbolFirstCorrection (p q : SmoothSymbol) : SmoothSymbol :=
  ∑ i : Fin 3, pderiv i p * symbolCoefficientDerivative i q

theorem symbolFirstCorrection_X_mul (i : Fin 3) (p q : SmoothSymbol) :
    symbolFirstCorrection (X i * p) q =
      X i * symbolFirstCorrection p q + p * symbolCoefficientDerivative i q := by
  classical
  simp only [symbolFirstCorrection, pderiv_mul, pderiv_X, add_mul, Pi.single_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

@[simp] theorem symbolFirstCorrection_one (q : SmoothSymbol) :
    symbolFirstCorrection 1 q = 0 := by simp [symbolFirstCorrection]

@[simp] theorem coefficientDerivative_pderiv_momentum (i j : Fin 3) (α : MultiIndex) :
    symbolCoefficientDerivative i (pderiv j (monomial α (1 : Smooth))) = 0 := by
  simp only [pderiv_monomial, one_mul, symbolCoefficientDerivative_monomial]
  have hz : partialDerivative i (α j : Smooth) = 0 := by
    change partialDerivative i ((α j : ℝ) • smoothOne) = 0
    exact partialDerivative_const i _
  rw [hz, monomial_zero]

theorem coefficientDerivative_firstCorrection_momentum (i : Fin 3) (α : MultiIndex)
    (q : SmoothSymbol) :
    symbolCoefficientDerivative i (symbolFirstCorrection (monomial α 1) q) =
      ∑ j : Fin 3, pderiv j (monomial α 1) *
        symbolCoefficientDerivative i (symbolCoefficientDerivative j q) := by
  simp only [symbolFirstCorrection, map_sum, symbolCoefficientDerivative_mul,
    coefficientDerivative_pderiv_momentum, zero_mul, zero_add]

/-- The terms involving at least two coefficient differentiations. -/
def symbolMultiRemainder (α : MultiIndex) (q : SmoothSymbol) : SmoothSymbol :=
  symbolLeftMultiPartial α q - monomial α 1 * q - symbolFirstCorrection (monomial α 1) q

@[simp] theorem symbolMultiRemainder_zero (q : SmoothSymbol) :
    symbolMultiRemainder 0 q = 0 := by simp [symbolMultiRemainder]

theorem symbolMultiRemainder_shift (α : MultiIndex) (i : Fin 3) (q : SmoothSymbol) :
    symbolMultiRemainder (α + Finsupp.single i 1) q =
      symbolCoefficientDerivative i (symbolMultiRemainder α q) +
      X i * symbolMultiRemainder α q +
      ∑ j : Fin 3, pderiv j (monomial α 1) *
        symbolCoefficientDerivative i (symbolCoefficientDerivative j q) := by
  have hm : monomial (α + Finsupp.single i 1) (1 : Smooth) = X i * monomial α 1 := by
    simp [X, monomial_mul_monomial, add_comm]
  simp only [symbolMultiRemainder, symbolLeftMultiPartial_shift, hm,
    symbolFirstCorrection_X_mul, map_sub,
    symbolCoefficientDerivative_mul, symbolCoefficientDerivative_momentum,
    coefficientDerivative_firstCorrection_momentum, zero_mul, zero_add]
  ring

/-- Two or more coefficient differentiations lower order by at least two. -/
theorem symbolMultiRemainder_order (α : MultiIndex) (q : SmoothSymbol) (n : ℤ)
    (hq : SymbolOrderLE n q) :
    SymbolOrderLE (n + (α.degree : ℤ) - 2) (symbolMultiRemainder α q) := by
  induction α using multiIndex_induction with
  | hzero => simp only [symbolMultiRemainder_zero]; exact SymbolOrderLE.zero _
  | hstep α i ih =>
    rw [symbolMultiRemainder_shift]
    have he : n + ((α + Finsupp.single i 1).degree : ℤ) - 2 =
        n + (α.degree : ℤ) - 1 := by
      simp only [map_add, Finsupp.degree_single, Nat.cast_add, Nat.cast_one]
      ring
    rw [he]
    refine ((ih.coefficientDerivative i).mono (by omega)).add ?_ |>.add ?_
    · have hm := (SymbolOrderLE.X i).mul ih
      convert hm using 1; ring
    · apply SymbolOrderLE.sum
      intro j _
      have hm := ((SymbolOrderLE.monomial α (1 : Smooth)).pderiv j).mul
        ((hq.coefficientDerivative j).coefficientDerivative i)
      convert hm using 1; ring

end Wong.SmoothModel
