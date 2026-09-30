import Wong.WeightedSymbolsOrder
import Wong.NormalSymbolsHeads

/-!
# Exact actual symbol calculus and canonical weighted commutator bounds

The coefficient filtration uses actual hidden derivatives. These proofs
reuse genuine normal composition and faithfulness; no assumed principal
intertwiner or formal operator model is introduced. Related blocks are
compiled together to avoid repeated large imports on the 8 GB workstation.
-/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial


/-- One actual sufficiently high hidden derivative suffices for the full hidden degree bound. -/
theorem hiddenDegreeLE_nat_iff (n : ℕ) (u : Smooth) :
    HiddenDegreeLE n u ↔ (partialDerivative 2 ^ (n+1)) u=0 := by
  constructor
  · intro hu
    exact hu (n+1) (by omega)
  · intro hu k hk
    have hkn : n+1≤k := by omega
    rw [show k=(k-(n+1))+(n+1) by omega, pow_add, Module.End.mul_apply, hu, map_zero]

/-! ## NormalSymbolsExact -/

theorem partialDerivative_commute_multiPartial (i : Fin 3) (α : MultiIndex) :
    Commute (partialDerivative i) (multiPartial α) := by
  have hc (j : Fin 3) : Commute (partialDerivative i) (partialDerivative j) :=
    partialDerivative_commute i j
  exact (((hc 0).pow_right (α 0)).mul_right
    ((hc 1).pow_right (α 1))).mul_right ((hc 2).pow_right (α 2))

theorem normalQuantize_mul_X (p : SmoothSymbol) (i : Fin 3) :
    normalQuantize (p * X i) = normalQuantize p * partialDerivative i := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]
  | monomial α u =>
    rw [X, monomial_mul_monomial, mul_one, normalQuantize_monomial,
      normalQuantize_monomial, multiPartial_shift,
      (partialDerivative_commute_multiPartial i α).eq, mul_assoc]

@[simp] theorem normalQuantize_X (i : Fin 3) :
    normalQuantize (X i) = partialDerivative i := by
  change normalAction (Finsupp.single (Finsupp.single i 1) smoothOne) = _
  exact normalAction_partial i

/-- Position coefficient differentiation is exactly the actual commutator
with a coordinate partial, with the genuine sign. -/
theorem normalQuantize_coefficientDerivative (p : SmoothSymbol) (i : Fin 3) :
    normalQuantize (symbolCoefficientDerivative i p) = ⁅partialDerivative i, normalQuantize p⁆ := by
  have hh := normalQuantize_X_mul i p
  rw [mul_comm (X i) p, normalQuantize_mul_X] at hh
  rw [operator_lie_def]
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact eq_sub_iff_add_eq.mp hh

theorem normalQuantize_symbolBracket (p q : SmoothSymbol) :
    normalQuantize (symbolBracket p q) = ⁅normalQuantize p,normalQuantize q⁆ :=
  symbolBracket_action p q

theorem symbolBracket_X_left (i : Fin 3) (p : SmoothSymbol) :
    symbolBracket (X i) p = symbolCoefficientDerivative i p := by
  apply normalQuantize_injective
  rw [normalQuantize_symbolBracket, normalQuantize_X, normalQuantize_coefficientDerivative]

/-- Exact second-order Leibniz identity; the second coefficient derivative
is retained explicitly rather than silently discarded. -/
theorem symbolBracket_X_sq_left (i : Fin 3) (p : SmoothSymbol) :
    symbolBracket ((X i)^2) p =
      2 * X i * symbolCoefficientDerivative i p +
      symbolCoefficientDerivative i (symbolCoefficientDerivative i p) := by
  apply normalQuantize_injective
  rw [normalQuantize_symbolBracket]
  have hsq : normalQuantize ((X i : SmoothSymbol)^2) = partialDerivative i*partialDerivative i := by
    rw [pow_two, normalQuantize_mul_X, normalQuantize_X]
  rw [hsq, operator_lie_mul_left]
  have he : 2 * X i * symbolCoefficientDerivative i p =
      X i * symbolCoefficientDerivative i p + X i * symbolCoefficientDerivative i p := by ring
  simp only [he, map_add, normalQuantize_X_mul,
    normalQuantize_coefficientDerivative, operator_lie_def]
  noncomm_ring


theorem normalQuantize_symbolCompose (p q : SmoothSymbol) :
    normalQuantize (symbolCompose p q) = normalQuantize p*normalQuantize q :=
  symbolCompose_action p q

@[simp] theorem symbolCompose_C_left (u : Smooth) (p : SmoothSymbol) :
    symbolCompose (C u) p = C u*p := by
  apply normalQuantize_injective
  rw [normalQuantize_symbolCompose, normalQuantize_C, normalQuantize_C_mul]

/-- Exact composition by a coefficient times one actual partial. -/
theorem symbolCompose_C_X_left (u : Smooth) (i : Fin 3) (p : SmoothSymbol) :
    symbolCompose (C u*X i) p =
      C u*(symbolCoefficientDerivative i p+X i*p) := by
  apply normalQuantize_injective
  rw [normalQuantize_symbolCompose, normalQuantize_C_mul, normalQuantize_X,
    normalQuantize_C_mul, map_add, normalQuantize_X_mul]
  rw [mul_assoc]
  congr 1
  abel

@[simp] theorem symbolFirstCorrection_C_left (u : Smooth) (p : SmoothSymbol) :
    symbolFirstCorrection (C u) p = 0 := by
  simp [symbolFirstCorrection]

theorem symbolFirstCorrection_X_left (i : Fin 3) (p : SmoothSymbol) :
    symbolFirstCorrection (X i) p = symbolCoefficientDerivative i p := by
  simp [symbolFirstCorrection, pderiv_X, Pi.single_apply, ite_mul]

@[simp] theorem symbolCompositionRemainder_C_left (u : Smooth) (p : SmoothSymbol) :
    symbolCompositionRemainder (C u) p = 0 := by
  simp [symbolCompositionRemainder]

/-- The first-order left factor has no second Leibniz remainder, even for
arbitrary actual smooth coefficients. -/
@[simp] theorem symbolCompositionRemainder_C_X_left (u : Smooth) (i : Fin 3)
    (p : SmoothSymbol) : symbolCompositionRemainder (C u*X i) p=0 := by
  rw [symbolCompositionRemainder, symbolCompose_C_X_left,
    symbolFirstCorrection_C_mul, symbolFirstCorrection_X_left]
  ring


theorem symbolBracket_add_left (p q r : SmoothSymbol) :
    symbolBracket (p+q) r = symbolBracket p r+symbolBracket q r := by
  apply normalQuantize_injective
  simp only [normalQuantize_symbolBracket, map_add, add_lie]

theorem symbolBracket_add_right (p q r : SmoothSymbol) :
    symbolBracket p (q+r) = symbolBracket p q+symbolBracket p r := by
  apply normalQuantize_injective
  simp only [normalQuantize_symbolBracket, map_add, lie_add]

theorem symbolBracket_smul_left (c : ℝ) (p q : SmoothSymbol) :
    symbolBracket (c • p) q = c • symbolBracket p q := by
  apply normalQuantize_injective
  simp only [normalQuantize_symbolBracket, map_smul, smul_lie]

theorem symbolBracket_smul_right (c : ℝ) (p q : SmoothSymbol) :
    symbolBracket p (c • q) = c • symbolBracket p q := by
  apply normalQuantize_injective
  simp only [normalQuantize_symbolBracket, map_smul, lie_smul]

theorem symbolBracket_sub_left (p q r : SmoothSymbol) :
    symbolBracket (p-q) r = symbolBracket p r-symbolBracket q r := by
  apply normalQuantize_injective
  simp only [normalQuantize_symbolBracket, map_sub, sub_lie]

theorem symbolBracket_sub_right (p q r : SmoothSymbol) :
    symbolBracket p (q-r) = symbolBracket p q-symbolBracket p r := by
  apply normalQuantize_injective
  simp only [normalQuantize_symbolBracket, map_sub, lie_sub]


/-! ## WeightedSymbolsComposition -/

theorem pairedCoordinateWeight_pos (i : Fin 3) :
    (1:ℤ) ≤ (momentumCoordinateWeight i:ℤ)+(positionDerivativeWeight i:ℤ) := by
  fin_cases i <;> norm_num [momentumCoordinateWeight, positionDerivativeWeight]

/-- After the first Leibniz correction, at least two units of genuine weighted
order are lost. The bound is valid for all smooth hidden-polynomial coefficients. -/
theorem weightedSymbolMultiRemainder_order (α : MultiIndex) (q : SmoothSymbol)
    (n : ℤ) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE (n+momentumWeight α-2) (symbolMultiRemainder α q) := by
  induction α using multiIndex_induction with
  | hzero => rw [symbolMultiRemainder_zero]; exact WeightedSymbolOrderLE.zero _
  | hstep α i ih =>
    rw [symbolMultiRemainder_shift]
    simp only [momentumWeight_add, momentumWeight_single, mul_one, Nat.cast_add]
    change WeightedSymbolOrderLE (n+((momentumWeight α:ℤ)+momentumCoordinateWeight i)-2) _
    apply WeightedSymbolOrderLE.add
    · apply WeightedSymbolOrderLE.add
      · exact (ih.coefficientDerivative i).mono (by
          have hi := pairedCoordinateWeight_pos i
          omega)
      · exact ((WeightedSymbolOrderLE.X i).mul ih).mono (by omega)
    · apply WeightedSymbolOrderLE.sum
      intro j _
      have hm : WeightedSymbolOrderLE (momentumWeight α)
          (monomial α (1:Smooth)) := by
        have ho : HiddenDegreeLE 0 (1:Smooth) := by
          simpa only [one_smul, smoothOne_eq_one] using HiddenDegreeLE.constant 1
        simpa only [zero_add] using WeightedSymbolOrderLE.monomial α 1 ho
      have hh := (hm.pderiv j).mul ((hq.coefficientDerivative j).coefficientDerivative i)
      exact hh.mono (by
        have hi := pairedCoordinateWeight_pos i
        have hj := pairedCoordinateWeight_pos j
        omega)

theorem weightedSymbolCompositionRemainder_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : WeightedSymbolOrderLE m p) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE (m+n-2) (symbolCompositionRemainder p q) := by
  classical
  rw [symbolCompositionRemainder_expansion]
  apply WeightedSymbolOrderLE.sum
  intro α _
  have hh := (WeightedSymbolOrderLE.C (p.coeff α) (hp α)).mul
    (weightedSymbolMultiRemainder_order α q n hq)
  convert hh using 1 <;> ring

theorem weightedSymbolFirstCorrection_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : WeightedSymbolOrderLE m p) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE (m+n-1) (symbolFirstCorrection p q) := by
  apply WeightedSymbolOrderLE.sum
  intro i _
  have hh := (hp.pderiv i).mul (hq.coefficientDerivative i)
  exact hh.mono (by have hi := pairedCoordinateWeight_pos i; omega)

theorem weightedSymbolCompose_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : WeightedSymbolOrderLE m p) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE (m+n) (symbolCompose p q) := by
  have he : symbolCompose p q = p*q+symbolFirstCorrection p q+
      symbolCompositionRemainder p q := by unfold symbolCompositionRemainder; ring
  rw [he]
  exact ((hp.mul hq).add ((weightedSymbolFirstCorrection_order p q m n hp hq).mono (by omega))).add
    ((weightedSymbolCompositionRemainder_order p q m n hp hq).mono (by omega))

theorem weightedSymbolBracket_sub_poisson_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : WeightedSymbolOrderLE m p) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE (m+n-2) (symbolBracket p q-symbolPoisson p q) := by
  have he : symbolBracket p q-symbolPoisson p q =
      symbolCompositionRemainder p q-symbolCompositionRemainder q p := by
    unfold symbolBracket symbolPoisson symbolCompositionRemainder
    ring
  rw [he]
  exact (weightedSymbolCompositionRemainder_order p q m n hp hq).sub
    (by simpa only [add_comm n m] using weightedSymbolCompositionRemainder_order q p n m hq hp)

theorem weightedSymbolPoisson_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : WeightedSymbolOrderLE m p) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE (m+n-1) (symbolPoisson p q) := by
  exact (weightedSymbolFirstCorrection_order p q m n hp hq).sub
    (by simpa only [add_comm n m] using weightedSymbolFirstCorrection_order q p n m hq hp)

theorem weightedSymbolBracket_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : WeightedSymbolOrderLE m p) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE (m+n-1) (symbolBracket p q) := by
  have he : symbolBracket p q = symbolPoisson p q+
      (symbolBracket p q-symbolPoisson p q) := by ring
  rw [he]
  exact (weightedSymbolPoisson_order p q m n hp hq).add
    ((weightedSymbolBracket_sub_poisson_order p q m n hp hq).mono (by omega))


/-! ## WeightedHiddenRemainder -/

@[simp] theorem symbolLeftMultiPartial_zero_input (α : MultiIndex) :
    symbolLeftMultiPartial α 0=0 := by simp [symbolLeftMultiPartial]

theorem symbolCoefficientDerivative_leftMultiPartial (i : Fin 3) (α : MultiIndex)
    (p : SmoothSymbol) :
    symbolCoefficientDerivative i (symbolLeftMultiPartial α p) =
      symbolLeftMultiPartial α (symbolCoefficientDerivative i p) := by
  induction α using multiIndex_induction with
  | hzero => simp only [symbolLeftMultiPartial_zero]
  | hstep α j ih =>
    rw [symbolLeftMultiPartial_shift, map_add, symbolCoefficientDerivative_mul,
      symbolCoefficientDerivative_X, zero_mul, zero_add,
      symbolCoefficientDerivative_commute i j, ih, symbolLeftMultiPartial_shift]

theorem symbolCoefficientDerivative_multiRemainder (i : Fin 3) (α : MultiIndex)
    (p : SmoothSymbol) :
    symbolCoefficientDerivative i (symbolMultiRemainder α p) =
      symbolMultiRemainder α (symbolCoefficientDerivative i p) := by
  simp only [symbolMultiRemainder, map_sub, symbolCoefficientDerivative_leftMultiPartial,
    symbolCoefficientDerivative_mul, symbolCoefficientDerivative_momentum,
    zero_mul, zero_add, coefficientDerivative_firstCorrection_momentum]
  simp only [symbolFirstCorrection, symbolCoefficientDerivative_commute i]

@[simp] theorem symbolMultiRemainder_zero_input (α : MultiIndex) :
    symbolMultiRemainder α 0=0 := by
  simp [symbolMultiRemainder, symbolFirstCorrection]

/-- With hidden-only coefficient dependence, the two-derivative composition
remainder loses at least six units of the actual weighted order. -/
theorem weightedSymbolMultiRemainder_hiddenRight_order (α : MultiIndex) (q : SmoothSymbol)
    (n : ℤ) (hq : WeightedSymbolOrderLE n q)
    (hvis : ∀i : Fin 3,i≠2 → symbolCoefficientDerivative i q=0) :
    WeightedSymbolOrderLE (n+momentumWeight α-6) (symbolMultiRemainder α q) := by
  induction α using multiIndex_induction with
  | hzero => rw [symbolMultiRemainder_zero]; exact WeightedSymbolOrderLE.zero _
  | hstep α i ih =>
    rw [symbolMultiRemainder_shift]
    simp only [momentumWeight_add, momentumWeight_single, mul_one, Nat.cast_add]
    change WeightedSymbolOrderLE (n+((momentumWeight α:ℤ)+momentumCoordinateWeight i)-6) _
    apply WeightedSymbolOrderLE.add
    · apply WeightedSymbolOrderLE.add
      · exact (ih.coefficientDerivative i).mono (by
          have hi := pairedCoordinateWeight_pos i
          omega)
      · exact ((WeightedSymbolOrderLE.X i).mul ih).mono (by omega)
    · apply WeightedSymbolOrderLE.sum
      intro j _
      by_cases hi : i=2
      · subst i
        by_cases hj : j=2
        · subst j
          have hm : WeightedSymbolOrderLE (momentumWeight α) (monomial α (1:Smooth)) := by
            have ho : HiddenDegreeLE 0 (1:Smooth) := by
              simpa only [one_smul, smoothOne_eq_one] using HiddenDegreeLE.constant 1
            simpa only [zero_add] using WeightedSymbolOrderLE.monomial α 1 ho
          have hh := (hm.pderiv 2).mul ((hq.coefficientDerivative 2).coefficientDerivative 2)
          convert hh using 1 <;>
            norm_num [momentumCoordinateWeight, positionDerivativeWeight] <;> ring
        · rw [hvis j hj, map_zero, mul_zero]
          exact WeightedSymbolOrderLE.zero _
      · rw [symbolCoefficientDerivative_commute i j, hvis i hi, map_zero, mul_zero]
        exact WeightedSymbolOrderLE.zero _

/-- The stronger remainder bound is attached to the actual normal composition. -/
theorem weightedSymbolCompositionRemainder_hiddenRight_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : WeightedSymbolOrderLE m p) (hq : WeightedSymbolOrderLE n q)
    (hvis : ∀i : Fin 3,i≠2 → symbolCoefficientDerivative i q=0) :
    WeightedSymbolOrderLE (m+n-6) (symbolCompositionRemainder p q) := by
  classical
  rw [symbolCompositionRemainder_expansion]
  apply WeightedSymbolOrderLE.sum
  intro α _
  have hh := (WeightedSymbolOrderLE.C (p.coeff α) (hp α)).mul
    (weightedSymbolMultiRemainder_hiddenRight_order α q n hq hvis)
  convert hh using 1 <;> ring


/-! ## WeightedCanonicalBounds -/

theorem pairedCoordinateWeight_difference (i : Fin 3) :
    (momentumCoordinateWeight i:ℤ)-(positionDerivativeWeight i:ℤ)=1 := by
  fin_cases i <;> norm_num [momentumCoordinateWeight, positionDerivativeWeight]

/-- Every coordinate kinetic square raises actual weighted order at most one. -/
theorem weightedSymbolBracket_X_sq_order (i : Fin 3) (p : SmoothSymbol) (n : ℤ)
    (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE (n+1) (symbolBracket ((X i)^2) p) := by
  rw [symbolBracket_X_sq_left]
  have h₁ : WeightedSymbolOrderLE (n+1) (X i*symbolCoefficientDerivative i p) := by
    exact ((WeightedSymbolOrderLE.X i).mul (hp.coefficientDerivative i)).mono
      (by have hi := pairedCoordinateWeight_difference i; omega)
  have he : 2*X i*symbolCoefficientDerivative i p =
      X i*symbolCoefficientDerivative i p + X i*symbolCoefficientDerivative i p := by ring
  rw [he]
  exact (h₁.add h₁).add
    (((hp.coefficientDerivative i).coefficientDerivative i).mono (by omega))

/-- With hidden-only right coefficients, the first correction uses only the hidden index. -/
theorem symbolFirstCorrection_hiddenRight (p q : SmoothSymbol)
    (hvis : ∀i : Fin 3,i≠2 → symbolCoefficientDerivative i q=0) :
    symbolFirstCorrection p q = pderiv 2 p*symbolCoefficientDerivative 2 q := by
  simp only [symbolFirstCorrection, Fin.sum_univ_three,
    hvis 0 (by decide), hvis 1 (by decide), mul_zero, zero_add]

/-- Reconstruct the actual bracket from its exact first correction and remainders. -/
theorem symbolBracket_eq_poisson_remainders (p q : SmoothSymbol) :
    symbolBracket p q = symbolPoisson p q+
      (symbolCompositionRemainder p q-symbolCompositionRemainder q p) := by
  unfold symbolBracket symbolPoisson symbolCompositionRemainder
  ring

/-- A hidden-only multiplier of hidden degree d raises the weighted order
by at most d−3, with no regularity or finite-dimensionality shortcut. -/
theorem weightedSymbolBracket_hidden_multiplier_order (u : Smooth) (d : ℤ)
    (hu : HiddenDegreeLE d u) (hvis : ∀i : Fin 3,i≠2 → partialDerivative i u=0)
    (p : SmoothSymbol) (n : ℤ) (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE (n+d-3) (symbolBracket (C u) p) := by
  have hq := WeightedSymbolOrderLE.C u hu
  have hqv (i : Fin 3) (hi : i≠2) : symbolCoefficientDerivative i (C u)=0 := by
    rw [symbolCoefficientDerivative_C, hvis i hi, map_zero]
  rw [symbolBracket_eq_poisson_remainders, symbolCompositionRemainder_C_left,
    zero_sub, symbolPoisson, symbolFirstCorrection_C_left, zero_sub,
    symbolFirstCorrection_hiddenRight p (C u) hqv]
  have hcorr := (hp.pderiv 2).mul (hq.coefficientDerivative 2)
  have hcorr' : WeightedSymbolOrderLE (n+d-3)
      (pderiv 2 p*symbolCoefficientDerivative 2 (C u)) := by
    convert hcorr using 1 <;>
      norm_num [momentumCoordinateWeight, positionDerivativeWeight] <;> ring
  exact hcorr'.neg.add
    ((weightedSymbolCompositionRemainder_hiddenRight_order p (C u) n d hp hq hqv).neg.mono
      (by omega))

/-- A hidden-only vertical drift u(t)∂t of degree d raises actual weighted
order by at most d−1. The second-order composition remainder is six units lower. -/
theorem weightedSymbolBracket_hidden_drift_order (u : Smooth) (d : ℤ)
    (hu : HiddenDegreeLE d u) (hvis : ∀i : Fin 3,i≠2 → partialDerivative i u=0)
    (p : SmoothSymbol) (n : ℤ) (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE (n+d-1) (symbolBracket (C u*X 2) p) := by
  have hq : WeightedSymbolOrderLE (d+2) (C u*X 2) := by
    simpa [momentumCoordinateWeight] using
      (WeightedSymbolOrderLE.C u hu).mul (WeightedSymbolOrderLE.X 2)
  have hqv (i : Fin 3) (hi : i≠2) : symbolCoefficientDerivative i (C u*X 2)=0 := by
    rw [symbolCoefficientDerivative_mul, symbolCoefficientDerivative_C, hvis i hi,
      map_zero, zero_mul, symbolCoefficientDerivative_X, mul_zero, add_zero]
  rw [symbolBracket_eq_poisson_remainders, symbolCompositionRemainder_C_X_left,
    zero_sub, symbolPoisson, symbolFirstCorrection_C_mul,
    symbolFirstCorrection_X_left, symbolFirstCorrection_hiddenRight p (C u*X 2) hqv]
  have h₁ : WeightedSymbolOrderLE (n+d-1) (C u*symbolCoefficientDerivative 2 p) := by
    have hh := (WeightedSymbolOrderLE.C u hu).mul (hp.coefficientDerivative 2)
    convert hh using 1 <;> norm_num [positionDerivativeWeight] <;> ring
  have h₂ : WeightedSymbolOrderLE (n+d-1)
      (pderiv 2 p*symbolCoefficientDerivative 2 (C u*X 2)) := by
    have hh := (hp.pderiv 2).mul (hq.coefficientDerivative 2)
    convert hh using 1 <;>
      norm_num [momentumCoordinateWeight, positionDerivativeWeight] <;> ring
  exact (h₁.sub h₂).add
    ((weightedSymbolCompositionRemainder_hiddenRight_order p (C u*X 2) n (d+2) hp hq hqv).neg.mono
      (by omega))


end Wong.SmoothModel
