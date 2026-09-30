import Wong.NormalSymbolsComposition
import Wong.SharpDifferentialOrder

/-! The support order of the faithful ordinary normal form agrees with the
actual multiplier-commutator differential order. -/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

/-- Quantization is the existing faithful action, after linear symbol repackaging. -/
def normalQuantize : SmoothSymbol →ₗ[ℝ] Operator :=
  normalAction.comp normalTotalSymbol.symm.toLinearMap

@[simp] theorem normalQuantize_apply (p : SmoothSymbol) :
    normalQuantize p = normalAction (normalTotalSymbol.symm p) := rfl

@[simp] theorem normalQuantize_totalSymbol (p : NormalForm) :
    normalQuantize (normalTotalSymbol p) = normalAction p := by
  simp [normalQuantize]

@[simp] theorem normalQuantize_monomial (α : MultiIndex) (u : Smooth) :
    normalQuantize (monomial α u) = multiplication u * multiPartial α :=
  normalAction_single α u

@[simp] theorem normalQuantize_momentum (α : MultiIndex) :
    normalQuantize (monomial α (1 : Smooth)) = multiPartial α := by
  rw [normalQuantize_monomial]
  change multiplication smoothOne * multiPartial α = _
  rw [multiplication_smoothOne, one_mul]

theorem normalQuantize_C_mul (u : Smooth) (p : SmoothSymbol) :
    normalQuantize (C u * p) = multiplication u * normalQuantize p := by
  have hh := congrArg normalQuantize
    (normalTotalSymbol_leftMultiplier u (normalTotalSymbol.symm p))
  simpa only [normalQuantize_totalSymbol, LinearEquiv.apply_symm_apply,
    normalAction_leftMultiplier, normalQuantize_apply, LinearEquiv.symm_apply_apply] using hh.symm

theorem normalQuantize_X_mul (i : Fin 3) (p : SmoothSymbol) :
    normalQuantize (X i * p) = partialDerivative i * normalQuantize p -
      normalQuantize (symbolCoefficientDerivative i p) := by
  have hh := congrArg normalQuantize
    (normalTotalSymbol_leftPartial i (normalTotalSymbol.symm p))
  simp only [normalQuantize_totalSymbol, LinearEquiv.apply_symm_apply,
    normalAction_leftPartial, map_add] at hh
  exact eq_sub_of_add_eq (by simpa only [add_comm, normalQuantize_apply] using hh.symm)

theorem lie_multiPartial_coordinate (α : MultiIndex) (i : Fin 3) :
    ⁅multiPartial α, multiplication (linearFunction (coordinateVector i))⁆ =
      normalQuantize (pderiv i (monomial α (1 : Smooth))) := by
  induction α using multiIndex_induction with
  | hzero =>
    simp only [multiPartial_zero, show monomial (0 : MultiIndex) (1 : Smooth) = 1 from rfl,
      pderiv_one, map_zero]
    simpa only [one_smul] using scalar_identity_lie 1 _
  | hstep α j ih =>
    rw [multiPartial_shift, operator_lie_mul_left, ih]
    have hj : ⁅partialDerivative j, multiplication (linearFunction (coordinateVector i))⁆ =
        if j = i then (1 : Operator) else 0 := by
      rw [lie_partial_multiplication, partialDerivative_linearFunction,
        multiplication_smul, multiplication_smoothOne]
      simp [coordinateVector, Pi.single_apply, ite_smul]
    have hm : monomial (α + Finsupp.single j 1) (1 : Smooth) = X j * monomial α 1 := by
      simp [X, monomial_mul_monomial, add_comm]
    rw [hj, hm, pderiv_mul, pderiv_X, map_add]
    rw [normalQuantize_X_mul, coefficientDerivative_pderiv_momentum, map_zero, sub_zero]
    by_cases hji : j = i
    · subst j
      simp only [Pi.single_apply, ite_true, one_mul, normalQuantize_momentum]
      exact add_comm _ _
    · simp only [Pi.single_apply, hji, ite_false, zero_mul, map_zero, zero_add, add_zero]

/-- A coordinate multiplier commutator is the actual momentum partial derivative. -/
theorem normalQuantize_pderiv (p : SmoothSymbol) (i : Fin 3) :
    normalQuantize (pderiv i p) =
      ⁅normalQuantize p, multiplication (linearFunction (coordinateVector i))⁆ := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_lie, hp, hq]
  | monomial α u =>
    have hm : monomial α u = C u * monomial α 1 := by rw [C_mul_monomial, mul_one]
    rw [hm, pderiv_C_mul, normalQuantize_C_mul, normalQuantize_C_mul,
      normalQuantize_momentum, operator_lie_mul_left, lie_multiplication_multiplication,
      zero_mul, add_zero, lie_multiPartial_coordinate]

@[simp] theorem smooth_coe_natCast (n : ℕ) (x : State) :
    (n : Smooth).1 x = (n : ℝ) := by
  change (n : ℝ) * 1 = (n : ℝ)
  exact mul_one _

/-- Actual differential-order bounds imply the same bound on the unique normal support. -/
theorem normalDegreeLE_of_action_order (p : NormalForm) (n : ℕ)
    (hp : normalAction p ∈ orderSpace n) : NormalDegreeLE n p := by
  induction n generalizing p with
  | zero =>
    have he := orderSpace_zero_representation hp
    have hform : p = Finsupp.single 0 (normalAction p smoothOne) :=
      normalAction_injective (he.trans (normalAction_scalar _).symm)
    rw [hform]
    intro α hα
    have hn : (0 : MultiIndex) ≠ α := by
      intro he
      rw [← he] at hα
      simp at hα
    simp [hn]
  | succ n ih =>
    have hpartial (i : Fin 3) :
        NormalDegreeLE n (normalTotalSymbol.symm (pderiv i (normalTotalSymbol p))) := by
      apply ih
      change normalQuantize (pderiv i (normalTotalSymbol p)) ∈ orderSpace n
      rw [normalQuantize_pderiv, normalQuantize_totalSymbol]
      exact mem_orderSpace_succ.mp hp (linearFunction (coordinateVector i))
    intro α hα
    have hi : ∃ i, α i ≠ 0 := by
      by_contra hh
      push Not at hh
      have ha : α = 0 := Finsupp.ext hh
      simp [ha] at hα
    obtain ⟨i, hi⟩ := hi
    have hle : Finsupp.single i 1 ≤ α := by rw [Finsupp.single_le_iff]; omega
    let β := α - Finsupp.single i 1
    have he : β + Finsupp.single i 1 = α := tsub_add_cancel_of_le hle
    have hd : β.degree + 1 = α.degree := by
      rw [← Finsupp.degree_single i (1 : ℕ), ← map_add, he]
    have hz : (pderiv i (normalTotalSymbol p)).coeff β = 0 := hpartial i β (by omega)
    rw [coeff_pderiv, he, normalTotalSymbol_coeff] at hz
    apply Subtype.ext
    funext x
    have hh := congrArg (fun u : Smooth => u.1 x) hz
    have hh' : (p α).1 x * ((β i : ℝ) + 1) = 0 := by
      simpa only [smooth_coe_mul, Submodule.coe_add, Pi.add_apply, smooth_coe_natCast,
        smooth_coe_one, Submodule.coe_zero, Pi.zero_apply] using hh
    exact (mul_eq_zero.mp hh').resolve_right (by positivity)

/-- Every normally ordered derivative monomial has its expected actual order. -/
theorem multiPartial_mem_orderSpace (α : MultiIndex) :
    multiPartial α ∈ orderSpace α.degree := by
  induction α using multiIndex_induction with
  | hzero =>
    rw [multiPartial_zero]
    simpa only [map_zero, multiplication_smoothOne] using multiplication_mem_orderSpace_zero smoothOne
  | hstep α i ih =>
    rw [multiPartial_shift]
    have hh := mul_mem_orderSpace (partialDerivative_mem_orderSpace_one i) ih
    simpa only [map_add, Finsupp.degree_single, Nat.add_comm 1 α.degree] using hh

/-- Conversely, a finite normal support of degree at most n acts with actual order at most n. -/
theorem action_order_of_normalDegreeLE (p : NormalForm) (n : ℕ) (hp : NormalDegreeLE n p) :
    normalAction p ∈ orderSpace n := by
  classical
  change (p.sum fun α u => multiplication u * multiPartial α) ∈ orderSpace n
  apply (orderSpace n).sum_mem
  intro α hα
  have hdeg : α.degree ≤ n := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hα) (hp α (by omega))
  have hh := mul_mem_orderSpace (multiplication_mem_orderSpace_zero (p α))
    (multiPartial_mem_orderSpace α)
  exact orderSpace_monotone (by simpa using hdeg) hh

theorem normalDegreeLE_iff_action_order (p : NormalForm) (n : ℕ) :
    NormalDegreeLE n p ↔ normalAction p ∈ orderSpace n :=
  ⟨action_order_of_normalDegreeLE p n, normalDegreeLE_of_action_order p n⟩

end Wong.SmoothModel
