import Wong.NormalSymbolsRing
import Mathlib.Tactic.Module

/-!
# Ordinary principal symbols of actual smooth normal forms

The coefficient derivatives and momentum polynomials below are attached to
`normalAction` by proved identities for the actual composition operations.
-/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

/-- Differentiate every actual smooth coefficient, leaving momenta unchanged. -/
def symbolCoefficientDerivative (i : Fin 3) : SmoothSymbol →ₗ[ℝ] SmoothSymbol :=
  normalTotalSymbol.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (partialDerivative i)).comp normalTotalSymbol.symm.toLinearMap)

@[simp] theorem symbolCoefficientDerivative_coeff (i : Fin 3) (p : SmoothSymbol)
    (α : MultiIndex) : (symbolCoefficientDerivative i p).coeff α = partialDerivative i (p.coeff α) := rfl

@[simp] theorem symbolCoefficientDerivative_monomial (i : Fin 3) (α : MultiIndex)
    (u : Smooth) : symbolCoefficientDerivative i (monomial α u) =
      monomial α (partialDerivative i u) := by
  change normalTotalSymbol (Finsupp.mapRange (partialDerivative i) (map_zero _) (Finsupp.single α u)) = _
  rw [Finsupp.mapRange_single]
  rfl

@[simp] theorem symbolCoefficientDerivative_C (i : Fin 3) (u : Smooth) :
    symbolCoefficientDerivative i (C u) = C (partialDerivative i u) :=
  symbolCoefficientDerivative_monomial i 0 u

@[simp] theorem symbolCoefficientDerivative_X (i j : Fin 3) :
    symbolCoefficientDerivative i (X j) = 0 := by
  rw [X, symbolCoefficientDerivative_monomial]
  have hz : partialDerivative i (1 : Smooth) = 0 := by simpa using partialDerivative_const i 1
  rw [hz, monomial_zero]

/-- The usual product rule holds coefficientwise, with no formal derivative assumption. -/
theorem symbolCoefficientDerivative_mul (i : Fin 3) (p q : SmoothSymbol) :
    symbolCoefficientDerivative i (p * q) =
      symbolCoefficientDerivative i p * q + p * symbolCoefficientDerivative i q := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]; ring
  | monomial α u =>
    induction q using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]; ring
    | monomial β v =>
      simp only [monomial_mul_monomial, symbolCoefficientDerivative_monomial]
      rw [show partialDerivative i (u * v) =
        partialDerivative i u * v + u * partialDerivative i v from partialDerivative_smoothMul i u v]
      exact map_add (monomial (α + β)) _ _

/-- Ordinary left differentiation acts on the total symbol by `∂xi + ξi`. -/
theorem normalTotalSymbol_leftPartial (i : Fin 3) (p : NormalForm) :
    normalTotalSymbol (normalLeftPartial i p) =
      symbolCoefficientDerivative i (normalTotalSymbol p) + X i * normalTotalSymbol p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | single α u =>
    simp only [normalLeftPartial_single, map_add, normalTotalSymbol_single,
      symbolCoefficientDerivative_monomial, X, monomial_mul_monomial, one_mul]
    rw [add_comm (Finsupp.single i 1) α]

/-- Multiplication on the left is multiplication by the coefficient symbol. -/
theorem normalTotalSymbol_leftMultiplier (u : Smooth) (p : NormalForm) :
    normalTotalSymbol (normalLeftMultiplier u p) = C u * normalTotalSymbol p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | single α v =>
    simp only [normalLeftMultiplier_single, normalTotalSymbol_single, C_mul_monomial,
      smoothMul_eq_mul]

/-- A support definition of ordinary differential order for faithful normal forms. -/
def NormalDegreeLE (n : ℕ) (p : NormalForm) : Prop :=
  ∀ α : MultiIndex, n < α.degree → p α = 0

/-- The degree bound is exactly the usual polynomial bound on the total symbol. -/
theorem normalDegreeLE_iff (n : ℕ) (p : NormalForm) :
    NormalDegreeLE n p ↔ (normalTotalSymbol p).totalDegree ≤ n := by
  constructor
  · intro hp
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro α hα
    by_contra hn
    have hz := hp α (Nat.lt_of_not_ge hn)
    exact (MvPolynomial.mem_support_iff.mp hα) hz
  · intro hp α hα
    exact MvPolynomial.coeff_eq_zero_of_totalDegree_lt (hp.trans_lt hα)

/-- Coefficient differentiation cannot increase momentum degree. -/
theorem symbolCoefficientDerivative_totalDegree_le (i : Fin 3) (p : SmoothSymbol) :
    (symbolCoefficientDerivative i p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro α hα
  apply le_of_not_gt
  intro hgt
  have hz := MvPolynomial.coeff_eq_zero_of_totalDegree_lt hgt
  exact (MvPolynomial.mem_support_iff.mp hα) (by simp [hz])

/-- Coordinate coefficient differentiation commutes with extracting each homogeneous order. -/
theorem homogeneousComponent_symbolCoefficientDerivative (i : Fin 3) (n : ℕ)
    (p : SmoothSymbol) :
    homogeneousComponent n (symbolCoefficientDerivative i p) =
      symbolCoefficientDerivative i (homogeneousComponent n p) := by
  ext α
  simp only [coeff_homogeneousComponent, symbolCoefficientDerivative_coeff]
  split_ifs <;> simp

end Wong.SmoothModel
