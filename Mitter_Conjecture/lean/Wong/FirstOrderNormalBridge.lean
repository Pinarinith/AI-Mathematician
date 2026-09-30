import Wong.CovariantWords
import Wong.NormalSymbolsPrincipal

/-! A genuine first-order covariant operator has its faithful ordinary normal
form and exactly the displayed principal symbol, including its scalar remainder. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

def normalFirstOrder (f a : Fin 3 → Smooth) (b : Smooth) : NormalForm :=
  (∑ i, Finsupp.single (Finsupp.single i 1) (a i)) +
    Finsupp.single 0 (b - ∑ i, smoothMul (a i) (f i))

theorem normalAction_normalFirstOrder (f a : Fin 3 → Smooth) (b : Smooth) :
    normalAction (normalFirstOrder f a b) = firstOrder f a b := by
  have hm (i : Fin 3) : multiPartial (Finsupp.single i 1) = partialDerivative i := by
    simpa using multiPartial_shift 0 i
  simp only [normalFirstOrder, map_add, map_sum, normalAction_single, hm,
    multiPartial_zero, mul_one, multiplication_sub, multiplication_sum,
    firstOrder, D, mul_sub, multiplication_mul, Finset.sum_sub_distrib]
  abel

theorem normalFirstOrder_degree_le_one (f a : Fin 3 → Smooth) (b : Smooth) :
    NormalDegreeLE 1 (normalFirstOrder f a b) := by
  apply normalDegreeLE_of_action_order
  rw [normalAction_normalFirstOrder]
  exact firstOrder_mem_orderSpace_one f a b

theorem normalSymbol_one_normalFirstOrder (f a : Fin 3 → Smooth) (b : Smooth) :
    normalSymbol 1 (normalFirstOrder f a b) = ∑ i, C (a i) * X i := by
  simp only [normalFirstOrder, normalSymbol_add, normalSymbol_sum, normalSymbol_single,
    Finsupp.degree_single, ite_true, map_zero, zero_ne_one, ite_false, add_zero,
    C_mul_X_eq_monomial]

theorem exists_actual_normal_firstOrder (f a : Fin 3 → Smooth) (b : Smooth) :
    ∃ p : NormalForm, NormalDegreeLE 1 p ∧ normalAction p = firstOrder f a b ∧
      normalSymbol 1 p = ∑ i, C (a i) * X i :=
  ⟨normalFirstOrder f a b, normalFirstOrder_degree_le_one f a b,
    normalAction_normalFirstOrder f a b, normalSymbol_one_normalFirstOrder f a b⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.exists_actual_normal_firstOrder
