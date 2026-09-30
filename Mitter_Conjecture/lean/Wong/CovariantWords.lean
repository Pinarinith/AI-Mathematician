import Wong.GeneratorCommutator
import Wong.FirstOrderExtraction
import Mathlib.Tactic.NoncommRing

/-!
# Actual covariant first-order Lie words and transported generators

Gauge conjugation transports the original scalar potential unchanged.
`filteringOperator` therefore permits that transported potential without
silently recomputing `eta`. All identities below are genuine equalities
of endomorphisms of the original globally smooth functions.
-/

noncomputable section
namespace Wong.SmoothModel

/-- The Euclidean filtering operator with its specified scalar potential. -/
def filteringOperator (f : Fin 3 → Smooth) (V : Smooth) : Operator :=
  (1 / 2 : ℝ) • (∑ i, D f i * D f i) -
    (1 / 2 : ℝ) • multiplication V

theorem filteringOperator_eta {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    filteringOperator f (eta f h) = L0 f h := rfl

theorem filteringOperator_mem_orderSpace_two (f : Fin 3 → Smooth) (V : Smooth) :
    filteringOperator f V ∈ orderSpace 2 := by
  apply (orderSpace 2).sub_mem
  · apply (orderSpace 2).smul_mem
    apply (orderSpace 2).sum_mem
    intro i _
    exact mul_mem_orderSpace (D_mem_orderSpace_one f i) (D_mem_orderSpace_one f i)
  · apply (orderSpace 2).smul_mem
    exact orderSpace_monotone (by decide : 0 ≤ 2)
      (multiplication_mem_orderSpace_zero V)

theorem lie_filteringOperator_multiplication (f : Fin 3 → Smooth) (V u : Smooth) :
    ⁅filteringOperator f V, multiplication u⁆ =
      (∑ i, multiplication (partialDerivative i u) * D f i) +
        (1 / 2 : ℝ) • multiplication (∑ i, partialDerivative i (partialDerivative i u)) := by
  simp only [filteringOperator, sub_lie, smul_lie, lie_multiplication_multiplication,
    smul_zero, sub_zero, sum_lie, lie_D_square_multiplication,
    Finset.smul_sum, smul_add, smul_smul, multiplication_sum]
  norm_num
  rw [Finset.sum_add_distrib]

theorem lie_filteringOperator_linearFunction (f : Fin 3 → Smooth) (V : Smooth)
    (v : State) :
    ⁅filteringOperator f V, multiplication (linearFunction v)⁆ = directionD f v := by
  rw [lie_filteringOperator_multiplication]
  simp only [partialDerivative_linearFunction, partialDerivative_const,
    Finset.sum_const_zero, multiplication_zero, smul_zero, add_zero,
    multiplication_smul, multiplication_smoothOne, smul_mul_assoc, one_mul, directionD]

def filteringRemainder (f : Fin 3 → Smooth) (V : Smooth) (i : Fin 3) : Smooth :=
  (1 / 2 : ℝ) • ((∑ j, partialDerivative j (wong f i j)) + partialDerivative i V)

theorem lie_filteringOperator_D (f : Fin 3 → Smooth) (V : Smooth) (i : Fin 3) :
    ⁅filteringOperator f V, D f i⁆ =
      (∑ j, multiplication (wong f i j) * D f j) +
        multiplication (filteringRemainder f V i) := by
  have hV : ⁅multiplication V, D f i⁆ = -multiplication (partialDerivative i V) := by
    rw [← lie_skew, lie_D_multiplication]
  simp only [filteringOperator, sub_lie, smul_lie, sum_lie, lie_D_square_D, hV,
    smul_neg, sub_neg_eq_add, Finset.smul_sum, smul_add, smul_smul,
    filteringRemainder, multiplication_smul, multiplication_add, multiplication_sum]
  norm_num
  rw [Finset.sum_add_distrib]
  abel

theorem operator_lie_mul_right (A B C : Operator) :
    ⁅A, B * C⁆ = ⁅A, B⁆ * C + B * ⁅A, C⁆ := by
  apply LinearMap.ext
  intro u
  change A (B (C u)) - B (C (A u)) =
    (A (B (C u)) - B (A (C u))) + B (A (C u) - C (A u))
  rw [map_sub]
  abel

theorem operator_lie_product_product (A B C T : Operator) :
    ⁅A * B, C * T⁆ = A * ⁅B, C⁆ * T + A * C * ⁅B, T⁆ +
      ⁅A, C⁆ * T * B + C * ⁅A, T⁆ * B := by
  apply LinearMap.ext
  intro u
  change A (B (C (T u))) - C (T (A (B u))) =
    A (B (C (T u)) - C (B (T u))) +
    A (C (B (T u) - T (B u))) +
    (A (C (T (B u))) - C (A (T (B u)))) +
    C (A (T (B u)) - T (A (B u)))
  simp only [map_sub]
  abel

/-- The curvature sign follows the manuscript's convention
`[D_j,D_i]=M_(wong i j)`. -/
theorem lie_covariant_monomials (f : Fin 3 → Smooth) (a c : Smooth) (i j : Fin 3) :
    ⁅multiplication a * D f i, multiplication c * D f j⁆ =
      multiplication (smoothMul a (partialDerivative i c)) * D f j -
      multiplication (smoothMul c (partialDerivative j a)) * D f i +
      multiplication (smoothMul (smoothMul a c) (wong f j i)) := by
  rw [operator_lie_product_product, lie_D_multiplication,
    lie_D_D, lie_multiplication_multiplication]
  have hsk : ⁅multiplication a, D f j⁆ =
      -multiplication (partialDerivative j a) := by
    rw [← lie_skew, lie_D_multiplication]
  rw [hsk]
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.neg_apply, LinearMap.zero_apply, multiplication_apply, smoothMul_apply,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg,
    Submodule.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply]
  ring

theorem lie_covariant_monomial_multiplier (f : Fin 3 → Smooth) (a u : Smooth)
    (i : Fin 3) :
    ⁅multiplication a * D f i, multiplication u⁆ =
      multiplication (smoothMul a (partialDerivative i u)) := by
  rw [operator_lie_mul_left, lie_D_multiplication,
    lie_multiplication_multiplication, zero_mul, add_zero, multiplication_mul]

theorem firstOrder_mem_orderSpace_one (f a : Fin 3 → Smooth) (b : Smooth) :
    firstOrder f a b ∈ orderSpace 1 := by
  apply (orderSpace 1).add_mem
  · apply (orderSpace 1).sum_mem
    intro i _
    exact mul_mem_orderSpace (multiplication_mem_orderSpace_zero _) (D_mem_orderSpace_one f i)
  · exact orderSpace_le_succ 0 (multiplication_mem_orderSpace_zero b)

theorem lie_D_firstOrder (f a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    ⁅D f i, firstOrder f a b⁆ =
      firstOrder f (fun j => partialDerivative i (a j))
        (partialDerivative i b + ∑ j, smoothMul (a j) (wong f j i)) := by
  simp only [firstOrder, lie_add, lie_sum, operator_lie_mul_right,
    lie_D_multiplication, lie_D_D, multiplication_mul,
    Finset.sum_add_distrib, multiplication_add, multiplication_sum]
  abel

theorem firstOrder_scalar_constant (f a : Fin 3 → Smooth) (b : Smooth) (c : ℝ) :
    firstOrder f a (b + c • smoothOne) = firstOrder f a b + c • (1 : Operator) := by
  simp only [firstOrder, multiplication_add, multiplication_smul,
    multiplication_smoothOne]
  abel

end Wong.SmoothModel
