import Wong.GeneratorCommutator
import Wong.PublishedAffineStatement
import Wong.CovariantWords

/-! Three genuine multiplier words give the visible Hessian compatibility
obstruction. The hypotheses do not prohibit hidden quadratic multipliers. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Wong.SmoothModel
open MvPolynomial

theorem visibleFiltering_multiplication_neg (u : Smooth) :
    multiplication (-u) = -multiplication u := multiplicationLinear.map_neg u

theorem visibleFiltering_smoothMul_neg_right (u v : Smooth) :
    smoothMul u (-v) = -smoothMul u v := by
  apply Subtype.ext
  funext x
  exact mul_neg _ _

theorem visibleFiltering_smoothMul_neg_left (u v : Smooth) :
    smoothMul (-u) v = -smoothMul u v := by
  apply Subtype.ext
  funext x
  exact neg_mul _ _

def visibleFilteringOperator (f : Fin 3 → Smooth) (V : Smooth) : Operator :=
  (1 / 2 : ℝ) • (D f 0 * D f 0 + D f 1 * D f 1) -
    (1 / 2 : ℝ) • multiplication V

theorem visibleFiltering_lie_D_zero (f : Fin 3 → Smooth) (V : Smooth) :
    ⁅visibleFilteringOperator f V, D f 0⁆ =
      multiplication (wong f 0 1) * D f 1 +
        (1 / 2 : ℝ) • multiplication
          (partialDerivative 1 (wong f 0 1) + partialDerivative 0 V) := by
  have hself : ⁅D f 0 * D f 0, D f 0⁆ = 0 := by
    simp [operator_lie_mul_left]
  have hscalar : ⁅multiplication V, D f 0⁆ = -multiplication (partialDerivative 0 V) := by
    rw [← lie_skew, lie_D_multiplication]
  simp only [visibleFilteringOperator, sub_lie, smul_lie, add_lie,
    hself, zero_add, lie_D_square_D, hscalar, multiplication_add, smul_add]
  module

theorem visibleFiltering_lie_D_one (f : Fin 3 → Smooth) (V : Smooth) :
    ⁅visibleFilteringOperator f V, D f 1⁆ =
      multiplication (wong f 1 0) * D f 0 +
        (1 / 2 : ℝ) • multiplication
          (partialDerivative 0 (wong f 1 0) + partialDerivative 1 V) := by
  have hself : ⁅D f 1 * D f 1, D f 1⁆ = 0 := by
    simp [operator_lie_mul_left]
  have hscalar : ⁅multiplication V, D f 1⁆ = -multiplication (partialDerivative 1 V) := by
    rw [← lie_skew, lie_D_multiplication]
  simp only [visibleFilteringOperator, sub_lie, smul_lie, add_lie,
    hself, add_zero, lie_D_square_D, hscalar, multiplication_add, smul_add]
  module

theorem visibleFiltering_actual_three_multipliers {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (V : Smooth)
    (hP : visibleFilteringOperator f V ∈ estimationAlgebra f h)
    (hD0 : D f 0 ∈ estimationAlgebra f h) (hD1 : D f 1 ∈ estimationAlgebra f h)
    (k l : ℝ)
    (hw0 : partialDerivative 0 (wong f 0 1) = k • smoothOne)
    (hw1 : partialDerivative 1 (wong f 0 1) = l • smoothOne) :
    multiplication ((1 / 2 : ℝ) • partialDerivative 0 (partialDerivative 0 V) -
      smoothMul (wong f 0 1) (wong f 0 1)) ∈ estimationAlgebra f h ∧
    multiplication ((1 / 2 : ℝ) • partialDerivative 1 (partialDerivative 1 V) -
      smoothMul (wong f 0 1) (wong f 0 1)) ∈ estimationAlgebra f h ∧
    multiplication ((1 / 2 : ℝ) • partialDerivative 1 (partialDerivative 0 V)) ∈
      estimationAlgebra f h := by
  have hOne (i : Fin 3) : partialDerivative i smoothOne = 0 := by
    simpa only [one_smul] using partialDerivative_const i 1
  have h10 : wong f 1 0 = -wong f 0 1 := wong_skew f 0 1
  have he00 : ⁅D f 0, ⁅visibleFilteringOperator f V, D f 0⁆⁆ =
      k • D f 1 + multiplication
        ((1 / 2 : ℝ) • partialDerivative 0 (partialDerivative 0 V) -
          smoothMul (wong f 0 1) (wong f 0 1)) := by
    rw [visibleFiltering_lie_D_zero]
    rw [lie_add, lie_smul, operator_lie_mul_right, lie_D_multiplication,
      lie_D_D, lie_D_multiplication]
    simp only [lie_add, lie_smul, operator_lie_mul_right, lie_D_multiplication,
      lie_D_D, h10, hw0, hw1, map_add, map_smul, partialDerivative_const, hOne, smul_zero, add_zero,
      zero_add, multiplication_smul, multiplication_smoothOne, smul_mul_assoc,
      one_mul, mul_neg, neg_mul, multiplication_mul, multiplication_add, multiplication_sub,
      visibleFiltering_smoothMul_neg_right, visibleFiltering_multiplication_neg]
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, Module.End.mul_apply, Module.End.one_apply,
      multiplication_apply, smoothMul_apply, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_zero, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, smoothOne]
    ring
  have he11 : ⁅D f 1, ⁅visibleFilteringOperator f V, D f 1⁆⁆ =
      -l • D f 0 + multiplication
        ((1 / 2 : ℝ) • partialDerivative 1 (partialDerivative 1 V) -
          smoothMul (wong f 0 1) (wong f 0 1)) := by
    rw [visibleFiltering_lie_D_one]
    rw [lie_add, lie_smul, operator_lie_mul_right, lie_D_multiplication,
      lie_D_D, lie_D_multiplication]
    simp only [lie_add, lie_smul, operator_lie_mul_right, lie_D_multiplication,
      lie_D_D, h10, hw0, hw1, map_neg, map_add, map_smul, partialDerivative_const, hOne, smul_zero, add_zero,
      neg_zero, zero_add, multiplication_smul, multiplication_smoothOne,
      smul_mul_assoc, one_mul, mul_neg, neg_mul, multiplication_mul, multiplication_add,
      multiplication_sub, visibleFiltering_smoothMul_neg_left, visibleFiltering_multiplication_neg]
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, Module.End.mul_apply, Module.End.one_apply,
      multiplication_apply, smoothMul_apply, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_zero, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, smoothOne]
    ring
  have he01 : ⁅D f 1, ⁅visibleFilteringOperator f V, D f 0⁆⁆ =
      l • D f 1 + multiplication
        ((1 / 2 : ℝ) • partialDerivative 1 (partialDerivative 0 V)) := by
    rw [visibleFiltering_lie_D_zero]
    simp only [lie_add, lie_smul, operator_lie_mul_right, lie_D_multiplication,
      lie_self, hw1, map_add, partialDerivative_const, zero_add, mul_zero,
      add_zero, multiplication_smul, multiplication_smoothOne, smul_mul_assoc, one_mul]
  have hm00 := (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).lie_mem hD0 ((estimationAlgebra f h).lie_mem hP hD0))
    ((estimationAlgebra f h).smul_mem k hD1)
  have hm11 := (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).lie_mem hD1 ((estimationAlgebra f h).lie_mem hP hD1))
    ((estimationAlgebra f h).smul_mem (-l) hD0)
  have hm01 := (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).lie_mem hD1 ((estimationAlgebra f h).lie_mem hP hD0))
    ((estimationAlgebra f h).smul_mem l hD1)
  simp only [he00, he11, he01, add_sub_cancel_left] at hm00 hm11 hm01
  exact ⟨hm00, hm11, hm01⟩

theorem visibleFiltering_wong_slopes_zero_of_visible_hessian_free {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (V : Smooth)
    (hP : visibleFilteringOperator f V ∈ estimationAlgebra f h)
    (hD0 : D f 0 ∈ estimationAlgebra f h) (hD1 : D f 1 ∈ estimationAlgebra f h)
    (hF : ∀ u : Smooth, multiplication u ∈ estimationAlgebra f h →
      ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 → partialDerivative i (partialDerivative j u) = 0)
    (c k l : ℝ)
    (hw : wong f 0 1 = polynomialSmooth (C c + C k * X 0 + C l * X 1)) :
    k = 0 ∧ l = 0 := by
  have hw0 : partialDerivative 0 (wong f 0 1) = k • smoothOne := by
    rw [hw, partialDerivative_polynomialSmooth]
    simp
  have hw1 : partialDerivative 1 (wong f 0 1) = l • smoothOne := by
    rw [hw, partialDerivative_polynomialSmooth]
    simp
  obtain ⟨hm00, hm11, hm01⟩ := visibleFiltering_actual_three_multipliers
    f h V hP hD0 hD1 k l hw0 hw1
  have h00 := hF _ hm00 1 1 (by decide) (by decide)
  have h11 := hF _ hm11 0 0 (by decide) (by decide)
  have h01 := hF _ hm01 1 0 (by decide) (by decide)
  have hsquare (i : Fin 3) (a : ℝ) (ha : partialDerivative i (wong f 0 1) = a • smoothOne) :
      partialDerivative i (partialDerivative i (smoothMul (wong f 0 1) (wong f 0 1))) =
      (2*a^2 : ℝ) • smoothOne := by
    rw [partialDerivative_smoothMul, map_add, partialDerivative_smoothMul,
      partialDerivative_smoothMul, ha, partialDerivative_const]
    apply Subtype.ext
    funext x
    simp [smoothMul_apply, smoothOne]
    ring
  simp only [map_sub, map_smul, hsquare 1 l hw1, hsquare 0 k hw0] at h00 h11
  simp only [map_smul] at h01
  rw [partialDerivative_commute_apply 0 1 (partialDerivative 0 V)] at h01
  have hv : partialDerivative 1 (partialDerivative 1 (partialDerivative 0 (partialDerivative 0 V))) = 0 := by
    exact (smul_eq_zero.mp h01).resolve_left (by norm_num)
  rw [hv, smul_zero, zero_sub] at h00
  have hv' : partialDerivative 0 (partialDerivative 0 (partialDerivative 1 (partialDerivative 1 V))) = 0 := by
    rw [partialDerivative_commute_apply 0 1 (partialDerivative 1 V),
      partialDerivative_commute_apply 0 1 (partialDerivative 0 (partialDerivative 1 V)),
      partialDerivative_commute_apply 0 1 V,
      partialDerivative_commute_apply 0 1 (partialDerivative 0 V)]
    exact hv
  rw [hv', smul_zero, zero_sub] at h11
  have hk := congrArg (fun u : Smooth => u.1 (0 : State)) h11
  have hl := congrArg (fun u : Smooth => u.1 (0 : State)) h00
  simp [smoothOne] at hk hl
  constructor <;> nlinarith [sq_nonneg k, sq_nonneg l]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visibleFiltering_wong_slopes_zero_of_visible_hessian_free
