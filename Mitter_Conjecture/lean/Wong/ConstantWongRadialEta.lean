import Wong.VisibleWongQuadraticAnalysis
import Wong.SmoothEulerResolventRegularity

/-! Genuine full radial Lie words give global quadratic eta. Every operator
acts on the original globally smooth functions; its scalar term is retained. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open MvPolynomial

def constantWongRadialZ (f : Fin 3 → Smooth) : Operator :=
  ∑ i : Fin 3, multiplication (linearFunction (coordinateVector i)) * D f i

def constantWongRadialB (f : Fin 3 → Smooth) (i : Fin 3) : Smooth :=
  -(∑ j : Fin 3, smoothMul (linearFunction (coordinateVector j)) (wong f i j))

def constantWongRadialK (f : Fin 3 → Smooth) : Operator :=
  ∑ i : Fin 3, multiplication (constantWongRadialB f i) * D f i

theorem full_coordinateEuler_apply_sum (u : Smooth) :
    coordinateEuler Finset.univ u =
      ∑ i : Fin 3, smoothMul (linearFunction (coordinateVector i)) (partialDerivative i u) := by
  simp only [coordinateEuler, Finset.mem_univ, if_true, LinearMap.sum_apply,
    Module.End.mul_apply, multiplication_apply]

theorem full_coordinateEuler_linearFunction (a : State) :
    coordinateEuler Finset.univ (linearFunction a) = linearFunction a := by
  rw [full_coordinateEuler_apply_sum]
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply, smoothMul_apply,
    partialDerivative_linearFunction, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, smoothOne, mul_one]
  simp [linearFunction, coordinateVector, Pi.single_apply, mul_comm]

theorem constantWongRadialZ_lie_multiplier (f : Fin 3 → Smooth) (u : Smooth) :
    ⁅constantWongRadialZ f, multiplication u⁆ =
      multiplication (coordinateEuler Finset.univ u) := by
  simp only [constantWongRadialZ, sum_lie, lie_covariant_monomial_multiplier,
    full_coordinateEuler_apply_sum, multiplication_sum]

theorem constantWongRadialZ_lie_D (f : Fin 3 → Smooth) (i : Fin 3) :
    ⁅constantWongRadialZ f, D f i⁆ = -D f i - multiplication (constantWongRadialB f i) := by
  have hMD (j : Fin 3) :
      ⁅multiplication (linearFunction (coordinateVector j)), D f i⁆ =
      -(coordinateVector j i) • (1 : Operator) := by
    rw [← lie_skew, lie_D_multiplication, partialDerivative_linearFunction,
      multiplication_smul, multiplication_smoothOne, neg_smul]
  simp only [constantWongRadialZ, sum_lie, operator_lie_mul_left,
    lie_D_D, hMD, multiplication_mul, constantWongRadialB,
    multiplication_neg_smooth, multiplication_sum]
  fin_cases i <;>
    simp [Fin.sum_univ_three, coordinateVector, Pi.single_apply, smul_mul_assoc, one_mul] <;>
    try simp only [smul_mul_assoc, one_mul, mul_smul_comm, neg_smul, one_smul]
  all_goals
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, Module.End.mul_apply, Module.End.one_apply,
      map_neg, map_add, map_sub, map_smul, multiplication_apply, smoothMul_apply,
      Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul,
      Submodule.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul, smoothOne]
    ring

theorem constantWongRadialB_linear {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (Ω : Fin 3 → Fin 3 → ℝ)
    (hW : ∀ i j x, (wong f i j).1 x = Ω i j) (i : Fin 3) :
    constantWongRadialB f i = -linearFunction (Ω i) := by
  apply Subtype.ext
  funext x
  simp [constantWongRadialB, linearFunction, coordinateVector,
    Pi.single_apply, hW, mul_comm]

theorem constantWongRadialB_partial_diagonal_zero (f : Fin 3 → Smooth)
    (hW : ∀ i j k, partialDerivative k (wong f i j) = 0) (i : Fin 3) :
    partialDerivative i (constantWongRadialB f i) = 0 := by
  rw [constantWongRadialB, map_neg, map_sum]
  simp_rw [partialDerivative_smoothMul, partialDerivative_linearFunction, hW]
  apply Subtype.ext
  funext x
  fin_cases i <;> simp [Fin.sum_univ_three, coordinateVector, Pi.single_apply,
    wong_self, smoothMul_apply, smoothOne]

theorem constantWongRadialZ_lie_D_square (f : Fin 3 → Smooth)
    (hW : ∀ i j k, partialDerivative k (wong f i j) = 0) (i : Fin 3) :
    ⁅constantWongRadialZ f, D f i * D f i⁆ =
      (-2 : ℝ) • (D f i * D f i) -
        (2 : ℝ) • (multiplication (constantWongRadialB f i) * D f i) := by
  rw [operator_lie_mul_right, constantWongRadialZ_lie_D]
  simp only [mul_sub, sub_mul, mul_neg, neg_mul]
  rw [D_mul_multiplication, constantWongRadialB_partial_diagonal_zero f hW i,
    multiplication_zero, add_zero]
  try simp only [mul_neg, neg_mul, neg_add, mul_sub, sub_mul]
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, Module.End.mul_apply, Module.End.one_apply,
    map_neg, map_add, map_sub, map_smul, multiplication_apply, smoothMul_apply,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul,
    Submodule.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul, smoothOne]
  ring

theorem constantWongRadialZ_lie_K (f : Fin 3 → Smooth)
    (hB : ∀ i, coordinateEuler Finset.univ (constantWongRadialB f i) =
      constantWongRadialB f i) :
    ⁅constantWongRadialZ f, constantWongRadialK f⁆ =
      -multiplication (∑ i : Fin 3, smoothMul (constantWongRadialB f i)
        (constantWongRadialB f i)) := by
  simp only [constantWongRadialK, lie_sum, operator_lie_mul_right,
    constantWongRadialZ_lie_multiplier, hB, constantWongRadialZ_lie_D,
    mul_sub, mul_neg, multiplication_mul, multiplication_sum]
  simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, neg_smul, one_smul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
    multiplication_apply, smoothMul_apply, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_sum, Pi.add_apply,
    Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    Fin.sum_univ_three]
  ring

theorem constantWongRadial_L0_word {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hW : ∀ i j k, partialDerivative k (wong f i j) = 0) :
    ⁅L0 f h, constantWongRadialZ f⁆ =
      (∑ i : Fin 3, D f i * D f i) + constantWongRadialK f +
        (1 / 2 : ℝ) • multiplication (coordinateEuler Finset.univ (eta f h)) := by
  rw [← lie_skew]
  simp only [L0, lie_sub, lie_smul, lie_sum, constantWongRadialZ_lie_D_square f hW,
    constantWongRadialZ_lie_multiplier, Finset.sum_sub_distrib, ← Finset.smul_sum,
    constantWongRadialK]
  module

theorem constantWongRadial_eta_resolvent_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hW : ∀ i j k, partialDerivative k (wong f i j) = 0)
    (hB : ∀ i, coordinateEuler Finset.univ (constantWongRadialB f i) =
      constantWongRadialB f i)
    (hZ : constantWongRadialZ f ∈ estimationAlgebra f h) :
    multiplication ((1 / 2 : ℝ) •
      ((coordinateEuler Finset.univ + (0 : ℝ) • (1 : Operator))
        ((coordinateEuler Finset.univ + (2 : ℝ) • (1 : Operator)) (eta f h))) -
      ∑ i : Fin 3, smoothMul (constantWongRadialB f i) (constantWongRadialB f i)) ∈
      estimationAlgebra f h := by
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hK := (estimationAlgebra f h).lie_mem hL hZ
  have hm := (estimationAlgebra f h).add_mem
    ((estimationAlgebra f h).lie_mem hZ hK)
    ((estimationAlgebra f h).smul_mem (2 : ℝ) hK)
  have heq : ⁅constantWongRadialZ f, ⁅L0 f h, constantWongRadialZ f⁆⁆ +
      (2 : ℝ) • ⁅L0 f h, constantWongRadialZ f⁆ =
      multiplication ((1 / 2 : ℝ) •
        ((coordinateEuler Finset.univ + (0 : ℝ) • (1 : Operator))
          ((coordinateEuler Finset.univ + (2 : ℝ) • (1 : Operator)) (eta f h))) -
        ∑ i : Fin 3, smoothMul (constantWongRadialB f i) (constantWongRadialB f i)) := by
    rw [constantWongRadial_L0_word f h hW]
    rw [lie_add, lie_add, lie_sum, constantWongRadialZ_lie_K f hB]
    simp only [constantWongRadial_L0_word f h hW, lie_add, lie_sum,
      constantWongRadialZ_lie_D_square f hW, constantWongRadialZ_lie_K f hB,
      lie_smul, constantWongRadialZ_lie_multiplier, Finset.sum_sub_distrib,
      ← Finset.smul_sum, constantWongRadialK, zero_smul, add_zero,
      LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul, multiplication_sub, multiplication_smul, multiplication_add]
    module
  rwa [heq] at hm


theorem fullRadialQuadratic_L0_word {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    ⁅L0 f h, multiplication (polynomialSmooth fullRadialQuadraticPolynomial)⁆ =
      (2 : ℝ) • constantWongRadialZ f + (3 : ℝ) • (1 : Operator) := by
  have hpoly : fullRadialQuadraticPolynomial = ∑ i : Fin 3, (X i : RealPoly)^2 := by
    simp [fullRadialQuadraticPolynomial, Fin.sum_univ_three]
  rw [hpoly, polynomialSmooth_sum, multiplication_sum, lie_sum]
  simp only [lie_L0_polynomial_coordinate_square, polynomialSmooth_coordinate]
  simp only [constantWongRadialZ, Fin.sum_univ_three]
  module

theorem constantWongRadialZ_mem_of_full_radial_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : multiplication (polynomialSmooth fullRadialQuadraticPolynomial) ∈
      estimationAlgebra f h) : constantWongRadialZ f ∈ estimationAlgebra f h := by
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hm := (estimationAlgebra f h).sub_mem ((estimationAlgebra f h).lie_mem hL hq)
    ((estimationAlgebra f h).smul_mem (3 : ℝ)
      (one_mem_estimationAlgebra_of_rank_two f h hrank))
  rw [fullRadialQuadratic_L0_word, add_sub_cancel_right] at hm
  have hs := (estimationAlgebra f h).smul_mem (1 / 2 : ℝ) hm
  simpa only [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] using hs

theorem quadratic_eta_of_constant_wong_full_radial_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hW : WongConstant f)
    (hq : multiplication (polynomialSmooth fullRadialQuadraticPolynomial) ∈
      estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = eta f h := by
  obtain ⟨Ω, hΩ⟩ := hW
  have hd : ∀ i j k, partialDerivative k (wong f i j) = 0 :=
    (wongConstant_iff_partials_zero f).mp ⟨Ω, hΩ⟩
  have hB (i : Fin 3) : coordinateEuler Finset.univ (constantWongRadialB f i) =
      constantWongRadialB f i := by
    rw [constantWongRadialB_linear f h Ω hΩ i, map_neg,
      full_coordinateEuler_linearFunction]
  let B : Fin 3 → RealPoly := fun i => -(∑ j : Fin 3, C (Ω i j) * X j)
  have hBpoly (i : Fin 3) : polynomialSmooth (B i) = constantWongRadialB f i := by
    rw [constantWongRadialB_linear f h Ω hΩ i]
    apply Subtype.ext
    funext x
    simp [B, polynomialSmooth, linearFunction, mul_comm]
  have hBdegree (i : Fin 3) : (B i).totalDegree ≤ 1 := by
    dsimp only [B]
    rw [totalDegree_neg]
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simp)
  let S : RealPoly := ∑ i : Fin 3, (B i)^2
  have hS : S.totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_pow _ 2).trans (by have := hBdegree i; omega)
  have hSpoly : polynomialSmooth S =
      ∑ i : Fin 3, smoothMul (constantWongRadialB f i) (constantWongRadialB f i) := by
    simp only [S, polynomialSmooth_sum, pow_two, polynomialSmooth_mul, hBpoly]
  let F : Smooth := (1 / 2 : ℝ) •
    ((coordinateEuler Finset.univ + (0 : ℝ) • (1 : Operator))
      ((coordinateEuler Finset.univ + (2 : ℝ) • (1 : Operator)) (eta f h))) -
    ∑ i : Fin 3, smoothMul (constantWongRadialB f i) (constantWongRadialB f i)
  have hF := constantWongRadial_eta_resolvent_member f h hd hB
    (constantWongRadialZ_mem_of_full_radial_member f h hrank hq)
  obtain ⟨p, hp, he⟩ := function_element_polynomial_degree_le_two f h F hF
  let Q : RealPoly := (2 : ℝ) • (p + S)
  have hQ : Q.totalDegree ≤ 2 := by
    exact (totalDegree_smul_le _ _).trans ((totalDegree_add _ _).trans (max_le hp hS))
  have hQpoly : (coordinateEuler Finset.univ + (0 : ℝ) • (1 : Operator))
      ((coordinateEuler Finset.univ + (2 : ℝ) • (1 : Operator)) (eta f h)) =
      polynomialSmooth Q := by
    simp only [Q, polynomialSmooth_smul, polynomialSmooth_add, hSpoly]
    dsimp [F] at he
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      zero_smul, add_zero] at he ⊢
    rw [he]
    module
  exact smooth_quadratic_of_fullEuler_resolvent_polynomial (eta f h) Q hQ hQpoly

end Wong.SmoothModel

#print axioms Wong.SmoothModel.constantWongRadial_eta_resolvent_member
#print axioms Wong.SmoothModel.quadratic_eta_of_constant_wong_full_radial_member
