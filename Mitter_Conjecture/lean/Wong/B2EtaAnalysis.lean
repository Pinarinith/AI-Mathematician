import Wong.PureHiddenQuadraticEta
import Wong.CubicEtaRiccatiRigidity
import Wong.ConstantWongQuadraticEtaClosure
import Wong.VisibleWongQuadraticAnalysis

/-! The genuine plane-radial eta word has an extra Euler shift by minus one.
After three hidden derivatives all three shifts are positive. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open MvPolynomial

def b2EtaZ (f : Fin 3 → Smooth) : Operator :=
  multiplication (linearFunction (coordinateVector 0)) * D f 0 +
    multiplication (linearFunction (coordinateVector 2)) * D f 2

def b2EtaK (f : Fin 3 → Smooth) (c : ℝ) : Operator :=
  c • (multiplication (linearFunction (coordinateVector 0)) * D f 1)

def b2EtaResolvent (u : Smooth) : Smooth :=
  (coordinateEuler {0,2} + (-1 : ℝ) • (1 : Operator))
    ((coordinateEuler {0,2} + (0 : ℝ) • (1 : Operator))
      ((coordinateEuler {0,2} + (2 : ℝ) • (1 : Operator)) u))

theorem b2_coordinateEuler_apply (u : Smooth) : coordinateEuler {0,2} u =
    smoothMul (linearFunction (coordinateVector 0)) (partialDerivative 0 u) +
    smoothMul (linearFunction (coordinateVector 2)) (partialDerivative 2 u) := by
  simp [coordinateEuler, Fin.sum_univ_three, multiplication_apply, Module.End.mul_apply]

theorem b2EtaZ_lie_multiplier (f : Fin 3 → Smooth) (u : Smooth) :
    ⁅b2EtaZ f, multiplication u⁆ = multiplication (coordinateEuler {0,2} u) := by
  simp only [b2EtaZ, add_lie, lie_covariant_monomial_multiplier,
    b2_coordinateEuler_apply, multiplication_add]

theorem b2EtaZ_lie_D (f : Fin 3 → Smooth) (c : ℝ)
    (hc : wong f 0 1 = c • smoothOne)
    (h02 : wong f 0 2 = 0) (h12 : wong f 1 2 = 0) (i : Fin 3) :
    ⁅b2EtaZ f, D f i⁆ = if i = 1 then
      -c • multiplication (linearFunction (coordinateVector 0)) else -D f i := by
  have h10 : wong f 1 0 = -c • smoothOne := by rw [wong_skew f 0 1, hc, neg_smul]
  have h20 : wong f 2 0 = 0 := by rw [wong_skew f 0 2, h02, neg_zero]
  have h21 : wong f 2 1 = 0 := by rw [wong_skew f 1 2, h12, neg_zero]
  have hMD (j : Fin 3) :
      ⁅multiplication (linearFunction (coordinateVector j)), D f i⁆ =
      -(coordinateVector j i) • (1 : Operator) := by
    rw [← lie_skew, lie_D_multiplication, partialDerivative_linearFunction,
      multiplication_smul, multiplication_smoothOne, neg_smul]
  simp only [b2EtaZ, add_lie, operator_lie_mul_left, lie_D_D, hMD]
  fin_cases i <;>
    simp [hc, h02, h12, h10, h20, h21, wong_self, multiplication_smul,
      multiplication_smoothOne, coordinateVector, Pi.single_apply,
      mul_smul_comm, smul_mul_assoc]
  all_goals
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, Module.End.mul_apply, Module.End.one_apply,
      map_neg, multiplication_apply, smoothMul_apply, Submodule.coe_add,
      Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_zero,
      Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul, smoothOne] <;> ring

theorem b2EtaZ_lie_K (f : Fin 3 → Smooth) (c : ℝ)
    (hc : wong f 0 1 = c • smoothOne) (h02 : wong f 0 2 = 0)
    (h12 : wong f 1 2 = 0) :
    ⁅b2EtaZ f, b2EtaK f c⁆ = b2EtaK f c -
      c^2 • multiplication (polynomialSmooth ((X 0 : RealPoly)^2)) := by
  have hx : coordinateEuler {0,2} (linearFunction (coordinateVector 0)) =
      linearFunction (coordinateVector 0) := by
    rw [b2_coordinateEuler_apply]
    simp [partialDerivative_linearFunction, coordinateVector, smoothMul_eq_mul]
  rw [b2EtaK, lie_smul, operator_lie_mul_right, b2EtaZ_lie_multiplier,
    hx, b2EtaZ_lie_D f c hc h02 h12 1]
  simp only [ite_true, mul_smul_comm, multiplication_mul, b2EtaK]
  have hs : smoothMul (linearFunction (coordinateVector 0))
      (linearFunction (coordinateVector 0)) = polynomialSmooth ((X 0 : RealPoly)^2) := by
    simp only [pow_two, polynomialSmooth_mul, polynomialSmooth_coordinate]
  rw [hs]
  module

theorem b2EtaZ_lie_selected_square (f : Fin 3 → Smooth) (c : ℝ)
    (hc : wong f 0 1 = c • smoothOne) (h02 : wong f 0 2 = 0)
    (h12 : wong f 1 2 = 0) (i : Fin 3) (hi : i = 0 ∨ i = 2) :
    ⁅b2EtaZ f, D f i * D f i⁆ = (-2 : ℝ) • (D f i * D f i) := by
  rw [operator_lie_mul_right, b2EtaZ_lie_D f c hc h02 h12 i]
  have hne : i ≠ 1 := by rcases hi with rfl | rfl <;> decide
  simp only [hne, ite_false, neg_mul, mul_neg]
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, Module.End.mul_apply, Module.End.one_apply,
    map_neg, multiplication_apply, smoothMul_apply, Submodule.coe_add,
    Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_zero,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply,
    smul_eq_mul, smoothOne]
  ring

theorem b2Eta_L0_word {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) (c : ℝ)
    (hc : wong f 0 1 = c • smoothOne) (h02 : wong f 0 2 = 0)
    (h12 : wong f 1 2 = 0) :
    ⁅L0 f h, b2EtaZ f⁆ = D f 0 * D f 0 + D f 2 * D f 2 + b2EtaK f c +
      (1/2 : ℝ) • multiplication (coordinateEuler {0,2} (eta f h)) := by
  have hcomm : D f 1 * multiplication (linearFunction (coordinateVector 0)) =
      multiplication (linearFunction (coordinateVector 0)) * D f 1 := by
    rw [D_mul_multiplication, partialDerivative_linearFunction]
    simp [coordinateVector]
  have hsq : ⁅b2EtaZ f, D f 1 * D f 1⁆ = (-2 : ℝ) • b2EtaK f c := by
    rw [operator_lie_mul_right, b2EtaZ_lie_D f c hc h02 h12 1]
    simp only [ite_true, smul_mul_assoc, mul_smul_comm, hcomm, b2EtaK]
    module
  rw [← lie_skew]
  simp only [L0, pow_two, lie_sub, lie_smul, lie_sum, Fin.sum_univ_three, lie_add,
    b2EtaZ_lie_selected_square f c hc h02 h12 0 (Or.inl rfl),
    b2EtaZ_lie_selected_square f c hc h02 h12 2 (Or.inr rfl), hsq,
    b2EtaZ_lie_multiplier]
  module

theorem b2Eta_resolvent_word {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (c : ℝ)
    (hc : wong f 0 1 = c • smoothOne) (h02 : wong f 0 2 = 0)
    (h12 : wong f 1 2 = 0) :
    let A := ⁅L0 f h, b2EtaZ f⁆
    let C := ⁅b2EtaZ f, A⁆ + (2 : ℝ) • A
    ⁅b2EtaZ f, C⁆ - C = multiplication
      ((1/2 : ℝ) • b2EtaResolvent (eta f h) -
        (4*c^2 : ℝ) • polynomialSmooth ((X 0 : RealPoly)^2)) := by
  have hx2 : coordinateEuler {0,2} (polynomialSmooth ((X 0 : RealPoly)^2)) =
      (2 : ℝ) • polynomialSmooth ((X 0 : RealPoly)^2) := by
    rw [b2_coordinateEuler_apply]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    simp [polynomialSmooth, smoothMul_apply, linearFunction, Fin.sum_univ_three,
      coordinateVector, pow_two]
    ring
  dsimp only
  have hC : ⁅b2EtaZ f, ⁅L0 f h, b2EtaZ f⁆⁆ + (2 : ℝ) • ⁅L0 f h, b2EtaZ f⁆ =
      (3 : ℝ) • b2EtaK f c - c^2 • multiplication (polynomialSmooth ((X 0 : RealPoly)^2)) +
      (1/2 : ℝ) • multiplication
        ((coordinateEuler {0,2} + (0 : ℝ) • (1 : Operator))
          ((coordinateEuler {0,2} + (2 : ℝ) • (1 : Operator)) (eta f h))) := by
    simp only [b2Eta_L0_word f h c hc h02 h12, lie_add, lie_smul,
      b2EtaZ_lie_selected_square f c hc h02 h12 0 (Or.inl rfl),
      b2EtaZ_lie_selected_square f c hc h02 h12 2 (Or.inr rfl),
      b2EtaZ_lie_K f c hc h02 h12, b2EtaZ_lie_multiplier,
      zero_smul, add_zero, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul, multiplication_add, multiplication_smul]
    module
  simp only [hC]
  simp only [lie_add, lie_sub, lie_smul, b2EtaZ_lie_K f c hc h02 h12,
    b2EtaZ_lie_multiplier, hx2, b2EtaResolvent, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
    multiplication_add, multiplication_sub, multiplication_smul, zero_smul, add_zero]
  module


theorem smooth_cubic_of_fourth_partials_zero (u : Smooth)
    (hu : ∀ i j k l : Fin 3, partialDerivative i
      (partialDerivative j (partialDerivative k (partialDerivative l u))) = 0) :
    ∃ p : RealPoly, p.totalDegree ≤ 3 ∧ polynomialSmooth p = u := by
  have hgradient (i : Fin 3) : ∃ p : RealPoly, p.totalDegree ≤ 2 ∧
      polynomialSmooth p = partialDerivative i u :=
    smooth_quadratic_of_third_partials_zero (partialDerivative i u)
      (fun j k l => hu j k l i)
  exact smooth_polynomial_of_polynomial_gradient_bounds u 2 hgradient

theorem b2Eta_hidden_third_zero_of_polynomial_word
    (u : Smooth) (c : ℝ) (p : RealPoly) (hp : p.totalDegree ≤ 2)
    (he : (1/2 : ℝ) • b2EtaResolvent u -
      (4*c^2 : ℝ) • polynomialSmooth ((X 0 : RealPoly)^2) = polynomialSmooth p) :
    partialDerivative 2 (partialDerivative 2 (partialDerivative 2 u)) = 0 := by
  have hq : partialDerivative 2 (partialDerivative 2
      (partialDerivative 2 (polynomialSmooth ((X 0 : RealPoly)^2)))) = 0 := by
    simp [partialDerivative_polynomialSmooth]
  have hh := congrArg (fun z : Smooth => partialDerivative 2
    (partialDerivative 2 (partialDerivative 2 z))) he
  rw [smooth_polynomial_third_partials_zero p hp 2 2 2] at hh
  simp only [map_sub, map_smul, hq, smul_zero, sub_zero, b2EtaResolvent,
    partialDerivative_coordinateEuler_shift,
    show (2 : Fin 3) ∈ ({0,2} : Finset (Fin 3)) by decide, ite_true] at hh
  norm_num only at hh
  have hz := (smul_eq_zero.mp hh).resolve_left (by norm_num)
  have hz2 := positive_coordinateEuler_shift_kernel {0,2} 2 (by norm_num) _ hz
  have hz3 := positive_coordinateEuler_shift_kernel {0,2} 3 (by norm_num) _ hz2
  exact positive_coordinateEuler_shift_kernel {0,2} 5 (by norm_num) _ hz3

theorem b2EtaZ_mem_of_plane_radial_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 2)^2)) ∈
      estimationAlgebra f h) : b2EtaZ f ∈ estimationAlgebra f h := by
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have he : ⁅L0 f h, multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 2)^2))⁆ =
      (2 : ℝ) • b2EtaZ f + (2 : ℝ) • (1 : Operator) := by
    rw [polynomialSmooth_add, multiplication_add, lie_add,
      lie_L0_polynomial_coordinate_square, lie_L0_polynomial_coordinate_square]
    simp only [b2EtaZ, polynomialSmooth_coordinate]
    module
  have hm := (estimationAlgebra f h).sub_mem ((estimationAlgebra f h).lie_mem hL hq)
    ((estimationAlgebra f h).smul_mem (2 : ℝ)
      (one_mem_estimationAlgebra_of_rank_two f h hrank))
  rw [he,add_sub_cancel_right] at hm
  have hs := (estimationAlgebra f h).smul_mem (1/2 : ℝ) hm
  simpa only [smul_smul, show (1/2 : ℝ)*2=1 by norm_num,one_smul] using hs

theorem cubic_eta_of_constant_wong_plane_radial_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f) (h02 : wong f 0 2 = 0) (h12 : wong f 1 2 = 0)
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 2)^2)) ∈
      estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 3 ∧ polynomialSmooth p = eta f h := by
  obtain ⟨Ω,hΩ⟩ := hW
  let c := Ω 0 1
  have hc : wong f 0 1 = c • smoothOne := by
    apply Subtype.ext
    funext x
    change (wong f 0 1).1 x=c*1
    rw [hΩ,mul_one]
  have hZ := b2EtaZ_mem_of_plane_radial_member f h hrank hq
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  let A := ⁅L0 f h,b2EtaZ f⁆
  have hA : A ∈ estimationAlgebra f h := (estimationAlgebra f h).lie_mem hL hZ
  let C := ⁅b2EtaZ f,A⁆+(2 : ℝ)•A
  have hC : C ∈ estimationAlgebra f h := (estimationAlgebra f h).add_mem
    ((estimationAlgebra f h).lie_mem hZ hA) ((estimationAlgebra f h).smul_mem _ hA)
  have hF := (estimationAlgebra f h).sub_mem ((estimationAlgebra f h).lie_mem hZ hC) hC
  have heF := b2Eta_resolvent_word f h c hc h02 h12
  dsimp only at heF
  change ⁅b2EtaZ f,⁅b2EtaZ f,⁅L0 f h,b2EtaZ f⁆⁆+(2 : ℝ)•⁅L0 f h,b2EtaZ f⁆⁆ -
    (⁅b2EtaZ f,⁅L0 f h,b2EtaZ f⁆⁆+(2 : ℝ)•⁅L0 f h,b2EtaZ f⁆) ∈ estimationAlgebra f h at hF
  rw [heF] at hF
  obtain ⟨p,hp,he⟩ := function_element_polynomial_degree_le_two f h _ hF
  have h222 := b2Eta_hidden_third_zero_of_polynomial_word (eta f h) c p hp he.symm
  have hvisible (i : Fin 3) (hi : i ≠ 2) (a b k : Fin 3) :
      partialDerivative a (partialDerivative b (partialDerivative k
        (partialDerivative i (eta f h)))) = 0 := by
    have hm := eta_visible_partial_member_of_constant_wong_mixed_zero
      f h ⟨Ω,hΩ⟩ h02 h12 (D_mem_of_coordinate_mem f h 0 hx0)
      (D_mem_of_coordinate_mem f h 1 hx1) i hi
    obtain ⟨P,hP,heP⟩ := function_element_polynomial_degree_le_two f h _ hm
    rw [← heP]
    exact smooth_polynomial_third_partials_zero P hP a b k
  apply smooth_cubic_of_fourth_partials_zero
  intro a b k l
  by_cases hl : l = 2
  · subst l
    by_cases hk : k = 2
    · subst k
      by_cases hb : b = 2
      · subst b
        rw [h222,map_zero]
      · rw [partialDerivative_commute_apply b 2 (partialDerivative 2 (eta f h)),
          partialDerivative_commute_apply b 2 (eta f h)]
        exact hvisible b hb a 2 2
    · rw [partialDerivative_commute_apply k 2 (eta f h)]
      exact hvisible k hk a b 2
  · exact hvisible l hl a b k

theorem functionElementsAffine_of_constant_wong_plane_radial_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f) (h02 : wong f 0 2 = 0) (h12 : wong f 1 2 = 0)
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 2)^2)) ∈
      estimationAlgebra f h) : FunctionElementsAffine (estimationAlgebra f h) := by
  obtain ⟨Q,hQ,he⟩ := cubic_eta_of_constant_wong_plane_radial_member
    f h hrank hx0 hx1 hW h02 h12 hq
  have hQ2 := (cubic_eta_degree_le_two_and_observations_affine f h Q hQ he).1
  exact functionElementsAffine_of_constant_wong_quadratic_eta f h hW Q hQ2 he

end Wong.SmoothModel

#print axioms Wong.SmoothModel.b2Eta_resolvent_word
#print axioms Wong.SmoothModel.functionElementsAffine_of_constant_wong_plane_radial_member
