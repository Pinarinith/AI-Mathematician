import Wong.C1Constancy
import Wong.SmoothCoordinateEuler
import Wong.SmoothPolynomialRegularity

/-! Genuine visible radial words for the C1 sector retain arbitrary hidden
eta profiles and constant mixed Wong entries. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Wong.SmoothModel
open MvPolynomial

def c1RadialZ (f : Fin 3 → Smooth) : Operator :=
  multiplication (linearFunction (coordinateVector 0)) * D f 0 +
    multiplication (linearFunction (coordinateVector 1)) * D f 1

def c1RadialB (f : Fin 3 → Smooth) (i : Fin 3) : Smooth :=
  -(smoothMul (linearFunction (coordinateVector 0)) (wong f i 0) +
    smoothMul (linearFunction (coordinateVector 1)) (wong f i 1))

theorem c1_coordinateEuler_apply (u : Smooth) :
    coordinateEuler {0, 1} u =
      smoothMul (linearFunction (coordinateVector 0)) (partialDerivative 0 u) +
        smoothMul (linearFunction (coordinateVector 1)) (partialDerivative 1 u) := by
  simp [coordinateEuler, Fin.sum_univ_three, multiplication_apply,
    Module.End.mul_apply]

theorem c1RadialZ_lie_multiplier (f : Fin 3 → Smooth) (u : Smooth) :
    ⁅c1RadialZ f, multiplication u⁆ = multiplication (coordinateEuler {0,1} u) := by
  simp only [c1RadialZ, add_lie, lie_covariant_monomial_multiplier,
    c1_coordinateEuler_apply, multiplication_add]

theorem c1RadialZ_lie_D (f : Fin 3 → Smooth) (i : Fin 3) :
    ⁅c1RadialZ f, D f i⁆ = -(if i = 2 then 0 else D f i) -
      multiplication (c1RadialB f i) := by
  have hMD (j : Fin 3) :
      ⁅multiplication (linearFunction (coordinateVector j)), D f i⁆ =
      -(coordinateVector j i) • (1 : Operator) := by
    rw [← lie_skew, lie_D_multiplication, partialDerivative_linearFunction,
      multiplication_smul, multiplication_smoothOne, neg_smul]
  simp only [c1RadialZ, add_lie, operator_lie_mul_left, lie_D_D, hMD,
    multiplication_mul, c1RadialB, multiplication_neg_smooth, multiplication_add]
  fin_cases i <;>
    simp [coordinateVector, Pi.single_apply, smul_mul_assoc, one_mul]
  all_goals try simp only [smul_mul_assoc, one_mul, mul_smul_comm, neg_smul, one_smul]
  all_goals abel_nf
  all_goals
    ext u x <;> simp [Module.End.mul_apply]

theorem c1RadialZ_mem_of_radial_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
      estimationAlgebra f h) : c1RadialZ f ∈ estimationAlgebra f h := by
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have he : ⁅L0 f h, multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2))⁆ =
      (2 : ℝ) • c1RadialZ f + (2 : ℝ) • (1 : Operator) := by
    rw [polynomialSmooth_add, multiplication_add, lie_add,
      lie_L0_polynomial_coordinate_square, lie_L0_polynomial_coordinate_square]
    simp only [c1RadialZ, polynomialSmooth_coordinate]
    module
  have hm := (estimationAlgebra f h).sub_mem ((estimationAlgebra f h).lie_mem hL hq)
    ((estimationAlgebra f h).smul_mem (2 : ℝ)
      (one_mem_estimationAlgebra_of_rank_two f h hrank))
  rw [he, add_sub_cancel_right] at hm
  have hs := (estimationAlgebra f h).smul_mem (1 / 2 : ℝ) hm
  simpa only [smul_smul, show (1 / 2 : ℝ)*2=1 by norm_num, one_smul] using hs

theorem c1_eta_visibleEuler_partial_member_of_constant_wong {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f)
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
      estimationAlgebra f h)
    (i : Fin 3) (hi : i ≠ 2) :
    multiplication (coordinateEuler {0,1} (partialDerivative i (eta f h))) ∈
      estimationAlgebra f h := by
  obtain ⟨Ω, hΩ⟩ := hW
  have hw (a b : Fin 3) : wong f a b = Ω a b • smoothOne := by
    apply Subtype.ext
    funext x
    change (wong f a b).1 x = Ω a b * 1
    rw [hΩ, mul_one]
  have hd : ∀ a b c, partialDerivative c (wong f a b) = 0 :=
    (wongConstant_iff_partials_zero f).mp ⟨Ω,hΩ⟩
  have hB (j : Fin 3) : multiplication (c1RadialB f j) ∈ estimationAlgebra f h := by
    have he : c1RadialB f j = -(Ω j 0 • linearFunction (coordinateVector 0) +
        Ω j 1 • linearFunction (coordinateVector 1)) := by
      apply Subtype.ext
      funext x
      simp [c1RadialB, smoothMul_apply, hΩ, mul_comm]
    rw [he, multiplication_neg_smooth, multiplication_add, multiplication_smul,
      multiplication_smul]
    exact (estimationAlgebra f h).neg_mem ((estimationAlgebra f h).add_mem
      ((estimationAlgebra f h).smul_mem _ hx0) ((estimationAlgebra f h).smul_mem _ hx1))
  have hD0 := D_mem_of_coordinate_mem f h 0 hx0
  have hD1 := D_mem_of_coordinate_mem f h 1 hx1
  have hDi : D f i ∈ estimationAlgebra f h := by fin_cases i <;> simp_all
  have hZ := c1RadialZ_mem_of_radial_member f h hrank hq
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hU := (estimationAlgebra f h).lie_mem hL hDi
  have hfirst := (estimationAlgebra f h).add_mem
    ((estimationAlgebra f h).smul_mem (Ω i 0) hD0)
    ((estimationAlgebra f h).smul_mem (Ω i 1) hD1)
  have hlinear : (∑ j : Fin 3, Ω i j • multiplication (c1RadialB f j)) ∈
      estimationAlgebra f h := by
    apply (estimationAlgebra f h).sum_mem
    intro j _
    exact (estimationAlgebra f h).smul_mem _ (hB j)
  have hm := (estimationAlgebra f h).add_mem
    ((estimationAlgebra f h).add_mem ((estimationAlgebra f h).lie_mem hZ hU) hfirst) hlinear
  have he : ⁅c1RadialZ f, ⁅L0 f h, D f i⁆⁆ +
      (Ω i 0 • D f 0 + Ω i 1 • D f 1) +
      (∑ j : Fin 3, Ω i j • multiplication (c1RadialB f j)) =
      (1 / 2 : ℝ) • multiplication (coordinateEuler {0,1} (partialDerivative i (eta f h))) := by
    have hr : generatorRemainder f h i = (1/2 : ℝ) • partialDerivative i (eta f h) := by
      simp only [generatorRemainder, hd, Finset.sum_const_zero, zero_add]
    rw [lie_L0_D, hr]
    simp only [multiplication_smul, hw, multiplication_smoothOne, smul_mul_assoc, one_mul,
      lie_add, lie_sum, lie_smul, c1RadialZ_lie_multiplier, c1RadialZ_lie_D,
      smul_sub, smul_neg, Fin.sum_univ_three]
    simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      if_false, if_true, neg_zero, smul_zero, zero_sub]
    module
  rw [he] at hm
  have hs := (estimationAlgebra f h).smul_mem (2 : ℝ) hm
  simpa only [smul_smul, show (2 : ℝ)*(1/2)=1 by norm_num, one_smul] using hs


theorem c1_eta_visible_fourth_and_hidden_hessian_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f)
    (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
      estimationAlgebra f h) :
    (∀ i j k l : Fin 3, i ≠ 2 → j ≠ 2 → k ≠ 2 → l ≠ 2 →
      partialDerivative j (partialDerivative k (partialDerivative l
        (partialDerivative i (eta f h)))) = 0) ∧
    (∀ i j : Fin 3, i ≠ 2 → j ≠ 2 →
      partialDerivative 2 (partialDerivative j (partialDerivative i (eta f h))) = 0) := by
  have hmember (i : Fin 3) (hi : i ≠ 2) : i ∈ ({0,1} : Finset (Fin 3)) := by
    fin_cases i <;> simp_all
  have hF (i : Fin 3) (hi : i ≠ 2) : multiplication
      ((coordinateEuler {0,1} + (0 : ℝ) • (1 : Operator))
        (partialDerivative i (eta f h))) ∈ estimationAlgebra f h := by
    simpa only [zero_smul, add_zero] using
      c1_eta_visibleEuler_partial_member_of_constant_wong f h hrank hx0 hx1 hW hq i hi
  constructor
  · intro i j k l hi hj hk hl
    let F : Smooth := (coordinateEuler {0,1} + (0 : ℝ) • (1 : Operator))
      (partialDerivative i (eta f h))
    obtain ⟨p, hp, he⟩ := function_element_polynomial_degree_le_two f h F (hF i hi)
    have hh := congrArg (fun u : Smooth =>
      partialDerivative j (partialDerivative k (partialDerivative l u))) he
    rw [smooth_polynomial_third_partials_zero p hp j k l] at hh
    have hz := hh.symm
    simp only [F, partialDerivative_coordinateEuler_shift, hmember j hj,
      hmember k hk, hmember l hl, if_true] at hz
    norm_num only at hz
    exact positive_coordinateEuler_shift_kernel {0,1} 3 (by norm_num) _ hz
  · intro i j hi hj
    have hh := congrArg (partialDerivative j) (hHF _ (hF i hi))
    simp only [partialDerivative_coordinateEuler_shift,
      show (2 : Fin 3) ∉ ({0,1} : Finset (Fin 3)) by decide, if_false,
      hmember j hj, if_true, map_zero] at hh
    norm_num only at hh
    rw [partialDerivative_commute_apply 2 j (partialDerivative i (eta f h))]
    exact positive_coordinateEuler_shift_kernel {0,1} 1 (by norm_num) _ hh

theorem c1_eta_visible_third_partials_constant {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f)
    (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
      estimationAlgebra f h)
    (i j k : Fin 3) (hi : i ≠ 2) (hj : j ≠ 2) (hk : k ≠ 2) :
    ∃ d : ℝ, partialDerivative i (partialDerivative j (partialDerivative k (eta f h))) =
      d • smoothOne := by
  obtain ⟨hfour, hhidden⟩ :=
    c1_eta_visible_fourth_and_hidden_hessian_zero f h hrank hx0 hx1 hW hHF hq
  let u := partialDerivative i (partialDerivative j (partialDerivative k (eta f h)))
  refine ⟨u.1 0, smooth_eq_constant_of_partials_zero u ?_⟩
  intro a
  change partialDerivative a
    (partialDerivative i (partialDerivative j (partialDerivative k (eta f h)))) = 0
  by_cases ha : a = 2
  · subst a
    rw [partialDerivative_commute_apply 2 i
      (partialDerivative j (partialDerivative k (eta f h))), hhidden k j hk hj, map_zero]
  · exact hfour k a i j hk ha hi hj


theorem visibleDirectionalCube_apply (u : Smooth) (v : State) (hv : v 2 = 0) :
    (directionalDerivative v ^ 3) u =
      (v 0)^3 • partialDerivative 0 (partialDerivative 0 (partialDerivative 0 u)) +
      (3*(v 0)^2*(v 1)) • partialDerivative 0 (partialDerivative 0 (partialDerivative 1 u)) +
      (3*(v 0)*(v 1)^2) • partialDerivative 0 (partialDerivative 1 (partialDerivative 1 u)) +
      (v 1)^3 • partialDerivative 1 (partialDerivative 1 (partialDerivative 1 u)) := by
  have hc (a : Smooth) : partialDerivative 1 (partialDerivative 0 a) =
      partialDerivative 0 (partialDerivative 1 a) := partialDerivative_commute_apply 1 0 a
  simp only [directionalDerivative, Fin.sum_univ_three, hv, zero_smul, add_zero,
    pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hc]
  module

theorem c1_eta_visible_directional_third_constant {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f)
    (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
      estimationAlgebra f h)
    (v : State) (hv : v 2 = 0) :
    ∃ d : ℝ, (directionalDerivative v ^ 3) (eta f h) = d • smoothOne := by
  obtain ⟨a, ha⟩ := c1_eta_visible_third_partials_constant f h hrank hx0 hx1 hW hHF hq
    0 0 0 (by decide) (by decide) (by decide)
  obtain ⟨b, hb⟩ := c1_eta_visible_third_partials_constant f h hrank hx0 hx1 hW hHF hq
    0 0 1 (by decide) (by decide) (by decide)
  obtain ⟨c, hc⟩ := c1_eta_visible_third_partials_constant f h hrank hx0 hx1 hW hHF hq
    0 1 1 (by decide) (by decide) (by decide)
  obtain ⟨d, hd⟩ := c1_eta_visible_third_partials_constant f h hrank hx0 hx1 hW hHF hq
    1 1 1 (by decide) (by decide) (by decide)
  refine ⟨(v 0)^3*a+3*(v 0)^2*(v 1)*b+3*(v 0)*(v 1)^2*c+(v 1)^3*d, ?_⟩
  rw [visibleDirectionalCube_apply _ v hv, ha, hb, hc, hd]
  module

end Wong.SmoothModel

#print axioms Wong.SmoothModel.c1_eta_visibleEuler_partial_member_of_constant_wong
#print axioms Wong.SmoothModel.c1_eta_visible_third_partials_constant
#print axioms Wong.SmoothModel.c1_eta_visible_directional_third_constant
