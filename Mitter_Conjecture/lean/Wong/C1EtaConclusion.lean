import Wong.C1EtaWords
import Wong.VisibleCubicEtaObservationRigidity
import Wong.CoordinateCubicRiccati

/-! Actual C1 eta moments eliminate quadratic observations, and the same
Riccati bound then eliminates every visible cubic eta coefficient. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Wong.SmoothModel
open MvPolynomial MeasureTheory Measure

theorem directionalDerivative_squared_affine_zero
    (v : State) (p : RealPoly) (hp : p.totalDegree ≤ 1) :
    (directionalDerivative v ^ 2) (polynomialSmooth p) = 0 := by
  have hOne (i : Fin 3) : partialDerivative i smoothOne = 0 := by
    simpa only [one_smul] using partialDerivative_const i 1
  rw [polynomialSmooth_affine_of_degree_le_one p hp]
  simp only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply,
    directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    map_add, map_smul, _root_.map_sum, partialDerivative_const,
    partialDerivative_linearFunction, hOne, map_zero, smul_zero, Finset.sum_const_zero,
    zero_add]

theorem c1_observations_affine_of_constant_wong {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f)
    (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
      estimationAlgebra f h) :
    ∀ j, ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = h j := by
  have hpoly (j : Fin m) :
      ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = h j := by
    apply function_element_polynomial_degree_le_two f h (h j)
    exact LieSubalgebra.subset_lieSpan (Or.inr ⟨j,rfl⟩)
  choose P hP heP using hpoly
  have hhidden (j : Fin m) : pderiv 2 (P j) = 0 := by
    apply polynomialSmooth_injective
    rw [← partialDerivative_polynomialSmooth, heP,
      hHF (h j) (LieSubalgebra.subset_lieSpan (Or.inr ⟨j,rfl⟩)), polynomialSmooth_zero]
  have hdegree := observations_affine_of_visible_cubic_eta_moments
    (volume : Measure State) f h P hP hhidden heP (by
      intro v hv
      obtain ⟨d, hd⟩ := c1_eta_visible_directional_third_constant
        f h hrank hx0 hx1 hW hHF hq v hv
      let F := smoothTestFunctional (volume : Measure State)
        riccatiFixedTest riccatiFixedTest_compact
      refine ⟨smoothCubicRayMoment F (eta f h) v d,
        smoothCubicRayMoment_degree F (eta f h) v d, ?_⟩
      intro t
      exact smoothCubicRayMoment_actual_integral (volume : Measure State)
        riccatiFixedTest riccatiFixedTest_compact (eta f h) v d hd t)
  exact fun j => ⟨P j,hdegree j,heP j⟩

theorem c1_eta_visible_third_partials_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f)
    (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
      estimationAlgebra f h) :
    ∀ i j k : Fin 3, i ≠ 2 → j ≠ 2 → k ≠ 2 →
      partialDerivative i (partialDerivative j (partialDerivative k (eta f h))) = 0 := by
  have hobs := c1_observations_affine_of_constant_wong f h hrank hx0 hx1 hW hHF hq
  have hcube (v : State) (hv : v 2 = 0) : (directionalDerivative v^3) (eta f h) = 0 := by
    obtain ⟨d, hd⟩ := c1_eta_visible_directional_third_constant
      f h hrank hx0 hx1 hW hHF hq v hv
    have hz := eta_constant_third_directional_zero_of_observation_second_zero
      f h v d hd (by
        intro j
        obtain ⟨p,hp,he⟩ := hobs j
        rw [← he]
        exact directionalDerivative_squared_affine_zero v p hp)
    simpa only [hz,zero_smul] using hd
  have h000 : partialDerivative 0 (partialDerivative 0 (partialDerivative 0 (eta f h))) = 0 := by
    have hh := hcube ![1,0,0] (by simp)
    rw [visibleDirectionalCube_apply _ _ (by simp)] at hh
    simpa using hh
  have h111 : partialDerivative 1 (partialDerivative 1 (partialDerivative 1 (eta f h))) = 0 := by
    have hh := hcube ![0,1,0] (by simp)
    rw [visibleDirectionalCube_apply _ _ (by simp)] at hh
    simpa using hh
  have hplus := hcube ![1,1,0] (by simp)
  have hminus := hcube ![1,-1,0] (by simp)
  rw [visibleDirectionalCube_apply _ _ (by simp), h000, h111] at hplus hminus
  have hmixed : partialDerivative 0 (partialDerivative 0 (partialDerivative 1 (eta f h))) = 0 ∧
      partialDerivative 0 (partialDerivative 1 (partialDerivative 1 (eta f h))) = 0 := by
    constructor <;> apply Subtype.ext <;> funext x
    all_goals
      have hp := congrArg (fun u : Smooth => u.1 x) hplus
      have hn := congrArg (fun u : Smooth => u.1 x) hminus
      simp at hp hn ⊢
      nlinarith
  have hc (u : Smooth) : partialDerivative 1 (partialDerivative 0 u) =
      partialDerivative 0 (partialDerivative 1 u) := partialDerivative_commute_apply 1 0 u
  intro i j k hi hj hk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [hc, h000, h111, hmixed.1, hmixed.2]

theorem c1_eta_visible_hessians_constant {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f)
    (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
      estimationAlgebra f h) :
    ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 → ∃ c : ℝ,
      partialDerivative i (partialDerivative j (eta f h)) = c • smoothOne := by
  have hthird := c1_eta_visible_third_partials_zero f h hrank hx0 hx1 hW hHF hq
  have hhidden := (c1_eta_visible_fourth_and_hidden_hessian_zero
    f h hrank hx0 hx1 hW hHF hq).2
  intro i j hi hj
  let u := partialDerivative i (partialDerivative j (eta f h))
  refine ⟨u.1 0,smooth_eq_constant_of_partials_zero u ?_⟩
  intro a
  by_cases ha : a = 2
  · subst a
    exact hhidden j i hj hi
  · exact hthird a i j ha hi hj

end Wong.SmoothModel

#print axioms Wong.SmoothModel.c1_eta_visible_hessians_constant
