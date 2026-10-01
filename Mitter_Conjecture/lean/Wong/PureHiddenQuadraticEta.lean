import Wong.SmoothEulerResolventRegularity
import Wong.FunctionQuadraticRankConstraints

/-! The whole pure-hidden quadratic sector gives global quadratic eta
through a genuine hidden Euler function word. No eta profile is assumed. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem eta_visible_partial_member_of_constant_wong_mixed_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hW : WongConstant f) (h02 : wong f 0 2 = 0) (h12 : wong f 1 2 = 0)
    (hD0 : D f 0 ∈ estimationAlgebra f h) (hD1 : D f 1 ∈ estimationAlgebra f h)
    (i : Fin 3) (hi : i ≠ 2) :
    multiplication (partialDerivative i (eta f h)) ∈ estimationAlgebra f h := by
  obtain ⟨Ω, hΩ⟩ := hW
  have hw (a b : Fin 3) : wong f a b = Ω a b • smoothOne := by
    apply Subtype.ext
    funext x
    simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, smoothOne, mul_one]
      using hΩ a b x
  have hd : ∀ a b c, partialDerivative c (wong f a b) = 0 :=
    (wongConstant_iff_partials_zero f).mp ⟨Ω, hΩ⟩
  have hDi : D f i ∈ estimationAlgebra f h := by fin_cases i <;> simp_all
  have hi2 : wong f i 2 = 0 := by fin_cases i <;> simp_all
  have hrow : (∑ j : Fin 3, multiplication (wong f i j) * D f j) ∈
      estimationAlgebra f h := by
    apply (estimationAlgebra f h).sum_mem
    intro j _hj
    fin_cases j
    · rw [hw, multiplication_smul, multiplication_smoothOne, smul_mul_assoc, one_mul]
      exact (estimationAlgebra f h).smul_mem _ hD0
    · rw [hw, multiplication_smul, multiplication_smoothOne, smul_mul_assoc, one_mul]
      exact (estimationAlgebra f h).smul_mem _ hD1
    · change multiplication (wong f i 2) * D f 2 ∈ (estimationAlgebra f h).toSubmodule
      rw [hi2, multiplication_zero, zero_mul]
      exact (estimationAlgebra f h).zero_mem
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hm := (estimationAlgebra f h).sub_mem ((estimationAlgebra f h).lie_mem hL hDi) hrow
  simp only [lie_L0_D, add_sub_cancel_left, generatorRemainder, hd,
    Finset.sum_const_zero, zero_add, multiplication_smul] at hm
  have hs := (estimationAlgebra f h).smul_mem (2 : ℝ) hm
  simpa only [smul_smul, show (2 : ℝ)*(1/2)=1 by norm_num, one_smul] using hs

theorem quadratic_eta_of_pure_hidden_function_hessians_and_euler_word {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hW : WongConstant f) (h02 : wong f 0 2 = 0) (h12 : wong f 1 2 = 0)
    (hVis : ∀ u : Smooth, multiplication u ∈ estimationAlgebra f h →
      ∀ i j : Fin 3, i ≠ 2 → j ≠ 2 → partialDerivative i (partialDerivative j u) = 0)
    (hword : multiplication
      ((coordinateEuler {2} + (0 : ℝ) • (1 : Operator))
        ((coordinateEuler {2} + (2 : ℝ) • (1 : Operator)) (eta f h))) ∈
        estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = eta f h := by
  let F := (coordinateEuler {2} + (0 : ℝ) • (1 : Operator))
    ((coordinateEuler {2} + (2 : ℝ) • (1 : Operator)) (eta f h))
  obtain ⟨p, hp, he⟩ := function_element_polynomial_degree_le_two f h F hword
  have hEtaVis (i : Fin 3) (hi : i ≠ 2) :
      multiplication (partialDerivative i (eta f h)) ∈ estimationAlgebra f h :=
    eta_visible_partial_member_of_constant_wong_mixed_zero f h hW h02 h12
      (D_mem_of_coordinate_mem f h 0 hx0) (D_mem_of_coordinate_mem f h 1 hx1) i hi
  have hmixed (i : Fin 3) (hi : i ≠ 2) :
      partialDerivative 2 (partialDerivative i (eta f h)) = 0 := by
    have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp_all
    have hFm := function_element_hidden_visible_mixed_zero
      f h hrank hx0 hx1 F hword i (by rcases hi01 with rfl | rfl <;> assumption)
    exact euler_resolvent_mixed_partial_zero {2} (eta f h) 2 i (by simp)
      (by simp [hi]) hFm
  have hreverse (i : Fin 3) (hi : i ≠ 2) :
      partialDerivative i (partialDerivative 2 (eta f h)) = 0 := by
    rw [partialDerivative_commute_apply]
    exact hmixed i hi
  have h222 : partialDerivative 2 (partialDerivative 2 (partialDerivative 2 (eta f h))) = 0 :=
    euler_resolvent_selected_third_partial_zero {2} (eta f h) p hp he.symm
      2 2 2 (by simp) (by simp) (by simp)
  apply smooth_quadratic_of_third_partials_zero
  intro i j k
  by_cases hk : k = 2
  · subst k
    by_cases hj : j = 2
    · subst j
      by_cases hi : i = 2
      · subst i
        exact h222
      · rw [partialDerivative_commute_apply i 2 (partialDerivative 2 (eta f h)),
          hreverse i hi, map_zero]
    · rw [hreverse j hj, map_zero]
  · by_cases hj : j = 2
    · subst j
      rw [hmixed k hk, map_zero]
    · by_cases hi : i = 2
      · subst i
        rw [partialDerivative_commute_apply 2 j (partialDerivative k (eta f h)),
          hmixed k hk, map_zero]
      · exact hVis _ (hEtaVis k hk) i j hi hj

end Wong.SmoothModel

#print axioms Wong.SmoothModel.quadratic_eta_of_pure_hidden_function_hessians_and_euler_word
