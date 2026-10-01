import Wong.PublishedMixedAffinityProof
import Wong.RootAnalyticBridges

/-! A hidden scalar tail in an actual constant-principal first-order member
is quadratic at most when Wong is constant. The genuine bracket with L0
provides its gradient as principal coefficients; no scalar growth hypothesis
or unadmitted hidden derivative is used. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

theorem hidden_scalar_quadratic_of_constant_wong_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD0 : D f 0 ∈ estimationAlgebra f h) (hD1 : D f 1 ∈ estimationAlgebra f h)
    (hW : WongConstant f) (c : ℝ) (u : Smooth)
    (hu0 : partialDerivative 0 u = 0) (hu1 : partialDerivative 1 u = 0)
    (hT : c • D f 2 + multiplication u ∈ estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = u := by
  obtain ⟨Ω, hΩ⟩ := hW
  have hw (i j : Fin 3) : wong f i j = Ω i j • smoothOne := by
    apply Subtype.ext
    funext x
    simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, smoothOne, mul_one]
      using hΩ i j x
  let a : Fin 3 → Smooth := fun i => c • wong f 2 i + partialDerivative i u
  let b : Smooth := c • generatorRemainder f h 2 +
    (1 / 2 : ℝ) • ∑ i, partialDerivative i (partialDerivative i u)
  have hK : firstOrder f a b ∈ estimationAlgebra f h := by
    have hL : L0 f h ∈ estimationAlgebra f h :=
      LieSubalgebra.subset_lieSpan (Or.inl rfl)
    have hm := (estimationAlgebra f h).lie_mem hL hT
    have heq : ⁅L0 f h, c • D f 2 + multiplication u⁆ = firstOrder f a b := by
      simp only [lie_add, lie_smul, lie_L0_D, lie_L0_multiplication,
        a, b, firstOrder, multiplication_add, multiplication_smul, multiplication_sum,
        Finset.smul_sum, smul_add, add_mul, smul_mul_assoc, Finset.sum_add_distrib]
      module
    rwa [heq] at hm
  obtain ⟨N, hN⟩ := firstOrder_coefficients_uniform_polynomial_degree f h
  obtain ⟨p2, _hp2, he2⟩ := hN a b hK 2
  have hp2smooth : polynomialSmooth p2 = partialDerivative 2 u := by
    apply Subtype.ext
    funext x
    simpa only [polynomialSmooth_apply, a, wong_self, smul_zero, zero_add] using he2 x
  let P : Fin 3 → RealPoly := ![C (c * Ω 2 0), C (c * Ω 2 1), p2]
  have hP (i : Fin 3) : polynomialSmooth (P i) = a i := by
    fin_cases i
    · simp [P, a, hw, hu0, smul_smul, mul_comm]
    · simp [P, a, hw, hu1, smul_smul, mul_comm]
    · simpa [P, a] using hp2smooth
  have hKP : firstOrder f (fun i => polynomialSmooth (P i)) b ∈ estimationAlgebra f h := by
    simpa only [hP] using hK
  have hdegree : p2.totalDegree ≤ 1 := by
    have hd2 := actual_firstOrder_polynomial_hidden_degree_le_one f h hD0 hD1 P b hKP
        (by
          intro i hi
          have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp_all
          rcases hi01 with rfl | rfl
          · change (C (c * Ω 2 0) : RealPoly).totalDegree ≤ 1
            simp only [totalDegree_C]
            omega
          · change (C (c * Ω 2 1) : RealPoly).totalDegree ≤ 1
            simp only [totalDegree_C]
            omega)
        (by simp [P, partialDerivative_polynomialSmooth])
        (by simp [P, partialDerivative_polynomialSmooth])
    exact hd2
  have hda (i : Fin 3) (hi : i = 0 ∨ i = 1) :
      partialDerivative i (polynomialSmooth p2) = 0 := by
    rw [hp2smooth, partialDerivative_commute_apply]
    rcases hi with rfl | rfl
    · rw [hu0, map_zero]
    · rw [hu1, map_zero]
  obtain ⟨e, v, hv⟩ := polynomialSmooth_exists_affine_of_degree_le_one p2 hdegree
  have hv0 : v 0 = 0 := by
    have hh := hda 0 (Or.inl rfl)
    rw [hv, map_add, partialDerivative_const, partialDerivative_linearFunction, zero_add] at hh
    have hh' := congrArg (fun z : Smooth => z.1 (0 : State)) hh
    simpa [smoothOne] using hh'
  have hv1 : v 1 = 0 := by
    have hh := hda 1 (Or.inr rfl)
    rw [hv, map_add, partialDerivative_const, partialDerivative_linearFunction, zero_add] at hh
    have hh' := congrArg (fun z : Smooth => z.1 (0 : State)) hh
    simpa [smoothOne] using hh'
  let p : RealPoly := C (u.1 0) + C e * X 2 + C (v 2 / 2) * X 2 ^ 2
  have hpdegree : p.totalDegree ≤ 2 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      apply max_le
      · simp
      · exact (totalDegree_mul _ _).trans (by simp)
    · exact (totalDegree_mul _ _).trans (by simp)
  have hgradient : ∀ i : Fin 3, partialDerivative i (u - polynomialSmooth p) = 0 := by
    intro i
    rw [map_sub]
    fin_cases i
    · simp [p, partialDerivative_polynomialSmooth, hu0, Pi.single_apply]
    · simp [p, partialDerivative_polynomialSmooth, hu1, Pi.single_apply]
    · change partialDerivative 2 u - partialDerivative 2 (polynomialSmooth p) = 0
      rw [← hp2smooth, hv, partialDerivative_polynomialSmooth]
      apply Subtype.ext
      funext x
      simp [p, polynomialSmooth, linearFunction, Fin.sum_univ_three, hv0, hv1,
        Pi.single_apply, pow_two, smoothOne]
      ring
  obtain ⟨d, hd⟩ := (smooth_constant_iff_partials_zero _).mpr hgradient
  have hd0 : d = 0 := by
    have hh := hd (0 : State)
    simpa [p, polynomialSmooth] using hh.symm
  have heq : u - polynomialSmooth p = 0 := by
    apply Subtype.ext
    funext x
    simpa only [hd0, Submodule.coe_zero, Pi.zero_apply] using hd x
  exact ⟨p, hpdegree, (sub_eq_zero.mp heq).symm⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.hidden_scalar_quadratic_of_constant_wong_member
