import Wong.GlobalRiccatiMomentAnalysis

/-! Actual global Riccati bounds also eliminate cubic eta tails. This is
used only after a genuine operator word has proved eta polynomiality. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial MeasureTheory

theorem cubicEtaObservationMoment_degree {m : ℕ} (F : RealPoly →ₗ[ℝ] ℝ)
    (v : State) (Q : RealPoly) (P : Fin m → RealPoly)
    (hQ : Q.totalDegree ≤ 3) (hP : ∀ j, (P j).totalDegree ≤ 2) :
    (quadraticObservationMoment F v Q P).natDegree ≤ 4 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (rayMoment_degree F v Q).trans (by omega)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (rayMoment_degree F v ((P j)^2)).trans
      ((totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (hP j)))

theorem cubicEtaObservationMoment_coeff_four_eq_zero_eta {m : ℕ}
    (F : RealPoly →ₗ[ℝ] ℝ) (v : State) (Q : RealPoly) (P : Fin m → RealPoly)
    (hQ : Q.totalDegree ≤ 3) :
    (quadraticObservationMoment F v Q P).coeff 4 =
      (quadraticObservationMoment F v 0 P).coeff 4 := by
  have hzero : (rayMoment F v Q).coeff 4 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((rayMoment_degree F v Q).trans_lt (by omega))
  simp only [quadraticObservationMoment, Polynomial.coeff_sub, hzero]
  have hz : rayMoment F v 0 = 0 := by
    ext n
    simp [rayMoment, polynomialMoment_coeff]
  rw [hz, Polynomial.coeff_zero]

theorem observations_affine_of_cubic_eta_polynomials {m : ℕ}
    (μ : Measure State) [Measure.IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (Q : RealPoly) (P : Fin m → RealPoly)
    (hQ : Q.totalDegree ≤ 3) (hP : ∀ j, (P j).totalDegree ≤ 2)
    (heta : polynomialSmooth Q = eta f h)
    (hobs : ∀ j, polynomialSmooth (P j) = h j) :
    ∀ j, (P j).totalDegree ≤ 1 := by
  let φ := riccatiFixedTest
  have hφ : HasCompactSupport φ.1 := riccatiFixedTest_compact
  let F := polynomialTestFunctional μ φ hφ
  have hmass : 0 < F 1 := by
    rw [polynomialTestFunctional_one]
    exact riccatiFixedTest_mass_positive μ
  apply quadratic_observations_affine_of_ray_coeff_nonnegative F 0 P (by simp) hP hmass
  intro v
  rw [← cubicEtaObservationMoment_coeff_four_eq_zero_eta F v Q P hQ]
  let q := quadraticObservationMoment F v Q P
  have hpotential (x : State) :
      eval x (Q - ∑ j : Fin m, (P j)^2) = globalRiccatiValue f x := by
    rw [globalRiccatiValue_eq_eta_sub_observations]
    simp only [eval_sub, _root_.map_sum, map_pow]
    rw [← heta, polynomialSmooth_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← hobs j, polynomialSmooth_apply]
  have hmoment : ∀ t : ℝ, q.eval t =
      ∫ x, globalRiccatiValue f (x + t • v) * (φ.1 x)^2 ∂μ := by
    intro t
    have heq : q = rayMoment F v (Q - ∑ j : Fin m, (P j)^2) := by
      rw [rayMoment_sub, rayMoment_sum]
      rfl
    rw [heq, rayMoment_polynomialTestFunctional_eval]
    simp only [hpotential]
  exact riccati_ray_moment_nonnegative_top μ f φ hφ v q 4 (by decide)
    (cubicEtaObservationMoment_degree F v Q P hQ hP) hmoment

theorem homogeneous_cubic_eval_neg (p : RealPoly) (hp : p.IsHomogeneous 3) (v : State) :
    eval (-v) p = -eval v p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [_root_.map_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro α hα
  have hd : ∑ i ∈ α.support, α i = 3 := (hp.degree_eq_sum_deg_support hα).symm
  have hprod : α.prod (fun i n => (-v i)^n) = -α.prod (fun i n => (v i)^n) := by
    simp only [Finsupp.prod]
    calc
      (∏ i ∈ α.support, (-v i)^(α i)) =
          ∏ i ∈ α.support, ((-1 : ℝ)^(α i)) * (v i)^(α i) := by
            apply Finset.prod_congr rfl
            intro i _
            exact neg_pow (v i) (α i)
      _ = (∏ i ∈ α.support, (-1 : ℝ)^(α i)) *
          (∏ i ∈ α.support, (v i)^(α i)) := Finset.prod_mul_distrib
      _ = (-1 : ℝ)^3 * (∏ i ∈ α.support, (v i)^(α i)) := by
        rw [Finset.prod_pow_eq_pow_sum, hd]
      _ = -(∏ i ∈ α.support, (v i)^(α i)) := by norm_num
  simp only [eval_monomial, Pi.neg_apply]
  rw [hprod]
  ring

theorem riccati_cubic_polynomial_degree_le_two
    (μ : Measure State) [Measure.IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (p : RealPoly) (hp : p.totalDegree ≤ 3)
    (he : ∀ x : State, globalRiccatiValue f x = eval x p) :
    p.totalDegree ≤ 2 := by
  have htop : homogeneousComponent 3 p = 0 := by
    apply MvPolynomial.funext
    intro v
    have hpos := riccati_polynomial_top_nonnegative μ f p he v 3 (by decide) hp
    have hneg := riccati_polynomial_top_nonnegative μ f p he (-v) 3 (by decide) hp
    rw [homogeneous_cubic_eval_neg _ (homogeneousComponent_isHomogeneous _ _) v] at hneg
    simp only [map_zero]
    linarith
  have hd := polynomial_sub_top_component_degree_le p 3 (by decide) hp
  simpa only [htop, sub_zero, Nat.reduceSub] using hd

theorem cubic_eta_degree_le_two_and_observations_affine {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (Q : RealPoly) (hQ : Q.totalDegree ≤ 3) (heta : polynomialSmooth Q = eta f h) :
    Q.totalDegree ≤ 2 ∧
      (∀ j, ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = h j) := by
  have hpoly (j : Fin m) :
      ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = h j := by
    apply function_element_polynomial_degree_le_two f h (h j)
    exact LieSubalgebra.subset_lieSpan (Or.inr ⟨j, rfl⟩)
  choose P hP heP using hpoly
  have hPaff := observations_affine_of_cubic_eta_polynomials
    (volume : Measure State) f h Q P hQ hP heta heP
  let A := Q - ∑ j : Fin m, (P j)^2
  have hA : A.totalDegree ≤ 3 := by
    apply (totalDegree_sub _ _).trans
    apply max_le hQ
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_pow _ 2).trans (by have := hPaff j; omega)
  have hpotential (x : State) : globalRiccatiValue f x = eval x A := by
    rw [globalRiccatiValue_eq_eta_sub_observations]
    simp only [A, eval_sub, _root_.map_sum, map_pow]
    rw [← heta, polynomialSmooth_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← heP j, polynomialSmooth_apply]
  have hA2 := riccati_cubic_polynomial_degree_le_two
    (volume : Measure State) f A hA hpotential
  constructor
  · have hsum : (∑ j : Fin m, (P j)^2).totalDegree ≤ 2 := by
      apply totalDegree_finsetSum_le
      intro j _
      exact (totalDegree_pow _ 2).trans (by have := hPaff j; omega)
    have heq : Q = A + ∑ j : Fin m, (P j)^2 := by simp [A]
    rw [heq]
    exact (totalDegree_add _ _).trans (max_le hA2 hsum)
  · exact fun j => ⟨P j, hPaff j, heP j⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.cubic_eta_degree_le_two_and_observations_affine
