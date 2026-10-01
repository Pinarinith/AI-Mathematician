import Wong.GlobalRiccatiMomentAnalysis

/-! Quadratic observations are eliminated using actual compact-test cubic
eta moments along visible directions. No global eta polynomial is assumed. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial MeasureTheory Measure

theorem observations_affine_of_visible_cubic_eta_moments {m : ℕ}
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (P : Fin m → RealPoly) (hP : ∀ j, (P j).totalDegree ≤ 2)
    (hhidden : ∀ j, pderiv 2 (P j) = 0)
    (hobs : ∀ j, polynomialSmooth (P j) = h j)
    (hetaMoment : ∀ v : State, v 2 = 0 → ∃ q : Polynomial ℝ,
      q.natDegree ≤ 3 ∧ ∀ t : ℝ, q.eval t =
        ∫ x, (eta f h).1 (x + t • v) * (riccatiFixedTest.1 x)^2 ∂μ) :
    ∀ j, (P j).totalDegree ≤ 1 := by
  let φ := riccatiFixedTest
  have hφ : HasCompactSupport φ.1 := riccatiFixedTest_compact
  let F := polynomialTestFunctional μ φ hφ
  have hmass : 0 < F 1 := by
    rw [polynomialTestFunctional_one]
    exact riccatiFixedTest_mass_positive μ
  apply quadratic_observations_affine_of_ray_coeff_nonnegative F 0 P (by simp) hP hmass
  intro v
  let w : State := ![v 0, v 1, 0]
  obtain ⟨qe, hqe, hqeMoment⟩ := hetaMoment w (by simp [w])
  let S : RealPoly := ∑ j : Fin m, (P j)^2
  have hS : S.totalDegree ≤ 4 := by
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_pow _ 2).trans (by have := hP j; omega)
  let q : Polynomial ℝ := qe - rayMoment F w S
  have hq : q.natDegree ≤ 4 := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (by omega) ((rayMoment_degree F w S).trans hS))
  have hsame (j : Fin m) : eval v (homogeneousComponent 2 (P j)) =
      eval w (homogeneousComponent 2 (P j)) := by
    have hd : pderiv 2 (homogeneousComponent 2 (P j)) = 0 := by
      have hh := Wong.PolynomialGradient.partial_homogeneousComponent (P j) 2 1
      rw [hhidden j, map_zero] at hh
      exact hh.symm
    have hs := polynomialHiddenSpecialization_eq_self_of_hidden_partial_zero 0
      (homogeneousComponent 2 (P j)) hd
    have he := eval_polynomialHiddenSpecialization 0 (homogeneousComponent 2 (P j)) v
    rw [hs] at he
    exact he
  have hmoment : ∀ t : ℝ, q.eval t =
      ∫ x, globalRiccatiValue f (x + t • w) * (φ.1 x)^2 ∂μ := by
    intro t
    have heint : Integrable (fun x : State =>
        (eta f h).1 (x + t • w) * (φ.1 x)^2) μ := by
      simpa only [translationPullback, affinePullback_apply, ContinuousLinearEquiv.refl_apply,
        smoothMul_apply, pow_two] using
        smooth_compact_multiplier_integrable μ
          (translationPullback (t • w) (eta f h)) (smoothMul φ φ) hφ.mul_right
    have hsint : Integrable (fun x : State =>
        eval (x + t • w) S * (φ.1 x)^2) μ := by
      simpa only [rayLift_base_eval] using polynomial_test_product_integrable μ φ hφ
        ((rayLift w S).eval (MvPolynomial.C t))
    simp only [q, Polynomial.eval_sub]
    rw [hqeMoment, rayMoment_polynomialTestFunctional_eval, ← integral_sub heint hsint]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [globalRiccatiValue_eq_eta_sub_observations]
    simp only [S, _root_.map_sum, map_pow]
    have he : (∑ j : Fin m, (h j).1 (x + t • w)^2) =
        ∑ j : Fin m, eval (x + t • w) (P j)^2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hobs j, polynomialSmooth_apply]
    rw [he]
    ring
  have hn := riccati_ray_moment_nonnegative_top μ f φ hφ w q 4 (by decide) hq hmoment
  have hecoeff : qe.coeff 4 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hqe.trans_lt (by omega))
  have hcoeff : q.coeff 4 = (quadraticObservationMoment F v 0 P).coeff 4 := by
    have he : quadraticObservationMoment F w 0 P = -rayMoment F w S := by
      simp only [quadraticObservationMoment, rayMoment_sum, S]
      have hz : rayMoment F w 0 = 0 := by
        ext n
        simp [rayMoment, polynomialMoment_coeff]
      rw [hz, zero_sub]
    simp only [q, Polynomial.coeff_sub, hecoeff, zero_sub]
    rw [← Polynomial.coeff_neg, ← he,
      quadraticObservationMoment_coeff_four F w 0 P (by simp) hP,
      quadraticObservationMoment_coeff_four F v 0 P (by simp) hP]
    simp only [hsame]
  rwa [hcoeff] at hn

end Wong.SmoothModel

#print axioms Wong.SmoothModel.observations_affine_of_visible_cubic_eta_moments
