import Wong.GlobalRiccatiMomentAnalysis

/-! A cubic moment of the genuine global Riccati potential has zero cubic
coefficient. Lower coefficients may come from arbitrary smooth profiles. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure

theorem riccati_cubic_ray_moment_coeff_zero
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (φ : Smooth) (hφ : HasCompactSupport φ.1)
    (v : State) (q : Polynomial ℝ) (hq : q.natDegree ≤ 3)
    (hmoment : ∀ t : ℝ, q.eval t =
      ∫ x, globalRiccatiValue f (x + t • v) * (φ.1 x)^2 ∂μ) :
    q.coeff 3 = 0 := by
  by_cases hz : q.coeff 3 = 0
  · exact hz
  have hd : q.natDegree = 3 := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hq hz
  have hqne : q ≠ 0 := by intro he; simp [he] at hz
  let r := q.comp (-Polynomial.X)
  have hrdeg : r.natDegree = 3 := by
    have hh := Polynomial.natDegree_comp_eq_of_mul_ne_zero
      (p := q) (q := -Polynomial.X) (by simp [hqne])
    simpa only [r, Polynomial.natDegree_neg, Polynomial.natDegree_X, mul_one, hd] using hh
  have hrmoment : ∀ t : ℝ, r.eval t =
      ∫ x, globalRiccatiValue f (x + t • (-v)) * (φ.1 x)^2 ∂μ := by
    intro t
    simp only [r, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
    rw [hmoment]
    simp only [neg_smul, smul_neg]
  have hc : r.coeff 3 = -q.coeff 3 := by
    have hcr : r.coeff 3 = r.leadingCoeff := by rw [Polynomial.leadingCoeff, hrdeg]
    have hcq : q.leadingCoeff = q.coeff 3 := by rw [Polynomial.leadingCoeff, hd]
    rw [hcr]
    change (q.comp (-Polynomial.X)).leadingCoeff = _
    rw [Polynomial.comp_neg_X_leadingCoeff_eq, hd, hcq]
    norm_num
  have hp := riccati_ray_moment_nonnegative_top μ f φ hφ v q 3 (by decide) hq hmoment
  have hn := riccati_ray_moment_nonnegative_top μ f φ hφ (-v) r 3 (by decide)
    hrdeg.le hrmoment
  rw [hc] at hn
  linarith

end Wong.SmoothModel

#print axioms Wong.SmoothModel.riccati_cubic_ray_moment_coeff_zero
