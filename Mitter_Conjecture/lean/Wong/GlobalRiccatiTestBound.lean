import Wong.GlobalRiccatiQuadraticForm
import Mathlib.Tactic

/-! A genuine compact-test lower bound for div f + |f|². -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure

theorem smooth_compact_multiplier_integrable
    (μ : Measure State) [IsAddHaarMeasure μ]
    (u φ : Smooth) (hφ : HasCompactSupport φ.1) :
    Integrable (fun x => u.1 x * φ.1 x) μ :=
  ((smooth u).continuous.mul (smooth φ).continuous).integrable_of_hasCompactSupport
    hφ.mul_left

theorem compact_test_riccati_component_lower_bound
    (μ : Measure State) [IsAddHaarMeasure μ]
    (u φ : Smooth) (hφ : HasCompactSupport φ.1) (i : Fin 3) :
    -(∫ x, ((partialDerivative i φ).1 x)^2 ∂μ) ≤
      ∫ x, ((partialDerivative i u).1 x + (u.1 x)^2) * (φ.1 x)^2 ∂μ := by
  let t : Smooth := partialDerivative i φ
  let Φ : Smooth := smoothMul φ φ
  have hΦ : HasCompactSupport Φ.1 := hφ.mul_right
  have ht : HasCompactSupport t.1 := by
    change HasCompactSupport (fun x => fderiv ℝ φ.1 x (coordinateVector i))
    exact hφ.fderiv_apply (𝕜 := ℝ) (coordinateVector i)
  have hD : Integrable (fun x => (partialDerivative i u).1 x * (φ.1 x)^2) μ := by
    simpa only [Φ, smoothMul, pow_two] using
      smooth_compact_multiplier_integrable μ (partialDerivative i u) Φ hΦ
  have hA : Integrable (fun x => (u.1 x)^2 * (φ.1 x)^2) μ := by
    simpa only [Φ, smoothMul, pow_two] using
      smooth_compact_multiplier_integrable μ (smoothMul u u) Φ hΦ
  have hB : Integrable (fun x => (t.1 x)^2) μ := by
    simpa only [smoothMul, pow_two] using
      ((smooth (smoothMul t t)).continuous).integrable_of_hasCompactSupport ht.mul_right
  have hC : Integrable (fun x => φ.1 x * t.1 x * u.1 x) μ :=
    ((smooth (smoothMul (smoothMul φ t) u)).continuous).integrable_of_hasCompactSupport
      hφ.mul_right.mul_right
  have hcross : (∫ x, (partialDerivative i u).1 x * (φ.1 x)^2 ∂μ) =
      -(2 * ∫ x, φ.1 x * t.1 x * u.1 x ∂μ) := by
    have hb := smooth_compact_test_integration_by_parts μ u Φ hΦ i
    have hleft : (∫ x, (partialDerivative i u).1 x * (φ.1 x)^2 ∂μ) =
        ∫ x, Φ.1 x * (partialDerivative i u).1 x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [Φ, smoothMul]
      ring
    rw [hleft, hb]
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    have hd := congrArg (fun v : Smooth => v.1 x)
      (partialDerivative_smoothMul i φ φ)
    change (partialDerivative i Φ).1 x * u.1 x =
      2 * (φ.1 x * t.1 x * u.1 x)
    dsimp [Φ, smoothMul] at hd
    change (partialDerivative i (smoothMul φ φ)).1 x =
      t.1 x * φ.1 x + φ.1 x * t.1 x at hd
    rw [hd]
    ring
  have hineq : (2 * ∫ x, φ.1 x * t.1 x * u.1 x ∂μ) ≤
      (∫ x, (u.1 x)^2 * (φ.1 x)^2 ∂μ) + (∫ x, (t.1 x)^2 ∂μ) := by
    rw [← integral_const_mul, ← integral_add hA hB]
    apply integral_mono (hC.const_mul 2) (hA.add hB)
    intro x
    change 2 * (φ.1 x * t.1 x * u.1 x) ≤
      (u.1 x)^2 * (φ.1 x)^2 + (t.1 x)^2
    nlinarith [sq_nonneg (u.1 x * φ.1 x - t.1 x)]
  have hsplit : (∫ x, ((partialDerivative i u).1 x + (u.1 x)^2) * (φ.1 x)^2 ∂μ) =
      (∫ x, (partialDerivative i u).1 x * (φ.1 x)^2 ∂μ) +
        (∫ x, (u.1 x)^2 * (φ.1 x)^2 ∂μ) := by
    rw [← integral_add hD hA]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hsplit, hcross]
  change -(∫ x, (t.1 x)^2 ∂μ) ≤ _
  linarith

def globalRiccatiValue (f : Fin 3 → Smooth) (x : State) : ℝ :=
  ∑ i : Fin 3, ((partialDerivative i (f i)).1 x + (f i).1 x ^ 2)

theorem compact_test_global_riccati_lower_bound
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (φ : Smooth) (hφ : HasCompactSupport φ.1) :
    -(∫ x, ∑ i : Fin 3, ((partialDerivative i φ).1 x)^2 ∂μ) ≤
      ∫ x, globalRiccatiValue f x * (φ.1 x)^2 ∂μ := by
  classical
  have henergy (i : Fin 3) : Integrable (fun x => ((partialDerivative i φ).1 x)^2) μ := by
    have ht : HasCompactSupport (partialDerivative i φ).1 := by
      change HasCompactSupport (fun x => fderiv ℝ φ.1 x (coordinateVector i))
      exact hφ.fderiv_apply (𝕜 := ℝ) (coordinateVector i)
    simpa only [smoothMul, pow_two] using
      ((smooth (smoothMul (partialDerivative i φ) (partialDerivative i φ))).continuous).integrable_of_hasCompactSupport
        ht.mul_right
  have hΦ : HasCompactSupport (smoothMul φ φ).1 := hφ.mul_right
  have hcomponent (i : Fin 3) :
      Integrable (fun x => ((partialDerivative i (f i)).1 x + (f i).1 x ^ 2) *
        (φ.1 x)^2) μ := by
    simpa only [smoothMul, Submodule.coe_add, Pi.add_apply, pow_two] using
      smooth_compact_multiplier_integrable μ
        (partialDerivative i (f i) + smoothMul (f i) (f i)) (smoothMul φ φ) hΦ
  calc
    _ = ∑ i : Fin 3, -(∫ x, ((partialDerivative i φ).1 x)^2 ∂μ) := by
      rw [integral_finsetSum Finset.univ (fun i _ => henergy i), Finset.sum_neg_distrib]
    _ ≤ ∑ i : Fin 3, ∫ x, ((partialDerivative i (f i)).1 x + (f i).1 x ^ 2) *
        (φ.1 x)^2 ∂μ :=
      Finset.sum_le_sum (fun i _ => compact_test_riccati_component_lower_bound μ (f i) φ hφ i)
    _ = ∫ x, ∑ i : Fin 3, ((partialDerivative i (f i)).1 x + (f i).1 x ^ 2) *
        (φ.1 x)^2 ∂μ :=
      (integral_finsetSum Finset.univ (fun i _ => hcomponent i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [globalRiccatiValue, Finset.sum_mul]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.compact_test_riccati_component_lower_bound
#print axioms Wong.SmoothModel.compact_test_global_riccati_lower_bound
