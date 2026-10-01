import Wong.SmoothBrackets
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Compact-test integration by parts for the actual global smooth drift.
This supplies the analytic ingredient of Yau's global Riccati obstruction;
no obstruction, observation-affinity, or finite-dimensionality axiom is used.
-/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure

theorem smooth_compact_test_integration_by_parts
    (μ : Measure State) [IsAddHaarMeasure μ]
    (u φ : Smooth) (hφ : HasCompactSupport φ.1) (i : Fin 3) :
    (∫ x, φ.1 x * (partialDerivative i u).1 x ∂μ) =
      -(∫ x, (partialDerivative i φ).1 x * u.1 x ∂μ) := by
  have hφ' : HasCompactSupport (partialDerivative i φ).1 := by
    change HasCompactSupport (fun x => fderiv ℝ φ.1 x (coordinateVector i))
    exact hφ.fderiv_apply (𝕜 := ℝ) (coordinateVector i)
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (𝕜 := ℝ)
    (f := φ.1) (g := u.1) (v := coordinateVector i) (μ := μ)
  · exact ((smooth (partialDerivative i φ)).continuous.mul
      (smooth u).continuous).integrable_of_hasCompactSupport hφ'.mul_right
  · exact ((smooth φ).continuous.mul
      (smooth (partialDerivative i u)).continuous).integrable_of_hasCompactSupport hφ.mul_right
  · exact ((smooth φ).continuous.mul
      (smooth u).continuous).integrable_of_hasCompactSupport hφ.mul_right
  · intro x _
    exact ((smooth φ).differentiable (by simp)).differentiableAt
  · intro x _
    exact ((smooth u).differentiable (by simp)).differentiableAt

end Wong.SmoothModel

#print axioms Wong.SmoothModel.smooth_compact_test_integration_by_parts
