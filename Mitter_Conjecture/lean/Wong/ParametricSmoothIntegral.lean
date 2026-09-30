import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth integration over a fixed compact interval

The parameter derivative is integrated using the proved dominated
differentiation theorem. Compactness supplies a local uniform bound, and
induction gives all finite derivative orders, hence C-infinity smoothness.
-/

noncomputable section
namespace Wong.SmoothIntegration
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def compactIntegral (F : H × ℝ → E) (x : H) : E :=
  ∫ t in Icc (0 : ℝ) 1, F (x, t)

def parameterDerivative (F : H × ℝ → E) (z : H × ℝ) : H →L[ℝ] E :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H ℝ)

omit [FiniteDimensional ℝ H] [CompleteSpace E] in
theorem contDiff_parameterDerivative {n : ℕ}
    (F : H × ℝ → E) (hF : ContDiff ℝ ((n : ℕ∞ω) + 1) F) :
    ContDiff ℝ n (parameterDerivative F) := by
  exact (hF.fderiv_right (le_refl _)).clm_comp contDiff_const

omit [CompleteSpace E] in
theorem hasFDerivAt_compactIntegral (F : H × ℝ → E)
    (hF : ContDiff ℝ 1 F) (x₀ : H) :
    HasFDerivAt (compactIntegral F) (compactIntegral (parameterDerivative F) x₀) x₀ := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hd : Differentiable ℝ F := hF.differentiable (by decide)
  have hdc : Continuous (parameterDerivative F) :=
    (contDiff_parameterDerivative F hF).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod (isCompact_Icc :
    IsCompact (Icc (0 : ℝ) 1))).exists_bound_of_continuousOn hdc.continuousOn
  have hdiff (x : H) (t : ℝ) :
      HasFDerivAt (fun y : H => F (y, t)) (parameterDerivative F (x, t)) x := by
    have hg : HasFDerivAt (fun y : H => (y, t))
        (ContinuousLinearMap.inl ℝ H ℝ) x := by
      convert (ContinuousLinearMap.inl ℝ H ℝ).hasFDerivAt.add_const (0, t) using 1
      funext y
      ext <;> simp
    exact (hd (x, t)).hasFDerivAt.comp x hg
  have hμ : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have hi (x : H) : Integrable (fun t => F (x, t)) μ :=
    (hF.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hmeas (x : H) : AEStronglyMeasurable (fun t => F (x, t)) μ :=
    (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (fun t => parameterDerivative F (x₀, t)) μ :=
    (hdc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ x ∈ closedBall x₀ 1,
      ‖parameterDerivative F (x, t)‖ ≤ C := by
    filter_upwards [hμ] with t ht
    intro x hx
    exact hC (x, t) ⟨hx, ht⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (closedBall_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas) (hi x₀) hdmeas hbound (integrable_const C)
    (Eventually.of_forall (fun t x _ => hdiff x t))

theorem contDiff_compactIntegral (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      ∀ F : H × ℝ → E, ContDiff ℝ n F → ContDiff ℝ n (compactIntegral F) := by
  induction n with
  | zero =>
    intro E _ _ _ F hF
    exact contDiff_zero.mpr
      (continuous_parametric_integral_of_continuous
        (f := fun x t => F (x, t)) hF.continuous isCompact_Icc)
  | succ n ih =>
    intro E _ _ _ F hF
    have hc : ContDiff ℝ ((n : ℕ∞ω) + 1) F := by simpa using hF
    have h1 : ContDiff ℝ 1 F := hc.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    have hd (x : H) := hasFDerivAt_compactIntegral F h1 x
    have he : fderiv ℝ (compactIntegral F) = compactIntegral (parameterDerivative F) :=
      funext (fun x => (hd x).fderiv)
    have hg := ih (parameterDerivative F) (contDiff_parameterDerivative F hc)
    change ContDiff ℝ ((n : ℕ∞ω) + 1) (compactIntegral F)
    apply contDiff_succ_iff_fderiv.mpr
    refine ⟨fun x => (hd x).differentiableAt, ?_, ?_⟩
    · intro hn
      simp at hn
    · rw [he]
      exact hg

theorem contDiff_infty_compactIntegral (F : H × ℝ → E)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (compactIntegral F) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_compactIntegral n F (contDiff_infty.mp hF n)

end Wong.SmoothIntegration
