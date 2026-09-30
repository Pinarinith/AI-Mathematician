import Wong.ParametricSmoothIntegral
import Wong.FunctionElements
import Wong.Gauge
import Wong.EulerFiniteModule

/-!
# Genuine smooth hidden primitives and Hadamard gauges

Fixed-interval integration gives global C-infinity parameter dependence.
The fundamental theorem of calculus proves the specified hidden partial
derivative, including on the hyperplane x₂=0. The resulting Hadamard gauge
normalizes the actual Euler Lie element rather than a formal symbol.
-/

noncomputable section
namespace Wong.SmoothModel
open MeasureTheory Set
open scoped ContDiff

def hiddenHomotopy (z : State × ℝ) : State :=
  Function.update z.1 2 (z.2 * z.1 2)

theorem contDiff_hiddenHomotopy : ContDiff ℝ ∞ hiddenHomotopy := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 2
  · subst i
    simpa [hiddenHomotopy] using contDiff_snd.mul ((contDiff_apply ℝ ℝ 2).comp contDiff_fst)
  · simpa [hiddenHomotopy, Function.update_of_ne hi, Function.comp_def] using
      (contDiff_apply ℝ ℝ i).comp contDiff_fst

def hiddenIntegralCoefficient (a : Smooth) : Smooth :=
  ⟨Wong.SmoothIntegration.compactIntegral (fun z => a.1 (hiddenHomotopy z)),
    Wong.SmoothIntegration.contDiff_infty_compactIntegral _
      ((smooth a).comp contDiff_hiddenHomotopy)⟩

def hiddenPrimitive (a : Smooth) : Smooth :=
  smoothMul (linearFunction (coordinateVector 2)) (hiddenIntegralCoefficient a)

theorem hiddenPrimitive_value (a : Smooth) (x : State) :
    (hiddenPrimitive a).1 x = ∫ t in (0 : ℝ)..x 2, coordinateSlice a x 2 t := by
  rw [hiddenPrimitive, smoothMul_apply]
  have hx : (linearFunction (coordinateVector 2)).1 x = x 2 := by
    simp [linearFunction, coordinateVector, Pi.single_apply]
  rw [hx]
  change x 2 * Wong.SmoothIntegration.compactIntegral
    (fun z => a.1 (hiddenHomotopy z)) x = _
  rw [Wong.SmoothIntegration.compactIntegral, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [hiddenHomotopy, coordinateSlice, smul_eq_mul, mul_zero, mul_one, zero_mul, one_mul, mul_comm] using
    intervalIntegral.smul_integral_comp_mul_left (coordinateSlice a x 2) (x 2)
      (a := 0) (b := 1)

theorem coordinateSlice_hiddenPrimitive (a : Smooth) (x : State) :
    coordinateSlice (hiddenPrimitive a) x 2 =
      fun t => ∫ s in (0 : ℝ)..t, coordinateSlice a x 2 s := by
  funext t
  rw [coordinateSlice, hiddenPrimitive_value]
  simp only [Function.update_self, coordinateSlice, Function.update_idem]

theorem partialDerivative_hiddenPrimitive (a : Smooth) :
    partialDerivative 2 (hiddenPrimitive a) = a := by
  apply Subtype.ext
  funext x
  have he := congrFun (deriv_coordinateSlice (hiddenPrimitive a) x 2) (x 2)
  rw [coordinateSlice_hiddenPrimitive,
    (coordinateSlice_smooth a x 2).continuous.deriv_integral] at he
  simpa only [coordinateSlice, Function.update_eq_self] using he.symm

def hiddenRestriction (r : Smooth) : Smooth :=
  ⟨fun x => r.1 (Function.update x 2 0),
    (smooth r).comp (by
      simpa [hiddenHomotopy, Function.comp_def] using
        contDiff_hiddenHomotopy.comp (contDiff_id.prodMk (contDiff_const :
          ContDiff ℝ ∞ (fun _ : State => (0 : ℝ)))))⟩

theorem partialDerivative_hiddenRestriction (r : Smooth) :
    partialDerivative 2 (hiddenRestriction r) = 0 := by
  apply Subtype.ext
  funext x
  have he := congrFun (deriv_coordinateSlice (hiddenRestriction r) x 2) (x 2)
  have hconst : coordinateSlice (hiddenRestriction r) x 2 =
      fun _ => r.1 (Function.update x 2 0) := by
    funext t
    simp [coordinateSlice, hiddenRestriction]
  rw [hconst, deriv_const] at he
  simpa only [coordinateSlice, Function.update_eq_self, Submodule.coe_zero,
    Pi.zero_apply] using he.symm

theorem hiddenPrimitive_partialDerivative (r : Smooth) :
    hiddenPrimitive (partialDerivative 2 r) = r - hiddenRestriction r := by
  apply Subtype.ext
  funext x
  rw [hiddenPrimitive_value]
  have hd (t : ℝ) : HasDerivAt (coordinateSlice r x 2)
      (coordinateSlice (partialDerivative 2 r) x 2 t) t := by
    rw [← deriv_coordinateSlice]
    exact ((coordinateSlice_smooth r x 2).differentiable (by simp)).differentiableAt.hasDerivAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((coordinateSlice_smooth (partialDerivative 2 r) x 2).continuous.intervalIntegrable 0 (x 2))
  simpa only [coordinateSlice, Function.update_eq_self, hiddenRestriction,
    Submodule.coe_sub, Pi.sub_apply] using he

theorem smooth_hidden_hadamard (r : Smooth) :
    ∃ b : Smooth, r - hiddenRestriction r =
      smoothMul (linearFunction (coordinateVector 2)) b := by
  exact ⟨hiddenIntegralCoefficient (partialDerivative 2 r),
    (hiddenPrimitive_partialDerivative r).symm⟩

theorem exists_hidden_euler_gauge (r : Smooth) :
    ∃ Λ : Smooth,
      gaugeConjugation Λ (hiddenEuler + multiplication r) =
        hiddenEuler + multiplication (hiddenRestriction r) := by
  obtain ⟨b, hb⟩ := smooth_hidden_hadamard r
  refine ⟨hiddenPrimitive b, ?_⟩
  have hr : r - smoothMul (linearFunction (coordinateVector 2)) b =
      hiddenRestriction r := by rw [← hb]; abel
  simp only [hiddenEuler, map_add, map_mul, gaugeConjugation_multiplication,
    gaugeConjugation_partialDerivative, partialDerivative_hiddenPrimitive]
  rw [← hr, multiplication_sub]
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    multiplication_apply, smoothMul_apply, Submodule.coe_add, Submodule.coe_sub,
    Pi.add_apply, Pi.sub_apply]
  ring

end Wong.SmoothModel
