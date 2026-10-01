import Wong.RootAnalyticBridges
import Wong.EulerFunctionSpace

/-! Positive shifts of a coordinate Euler operator have no nonzero globally
smooth kernel, including the singular coordinate plane. The proof uses the
already proved global one-variable energy uniqueness theorem. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open scoped ContDiff

def coordinateProjection (s : Finset (Fin 3)) (x : State) : State :=
  fun i => if i ∈ s then x i else 0

def coordinateEuler (s : Finset (Fin 3)) : Operator :=
  ∑ i : Fin 3, multiplication (if i ∈ s then linearFunction (coordinateVector i) else 0) *
    partialDerivative i

theorem coordinateEuler_apply (s : Finset (Fin 3)) (u : Smooth) (x : State) :
    (coordinateEuler s u).1 x = fderiv ℝ u.1 x (coordinateProjection s x) := by
  rw [← directionalDerivative_apply]
  simp [coordinateEuler, directionalDerivative, coordinateProjection,
    multiplication_apply, smoothMul_apply, linearFunction, coordinateVector,
    Pi.single_apply, ite_mul, mul_ite, LinearMap.sum_apply, Finset.sum_apply]

theorem positive_coordinateEuler_shift_kernel
    (s : Finset (Fin 3)) (c : ℝ) (hc : 0 < c) (u : Smooth)
    (hu : (coordinateEuler s + c • (1 : Operator)) u = 0) : u = 0 := by
  apply Subtype.ext
  funext x
  let a := coordinateProjection s x
  let b := x - a
  let V : ℝ → ℝ := fun t => u.1 (b + t • a)
  have hcurve : ContDiff ℝ ∞ (fun t : ℝ => b + t • a) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hV : ContDiff ℝ ∞ V := (smooth u).comp hcurve
  have hderiv (t : ℝ) : deriv V t = fderiv ℝ u.1 (b + t • a) a := by
    have hline : HasDerivAt (fun t : ℝ => b + t • a) a t := by
      simpa only [zero_add, one_smul, Pi.add_def, id_eq] using
        (hasDerivAt_const t b).add ((hasDerivAt_id t).smul_const a)
    have hf : HasFDerivAt u.1 (fderiv ℝ u.1 (b + t • a)) (b + t • a) :=
      (((smooth u).differentiable (by simp)).differentiableAt.hasFDerivAt)
    have hd := hf.comp_hasDerivAt t hline
    simpa only [V, Function.comp_def] using hd.deriv
  have hmask (t : ℝ) : coordinateProjection s (b + t • a) = t • a := by
    funext i
    by_cases hi : i ∈ s <;> simp [coordinateProjection, a, b, hi]
  have hsys (t : ℝ) : t • deriv V t = (0 : ℝ →L[ℝ] ℝ) (V t) - c • V t := by
    have hh := congrArg (fun z : Smooth => z.1 (b + t • a)) hu
    change (coordinateEuler s u).1 (b + t • a) + c * V t = 0 at hh
    rw [coordinateEuler_apply, hmask, map_smul] at hh
    rw [hderiv]
    change t * fderiv ℝ u.1 (b + t • a) a = 0 - c * V t
    simpa only [smul_eq_mul, zero_sub] using (eq_neg_of_add_eq_zero_left hh)
  have hz := Wong.EulerSystem.shifted_euler_system_eq_zero (0 : ℝ →L[ℝ] ℝ) c
    (by simpa using hc) V (hV.differentiable (by simp)) hsys
  have hh := congrFun hz 1
  simpa [V, b] using hh

theorem partialDerivative_coordinateEuler_shift
    (s : Finset (Fin 3)) (i : Fin 3) (c : ℝ) (u : Smooth) :
    partialDerivative i ((coordinateEuler s + c • (1 : Operator)) u) =
      (coordinateEuler s + (c + if i ∈ s then 1 else 0) • (1 : Operator))
        (partialDerivative i u) := by
  have hlie : ⁅partialDerivative i, coordinateEuler s⁆ =
      (if i ∈ s then (1 : ℝ) else 0) • partialDerivative i := by
    by_cases h0 : (0 : Fin 3) ∈ s <;>
      by_cases h1 : (1 : Fin 3) ∈ s <;>
      by_cases h2 : (2 : Fin 3) ∈ s <;>
      fin_cases i <;>
      simp [coordinateEuler, Fin.sum_univ_three, h0, h1, h2,
        operator_lie_mul_right, lie_partial_multiplication,
        partialDerivative_linearFunction, coordinateVector, Pi.single_apply,
        multiplication_smul, smul_mul_assoc]
  rw [operator_lie_def] at hlie
  have hh := congrArg (fun A : Operator => A u) hlie
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] at hh
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_add, map_smul]
  rw [sub_eq_iff_eq_add.mp hh]
  module

end Wong.SmoothModel

#print axioms Wong.SmoothModel.positive_coordinateEuler_shift_kernel
#print axioms Wong.SmoothModel.partialDerivative_coordinateEuler_shift
