import Wong.EulerFalling
import Wong.EulerHiddenPolynomial
import Wong.AdaptedGauge

/-!
# Hidden independence forced by the actual adapted function space

The argument uses the true Lie polynomial ad(J)^2 + ad(J), followed by
injectivity of positive shifts of the global smooth Euler operator. No
polynomial-coefficient or spectral-decomposition premise is needed.
-/
noncomputable section
namespace Wong.SmoothModel
open scoped ContDiff
set_option maxHeartbeats 1000000

/-- A positive Euler shift has no nonzero globally smooth kernel. The
singular point is included by the already proved energy uniqueness theorem. -/
theorem positive_hiddenEuler_shift_kernel (c : ℝ) (hc : 0 < c) (u : Smooth)
    (hu : (hiddenEuler + c • (1 : Operator)) u = 0) : u = 0 := by
  apply Subtype.ext
  funext x
  change u.1 x = 0
  let V := coordinateSlice u x 2
  have hsys (t : ℝ) : t • deriv V t = (0 : ℝ →L[ℝ] ℝ) (V t) - c • V t := by
    have ht := congrArg (fun z : Smooth => coordinateSlice z x 2 t) hu
    change coordinateSlice (hiddenEuler u) x 2 t + c * coordinateSlice u x 2 t = 0 at ht
    rw [hiddenEuler_slice] at ht
    change t * deriv (coordinateSlice u x 2) t = 0 - c * coordinateSlice u x 2 t
    linarith
  have hz := Wong.EulerSystem.shifted_euler_system_eq_zero (0 : ℝ →L[ℝ] ℝ) c
    (by simpa using hc) V ((coordinateSlice_smooth u x 2).differentiable (by simp)) hsys
  have ht := congrFun hz (x 2)
  simpa only [V, coordinateSlice, Function.update_eq_self, Pi.zero_apply] using ht

/-- The true derivative/Euler shift identity on a smooth function. -/
theorem partial_hiddenEuler_apply (u : Smooth) :
    partialDerivative 2 (hiddenEuler u) =
      hiddenEuler (partialDerivative 2 u) + partialDerivative 2 u := by
  have hh := congrArg (fun A : Operator => A u) (hidden_partial_shift 1)
  simp only [pow_one, Nat.cast_one, one_smul, Module.End.mul_apply,
    LinearMap.sub_apply, Module.End.one_apply] at hh
  rw [map_sub] at hh
  exact sub_eq_iff_eq_add.mp hh

theorem multiplier_lie_partial_euler (B : Smooth) (i : Fin 3) :
    ⁅multiplication B, partialDerivative i⁆ = -multiplication (partialDerivative i B) := by
  rw [← lie_skew, lie_partial_multiplication]

theorem visible_B_partial_hiddenEuler (B : Smooth) (hB : partialDerivative 2 B = 0)
    (i : Fin 3) : hiddenEuler (partialDerivative i B) = 0 := by
  change multiplication (linearFunction (coordinateVector 2))
    (partialDerivative 2 (partialDerivative i B)) = 0
  rw [partialDerivative_commute_apply, hB, map_zero, map_zero]

/-- The first genuine Lie bracket in the short function-space argument. -/
theorem euler_affine_firstOrder_first_bracket (B u : Smooth)
    (hB : partialDerivative 2 B = 0) (i : Fin 3) (hi : i ≠ 2) (a : ℝ) :
    ⁅hiddenEuler + multiplication B,
      partialDerivative i + a • partialDerivative 2 + multiplication u⁆ =
      -a • partialDerivative 2 + multiplication (hiddenEuler u - partialDerivative i B) := by
  simp only [add_lie, lie_add, lie_smul, hiddenEuler_lie_partial, hi, ite_false,
    ite_true, zero_smul, hiddenEuler_lie_multiplier, multiplier_lie_partial_euler,
    hB, multiplication_zero, neg_zero, lie_multiplication_multiplication,
    multiplication_sub, zero_add, add_zero]
  module

/-- A genuine Lie polynomial kills the two derivative heads and leaves the
stated multiplication operator. -/
theorem euler_affine_firstOrder_lie_polynomial (B u : Smooth)
    (hB : partialDerivative 2 B = 0) (i : Fin 3) (hi : i ≠ 2) (a : ℝ) :
    let J := hiddenEuler + multiplication B
    let P := partialDerivative i + a • partialDerivative 2 + multiplication u
    ⁅J, ⁅J, P⁆⁆ + ⁅J, P⁆ =
      multiplication (hiddenEuler (hiddenEuler u) + hiddenEuler u - partialDerivative i B) := by
  dsimp only
  rw [euler_affine_firstOrder_first_bracket B u hB i hi a]
  have hJ3 : ⁅hiddenEuler + multiplication B, partialDerivative 2⁆ = -partialDerivative 2 := by
    simp only [add_lie, hiddenEuler_lie_partial, ite_true, neg_one_smul,
      multiplier_lie_partial_euler, hB, multiplication_zero, neg_zero, add_zero]
  have hJmul (v : Smooth) : ⁅hiddenEuler + multiplication B, multiplication v⁆ =
      multiplication (hiddenEuler v) := by
    rw [add_lie, hiddenEuler_lie_multiplier, lie_multiplication_multiplication, add_zero]
  rw [lie_add, lie_smul, hJ3, hJmul, map_sub,
    visible_B_partial_hiddenEuler B hB i, sub_zero]
  simp only [multiplication_add, multiplication_sub]
  module

/-- If actual multiplication elements of E are hidden-independent, then
a first-order element with the prescribed constant derivative heads has a
hidden-independent zero-order coefficient. Finite dimensionality is not needed. -/
theorem firstOrder_hidden_independent_of_function_space
    (E : LieSubalgebra ℝ Operator)
    (hfun : ∀ v : Smooth, multiplication v ∈ E → partialDerivative 2 v = 0)
    (B u : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (i : Fin 3) (hi : i ≠ 2) (a : ℝ)
    (hP : partialDerivative i + a • partialDerivative 2 + multiplication u ∈ E) :
    partialDerivative 2 u = 0 := by
  let J := hiddenEuler + multiplication B
  let P := partialDerivative i + a • partialDerivative 2 + multiplication u
  have hmem := E.add_mem (E.lie_mem hJ (E.lie_mem hJ hP)) (E.lie_mem hJ hP)
  rw [euler_affine_firstOrder_lie_polynomial B u hB i hi a] at hmem
  have hv := hfun _ hmem
  have hbi : partialDerivative 2 (partialDerivative i B) = 0 := by
    rw [partialDerivative_commute_apply, hB, map_zero]
  simp only [map_sub, map_add, partial_hiddenEuler_apply, hbi, sub_zero] at hv
  have hz : (hiddenEuler + (1 : ℝ) • (1 : Operator))
      ((hiddenEuler + (2 : ℝ) • (1 : Operator)) (partialDerivative 2 u)) = 0 := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul, one_smul]
    convert hv using 1 <;> module
  exact positive_hiddenEuler_shift_kernel 2 (by norm_num) (partialDerivative 2 u)
    (positive_hiddenEuler_shift_kernel 1 (by norm_num) _ hz)

/-- The adapted function-space hypothesis discharges hidden independence
of all actual multiplication elements, hence of the first-order remainder. -/
theorem adapted_firstOrder_hidden_independent
    (E : LieSubalgebra ℝ Operator) (hfun : AdaptedFunctionSpace E)
    (B u : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (i : Fin 3) (hi : i ≠ 2) (a : ℝ)
    (hP : partialDerivative i + a • partialDerivative 2 + multiplication u ∈ E) :
    partialDerivative 2 u = 0 := by
  apply firstOrder_hidden_independent_of_function_space E ?_ B u hB hJ i hi a hP
  intro v hv
  obtain ⟨c, a₀, a₁, rfl⟩ := hfun v hv
  have hOne : partialDerivative 2 smoothOne = 0 := by
    simpa only [one_smul] using partialDerivative_const 2 1
  simp only [map_add, map_smul, hOne, partialDerivative_linearFunction]
  simp [coordinateVector]

end Wong.SmoothModel
