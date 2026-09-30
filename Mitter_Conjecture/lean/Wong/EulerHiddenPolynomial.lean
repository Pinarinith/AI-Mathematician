import Wong.EulerNormalCoefficients
import Wong.HiddenPolynomialFiltration
import Wong.EulerSmooth

/-!
# Actual Euler annihilators imply globally polynomial hidden coefficients

The proof uses genuine coordinate slices, a single uniform ordinary
vanishing derivative for each fixed Euler polynomial, and the faithful
normal form. No pointwise-to-uniform assumption is made.
-/

noncomputable section
namespace Wong.SmoothModel
open scoped ContDiff
set_option maxHeartbeats 800000

def hiddenSliceLinear (x : State) : Smooth →ₗ[ℝ] (ℝ → ℝ) where
  toFun u := coordinateSlice u x 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem hiddenSliceLinear_apply (x : State) (u : Smooth) :
    hiddenSliceLinear x u = coordinateSlice u x 2 := rfl

/-- Restricting the actual hidden vector field to a coordinate line is
exactly the ordinary one-variable Euler operator. -/
theorem hiddenEuler_slice (u : Smooth) (x : State) :
    coordinateSlice (hiddenEuler u) x 2 =
      fun t => t * deriv (coordinateSlice u x 2) t := by
  rw [deriv_coordinateSlice]
  funext t
  simp [coordinateSlice, hiddenEuler, Module.End.mul_apply, linearFunction,
    coordinateVector, Pi.single_apply]

theorem hiddenEuler_power_slice (n : ℕ) (u : Smooth) (x : State) :
    coordinateSlice ((hiddenEuler ^ n) u) x 2 =
      Wong.EulerSmooth.eulerIterate (coordinateSlice u x 2) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change coordinateSlice (hiddenEuler ((hiddenEuler ^ n) u)) x 2 = _
    rw [hiddenEuler_slice, ih]
    rfl

/-- A polynomial in the actual smooth hidden Euler operator restricts to
its explicitly defined one-variable differential polynomial. -/
theorem hiddenEuler_aeval_slice (Q : Polynomial ℝ) (u : Smooth) (x : State) :
    coordinateSlice ((Polynomial.aeval hiddenEuler Q) u) x 2 =
      Wong.EulerSmooth.eulerPolynomialAction Q (coordinateSlice u x 2) := by
  change hiddenSliceLinear x ((Polynomial.aeval hiddenEuler Q) u) = _
  rw [Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  funext t
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    hiddenSliceLinear_apply, hiddenEuler_power_slice,
    Wong.EulerSmooth.eulerPolynomialAction]

/-- Crucially, the derivative order is independent of the visible
coordinates and of the function annihilated by the fixed polynomial. -/
theorem hiddenEuler_annihilator_uniform_partial_nilpotence
    (Q : Polynomial ℝ) (hQ : Q ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ u : Smooth,
      (Polynomial.aeval hiddenEuler Q) u = 0 → (partialDerivative 2 ^ n) u = 0 := by
  obtain ⟨n, hn, hnil⟩ := Wong.EulerSmooth.uniform_nilpotence_of_euler_annihilator Q hQ
  refine ⟨n, hn, ?_⟩
  intro u hu
  apply Subtype.ext
  funext x
  change ((partialDerivative 2 ^ n) u).1 x = 0
  have hz : Wong.EulerSmooth.eulerPolynomialAction Q (coordinateSlice u x 2) = 0 := by
    rw [← hiddenEuler_aeval_slice, hu]
    rfl
  have hd := hnil (coordinateSlice u x 2) (coordinateSlice_smooth u x 2) hz
  rw [iteratedDeriv_coordinateSlice] at hd
  have hx := congrFun hd (x 2)
  simpa only [coordinateSlice, Function.update_eq_self, Pi.zero_apply] using hx

/-- Translation of the Euler polynomial accounts exactly for the
multi-index weight of a normal coefficient. -/
def shiftedEulerPolynomial (Q : Polynomial ℝ) (α : MultiIndex) : Polynomial ℝ :=
  Q.comp (Polynomial.X + Polynomial.C (-(α 2 : ℝ)))

theorem shiftedEulerPolynomial_ne_zero (Q : Polynomial ℝ) (hQ : Q ≠ 0)
    (α : MultiIndex) : shiftedEulerPolynomial Q α ≠ 0 := by
  exact Polynomial.comp_X_add_C_ne_zero_iff.mpr hQ

theorem shiftedEulerPolynomial_aeval (Q : Polynomial ℝ) (α : MultiIndex) :
    Polynomial.aeval hiddenEuler (shiftedEulerPolynomial Q α) =
      Polynomial.aeval (shiftedHiddenEuler α) Q := by
  rw [shiftedEulerPolynomial, Polynomial.aeval_comp]
  congr 1
  simp [shiftedHiddenEuler, Algebra.smul_def, sub_eq_add_neg]

theorem euler_annihilator_hidden_coefficient_nilpotence (Q : Polynomial ℝ) (hQ : Q ≠ 0)
    (p : NormalForm)
    (hp : (Polynomial.aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) (normalAction p) = 0)
    (α : MultiIndex) : ∃ n, (partialDerivative 2 ^ n) (p α) = 0 := by
  obtain ⟨n, _, hn⟩ := hiddenEuler_annihilator_uniform_partial_nilpotence
    (shiftedEulerPolynomial Q α) (shiftedEulerPolynomial_ne_zero Q hQ α)
  refine ⟨n, hn (p α) ?_⟩
  rw [shiftedEulerPolynomial_aeval]
  exact euler_annihilator_normal_coefficient Q p hp α

/-- The actual smooth Euler finite-module lemma: finite dimensionality,
a true Euler-plus-visible-potential element, and hidden independence of
that potential give a common hidden derivative bound on all coefficients
of every normal form in the original estimation algebra. -/
theorem estimationAlgebra_uniform_hidden_nilpotence {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ estimationAlgebra f h) :
    ∃ N : ℕ, ∀ p : NormalForm, normalAction p ∈ estimationAlgebra f h →
      ∀ α, (partialDerivative 2 ^ N) (p α) = 0 := by
  obtain ⟨Q, hQ, hkill⟩ := hiddenEuler_ad_common_annihilator f h B hB hJ
  obtain ⟨N, hN⟩ := actual_uniform_hidden_degree_bound (estimationAlgebra f h).toSubmodule
  refine ⟨N, ?_⟩
  intro p hp
  exact hN p hp (fun α =>
    euler_annihilator_hidden_coefficient_nilpotence Q hQ p (hkill _ hp) α)

end Wong.SmoothModel
