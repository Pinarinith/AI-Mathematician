import Wong.GlobalRiccatiOddRayMoment

/-! Global directional cubic Taylor and compact-test Riccati rigidity.
The lower coefficients are actual smooth functions, including arbitrary
hidden-coordinate profiles; they are not assumed polynomial. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open scoped ContDiff
open MeasureTheory Measure

def smoothRay (u : Smooth) (x v : State) : ℝ → ℝ := fun t => u.1 (x+t•v)

theorem smoothRay_smooth (u : Smooth) (x v : State) : ContDiff ℝ ∞ (smoothRay u x v) :=
  (smooth u).comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem deriv_smoothRay (u : Smooth) (x v : State) :
    deriv (smoothRay u x v) = smoothRay (directionalDerivative v u) x v := by
  funext t
  have hl : HasDerivAt (fun t : ℝ => x+t•v) v t := by
    simpa only [Pi.add_def, zero_add, one_smul, id_eq] using
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)
  have hf : HasFDerivAt u.1 (fderiv ℝ u.1 (x+t•v)) (x+t•v) :=
    (((smooth u).differentiable (by simp)).differentiableAt.hasFDerivAt)
  have hd := hf.comp_hasDerivAt t hl
  change deriv (fun t => u.1 (x+t•v)) t = (directionalDerivative v u).1 (x+t•v)
  rw [directionalDerivative_apply]
  simpa only [Function.comp_def] using hd.deriv

theorem iteratedDeriv_smoothRay (n : ℕ) (u : Smooth) (x v : State) :
    iteratedDeriv n (smoothRay u x v) = smoothRay ((directionalDerivative v ^ n) u) x v := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ', deriv_smoothRay, ih, pow_succ]
    rfl

theorem iteratedDeriv_polynomial_eval (p : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => p.eval t) =
      fun t => (Polynomial.derivative^[n] p).eval t := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun t : ℝ => p.eval t) = fun t => p.derivative.eval t := by
      funext t
      exact Polynomial.deriv p
    rw [hd, ih, Function.iterate_succ_apply]

theorem smoothRay_cubic_taylor (u : Smooth) (v : State) (d : ℝ)
    (hu : (directionalDerivative v ^ 3) u = d • smoothOne) (x : State) (t : ℝ) :
    u.1 (x+t•v) = u.1 x + (directionalDerivative v u).1 x*t +
      ((directionalDerivative v ^ 2) u).1 x/2*t^2 + d/6*t^3 := by
  have hdc : directionalDerivative v (d • smoothOne) = 0 := by
    simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
      partialDerivative_const, smul_zero, Finset.sum_const_zero]
  have hu4 : (directionalDerivative v ^ 4) u = 0 := by
    rw [show 4=1+3 from rfl, pow_add, pow_one, Module.End.mul_apply, hu, hdc]
  have hnil : iteratedDeriv (3+1) (smoothRay u x v) = 0 := by
    rw [iteratedDeriv_smoothRay, hu4]
    rfl
  obtain ⟨p, hp, he⟩ := Wong.FunctionElements.polynomial_of_iteratedDeriv_eq_zero
    3 (smoothRay u x v) (smoothRay_smooth u x v) hnil
  have hcoef (n : ℕ) :
      (Polynomial.derivative^[n] p).eval 0 = ((directionalDerivative v ^ n) u).1 x := by
    have hh := congrArg (fun f : ℝ → ℝ => iteratedDeriv n f 0) (funext he)
    rw [iteratedDeriv_polynomial_eval, iteratedDeriv_smoothRay] at hh
    simpa [smoothRay] using hh
  have h0 : p.coeff 0 = u.1 x := by
    simpa only [Function.iterate_zero_apply, ← Polynomial.coeff_zero_eq_eval_zero,
      pow_zero, Module.End.one_apply] using hcoef 0
  have h1 : p.coeff 1 = (directionalDerivative v u).1 x := by
    have hh := hcoef 1
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative] at hh
    norm_num [Nat.descFactorial, pow_one] at hh
    exact hh
  have h2 : 2*p.coeff 2 = ((directionalDerivative v ^ 2) u).1 x := by
    have hh := hcoef 2
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative] at hh
    norm_num [Nat.descFactorial, nsmul_eq_mul] at hh
    exact hh
  have h3 : 6*p.coeff 3 = d := by
    have hh := hcoef 3
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, hu] at hh
    norm_num [Nat.descFactorial, nsmul_eq_mul, smoothOne] at hh
    exact hh
  have hexp := Polynomial.eval_eq_sum_range' (p := p) (n := 4) (by omega) t
  rw [he] at hexp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hexp
  change u.1 (x+t•v) = _ at hexp
  have h2' : p.coeff 2 = ((directionalDerivative v ^ 2) u).1 x/2 := by linarith
  have h3' : p.coeff 3 = d/6 := by linarith
  rw [h0,h1,h2',h3'] at hexp
  simpa only [pow_zero, mul_one, pow_one] using hexp


def smoothTestFunctional (μ : Measure State) [IsAddHaarMeasure μ]
    (φ : Smooth) (hφ : HasCompactSupport φ.1) : Smooth →ₗ[ℝ] ℝ where
  toFun u := ∫ x, u.1 x * (φ.1 x)^2 ∂μ
  map_add' u w := by
    have hi (z : Smooth) : Integrable (fun x : State => z.1 x*(φ.1 x)^2) μ := by
      simpa only [smoothMul_apply, pow_two] using
        smooth_compact_multiplier_integrable μ z (smoothMul φ φ) hφ.mul_right
    simpa only [Submodule.coe_add, Pi.add_apply, add_mul] using integral_add (hi u) (hi w)
  map_smul' c u := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _

theorem smoothTestFunctional_one (μ : Measure State) [IsAddHaarMeasure μ]
    (φ : Smooth) (hφ : HasCompactSupport φ.1) :
    smoothTestFunctional μ φ hφ smoothOne = smoothTestMass μ φ := by
  simp [smoothTestFunctional, smoothTestMass, smoothOne]

def smoothCubicRayMoment (F : Smooth →ₗ[ℝ] ℝ) (u : Smooth) (v : State) (d : ℝ) :
    Polynomial ℝ :=
  Polynomial.C (F u) + Polynomial.C (F (directionalDerivative v u))*Polynomial.X +
    Polynomial.C (F ((directionalDerivative v^2) u)/2)*Polynomial.X^2 +
    Polynomial.C (d/6*F smoothOne)*Polynomial.X^3

theorem smoothCubicRayMoment_degree (F : Smooth →ₗ[ℝ] ℝ) (u : Smooth) (v : State) (d : ℝ) :
    (smoothCubicRayMoment F u v d).natDegree ≤ 3 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · exact (Polynomial.natDegree_mul_le).trans (by simp)
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  · exact (Polynomial.natDegree_mul_le).trans (by
      simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
      rfl)

theorem smoothCubicRayMoment_coeff_three (F : Smooth →ₗ[ℝ] ℝ)
    (u : Smooth) (v : State) (d : ℝ) :
    (smoothCubicRayMoment F u v d).coeff 3 = d/6*F smoothOne := by
  simp only [smoothCubicRayMoment, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  norm_num

theorem smoothCubicRayMoment_eval (F : Smooth →ₗ[ℝ] ℝ)
    (u : Smooth) (v : State) (d : ℝ)
    (hu : (directionalDerivative v^3) u=d•smoothOne) (t : ℝ) :
    (smoothCubicRayMoment F u v d).eval t = F (translationPullback (t•v) u) := by
  have he : translationPullback (t•v) u = u + t•directionalDerivative v u +
      (t^2/2)•((directionalDerivative v^2) u) + (d*t^3/6)•smoothOne := by
    apply Subtype.ext
    funext x
    change u.1 (x+t•v) = _
    rw [smoothRay_cubic_taylor u v d hu x t]
    simp [smoothOne]
    ring
  rw [he]
  simp [smoothCubicRayMoment, map_add, map_smul]
  ring

/-- An actual smooth function with constant third directional derivative has
an exact cubic compact-test moment. No other-coordinate profile is discarded. -/
theorem smoothCubicRayMoment_actual_integral
    (μ : Measure State) [IsAddHaarMeasure μ] (φ : Smooth) (hφ : HasCompactSupport φ.1)
    (u : Smooth) (v : State) (d : ℝ) (hu : (directionalDerivative v^3) u=d•smoothOne)
    (t : ℝ) :
    (smoothCubicRayMoment (smoothTestFunctional μ φ hφ) u v d).eval t =
      ∫ x, u.1 (x+t•v)*(φ.1 x)^2 ∂μ := by
  rw [smoothCubicRayMoment_eval _ u v d hu t]
  rfl

def smoothRiccatiValue (f : Fin 3 → Smooth) : Smooth :=
  ∑ i, (partialDerivative i (f i) + smoothMul (f i) (f i))

theorem smoothRiccatiValue_apply (f : Fin 3 → Smooth) (x : State) :
    (smoothRiccatiValue f).1 x = globalRiccatiValue f x := by
  simp [smoothRiccatiValue, globalRiccatiValue, pow_two]

theorem constant_riccati_third_directional_zero
    (f : Fin 3 → Smooth) (v : State) (d : ℝ)
    (hd : (directionalDerivative v^3) (smoothRiccatiValue f)=d•smoothOne) : d=0 := by
  let μ : Measure State := volume
  let φ := riccatiFixedTest
  have hφ : HasCompactSupport φ.1 := riccatiFixedTest_compact
  let F := smoothTestFunctional μ φ hφ
  let q := smoothCubicRayMoment F (smoothRiccatiValue f) v d
  have hq := riccati_cubic_ray_moment_coeff_zero μ f φ hφ v q
    (smoothCubicRayMoment_degree F _ v d) (by
      intro t
      simpa only [smoothRiccatiValue_apply] using
        smoothCubicRayMoment_actual_integral μ φ hφ (smoothRiccatiValue f) v d hd t)
  rw [smoothCubicRayMoment_coeff_three] at hq
  have hm : 0 < F smoothOne := by
    rw [smoothTestFunctional_one]
    exact riccatiFixedTest_mass_positive μ
  have hz : d/6 = 0 := (mul_eq_zero.mp hq).resolve_right (ne_of_gt hm)
  linarith


theorem directional_cube_square_zero (u : Smooth) (v : State)
    (hu : (directionalDerivative v^2) u=0) :
    (directionalDerivative v^3) (smoothMul u u)=0 := by
  have h2 : directionalDerivative v (directionalDerivative v u)=0 := by
    simpa only [pow_succ, pow_one, pow_zero, Module.End.mul_apply, Module.End.one_apply] using hu
  change directionalDerivative v (directionalDerivative v
    (directionalDerivative v (smoothMul u u)))=0
  simp only [directionalDerivative_smoothMul, map_add, h2, map_zero]
  simp [smoothMul_eq_mul]

theorem smoothRiccatiValue_eq_eta {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    smoothRiccatiValue f = eta f h - ∑ j, smoothMul (h j) (h j) := by
  apply Subtype.ext
  funext x
  rw [smoothRiccatiValue_apply, globalRiccatiValue_eq_eta_sub_observations f h x]
  simp [pow_two]

/-- A constant third derivative of the actual eta along any real direction
vanishes once the actual observations are affine along that direction.
There is no finite-dimensionality or hidden-polynomial premise. -/
theorem eta_constant_third_directional_zero_of_observation_second_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (v : State) (d : ℝ)
    (heta : (directionalDerivative v^3) (eta f h)=d•smoothOne)
    (hobs : ∀j, (directionalDerivative v^2) (h j)=0) : d=0 := by
  apply constant_riccati_third_directional_zero f v d
  rw [smoothRiccatiValue_eq_eta f h, map_sub, _root_.map_sum, heta]
  simp only [directional_cube_square_zero _ v (hobs _), Finset.sum_const_zero, sub_zero]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.smoothRay_cubic_taylor
#print axioms Wong.SmoothModel.smoothCubicRayMoment_actual_integral
#print axioms Wong.SmoothModel.eta_constant_third_directional_zero_of_observation_second_zero
