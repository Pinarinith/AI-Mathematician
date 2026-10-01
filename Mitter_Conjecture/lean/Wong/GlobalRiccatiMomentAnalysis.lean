import Wong.PolynomialHiddenSpecializationBridge
import Wong.HiddenProfiles
import Wong.PolynomialRayLift
import Wong.QuadraticObservationMoment
import Wong.Ocone
import Mathlib.MeasureTheory.Constructions.Pi
import Wong.GlobalRiccatiTestBound
import Wong.RootAnalyticBridges
import Wong.PolynomialSmooth
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Polynomial.Basic

/-! Actual global Riccati compact tests and polynomial moment obstruction.
Compiled in one bundle to share Mathlib import memory on this workstation.
All ingredients and conclusions are proved in the original smooth model. -/

/-! Source segment: GlobalRiccatiSupportBound -/


/-! The actual global Riccati potential cannot be uniformly too negative
on the support of a nonzero compact smooth test function. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure

def smoothTestMass (μ : Measure State) (φ : Smooth) : ℝ :=
  ∫ x, (φ.1 x)^2 ∂μ

def smoothTestEnergy (μ : Measure State) (φ : Smooth) : ℝ :=
  ∫ x, ∑ i : Fin 3, ((partialDerivative i φ).1 x)^2 ∂μ

theorem compact_test_global_riccati_support_bound
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (φ : Smooth) (hφ : HasCompactSupport φ.1)
    (b : ℝ) (hb : ∀ x : State, φ.1 x ≠ 0 → globalRiccatiValue f x ≤ b) :
    -smoothTestEnergy μ φ ≤ b * smoothTestMass μ φ := by
  let R : Smooth := ∑ i : Fin 3, (partialDerivative i (f i) + smoothMul (f i) (f i))
  let Φ : Smooth := smoothMul φ φ
  have hΦ : HasCompactSupport Φ.1 := hφ.mul_right
  have hF : Integrable (fun x => globalRiccatiValue f x * (φ.1 x)^2) μ := by
    simpa only [R, Φ, globalRiccatiValue, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_add, Pi.add_apply, smoothMul_apply, pow_two] using
      smooth_compact_multiplier_integrable μ R Φ hΦ
  have hM : Integrable (fun x => (φ.1 x)^2) μ := by
    have hi : Integrable Φ.1 μ := (smooth Φ).continuous.integrable_of_hasCompactSupport hΦ
    change Integrable (fun x : State => φ.1 x * φ.1 x) μ at hi
    simpa only [pow_two] using hi
  have hupper : (∫ x, globalRiccatiValue f x * (φ.1 x)^2 ∂μ) ≤
      b * smoothTestMass μ φ := by
    calc
      _ ≤ ∫ x, b * (φ.1 x)^2 ∂μ := by
        apply integral_mono hF (hM.const_mul b)
        intro x
        by_cases hx : φ.1 x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_right (hb x hx) (sq_nonneg _)
      _ = _ := integral_const_mul _ _
  exact (compact_test_global_riccati_lower_bound μ f φ hφ).trans hupper

theorem exists_global_riccati_above_test_threshold
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (φ : Smooth) (hφ : HasCompactSupport φ.1)
    (hM : 0 < smoothTestMass μ φ) :
    ∃ x : State, φ.1 x ≠ 0 ∧
      -(smoothTestEnergy μ φ + 1) / smoothTestMass μ φ < globalRiccatiValue f x := by
  by_contra hn
  push Not at hn
  have hb := compact_test_global_riccati_support_bound μ f φ hφ
    (-(smoothTestEnergy μ φ + 1) / smoothTestMass μ φ) hn
  have hc : (-(smoothTestEnergy μ φ + 1) / smoothTestMass μ φ) *
      smoothTestMass μ φ = -(smoothTestEnergy μ φ + 1) :=
    div_mul_cancel₀ _ hM.ne'
  rw [hc] at hb
  linarith

end Wong.SmoothModel

#print axioms Wong.SmoothModel.exists_global_riccati_above_test_threshold

/-! Source segment: GlobalRiccatiTranslation -/


/-! The compact-test bound applies to the actual translated drift.  This
keeps the test mass and energy fixed without translating the test function. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure

theorem globalRiccatiValue_translationDrift
    (b : State) (f : Fin 3 → Smooth) (x : State) :
    globalRiccatiValue (translationDrift b f) x = globalRiccatiValue f (x + b) := by
  unfold globalRiccatiValue translationDrift
  simp only [partialDerivative_translationPullback]
  rfl

theorem compact_test_translated_global_riccati_lower_bound
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (φ : Smooth) (hφ : HasCompactSupport φ.1)
    (b : State) :
    -smoothTestEnergy μ φ ≤
      ∫ x, globalRiccatiValue f (x + b) * (φ.1 x)^2 ∂μ := by
  have hb := compact_test_global_riccati_lower_bound μ (translationDrift b f) φ hφ
  simpa only [smoothTestEnergy, globalRiccatiValue_translationDrift] using hb

end Wong.SmoothModel

#print axioms Wong.SmoothModel.compact_test_translated_global_riccati_lower_bound

/-! Source segment: GlobalRiccatiFixedTest -/


/-! A concrete smooth compact test of positive mass on the original state
space. Its existence is proved, rather than added to the model hypotheses. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure

def riccatiTestBump : ContDiffBump (0 : State) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def riccatiFixedTest : Smooth := ⟨riccatiTestBump, riccatiTestBump.contDiff⟩

theorem riccatiFixedTest_compact : HasCompactSupport riccatiFixedTest.1 :=
  riccatiTestBump.hasCompactSupport

theorem riccatiFixedTest_zero : riccatiFixedTest.1 0 = 1 :=
  riccatiTestBump.one_of_mem_closedBall (by simp [riccatiTestBump])

theorem riccatiFixedTest_mass_positive
    (μ : Measure State) [IsAddHaarMeasure μ] :
    0 < smoothTestMass μ riccatiFixedTest := by
  have hc : HasCompactSupport (fun x : State => riccatiFixedTest.1 x ^ 2) := by
    have hc' : HasCompactSupport (smoothMul riccatiFixedTest riccatiFixedTest).1 :=
      riccatiFixedTest_compact.mul_right
    change HasCompactSupport
      (fun x : State => riccatiFixedTest.1 x * riccatiFixedTest.1 x) at hc'
    simpa only [pow_two] using hc'
  unfold smoothTestMass
  apply integral_pos_of_integrable_nonneg_nonzero
    ((smooth riccatiFixedTest).continuous.pow 2)
    (((smooth riccatiFixedTest).continuous.pow 2).integrable_of_hasCompactSupport
      hc) (fun x => sq_nonneg _)
    (x := (0 : State))
  simp [riccatiFixedTest_zero]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.riccatiFixedTest_mass_positive

/-! Source segment: PolynomialTestFunctional -/


/-! The actual compact-test integral is a real linear functional on the
position polynomials. All polynomial integrability obligations are proved. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure MvPolynomial

theorem polynomial_test_product_integrable
    (μ : Measure State) [IsAddHaarMeasure μ]
    (φ : Smooth) (hφ : HasCompactSupport φ.1) (p : RealPoly) :
    Integrable (fun x : State => eval x p * (φ.1 x)^2) μ := by
  simpa only [polynomialSmooth_apply, smoothMul_apply, pow_two] using
    smooth_compact_multiplier_integrable μ (polynomialSmooth p)
      (smoothMul φ φ) hφ.mul_right

def polynomialTestFunctional
    (μ : Measure State) [IsAddHaarMeasure μ]
    (φ : Smooth) (hφ : HasCompactSupport φ.1) : RealPoly →ₗ[ℝ] ℝ where
  toFun p := ∫ x, eval x p * (φ.1 x)^2 ∂μ
  map_add' p q := by
    simp only [eval_add, add_mul]
    exact integral_add (polynomial_test_product_integrable μ φ hφ p)
      (polynomial_test_product_integrable μ φ hφ q)
  map_smul' c p := by
    change (∫ x, eval x (c • p) * (φ.1 x)^2 ∂μ) =
      c * ∫ x, eval x p * (φ.1 x)^2 ∂μ
    simp only [smul_eq_C_mul, eval_mul, eval_C, mul_assoc]
    exact integral_const_mul _ _

@[simp] theorem polynomialTestFunctional_apply
    (μ : Measure State) [IsAddHaarMeasure μ]
    (φ : Smooth) (hφ : HasCompactSupport φ.1) (p : RealPoly) :
    polynomialTestFunctional μ φ hφ p = ∫ x, eval x p * (φ.1 x)^2 ∂μ := rfl

theorem polynomialTestFunctional_one
    (μ : Measure State) [IsAddHaarMeasure μ]
    (φ : Smooth) (hφ : HasCompactSupport φ.1) :
    polynomialTestFunctional μ φ hφ 1 = smoothTestMass μ φ := by
  simp only [polynomialTestFunctional_apply, map_one, one_mul, smoothTestMass]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.polynomialTestFunctional_one

/-! Source segment: RiccatiRayMoment -/


/-! A polynomial moment of an actual globally smooth Riccati potential
cannot have a negative highest coefficient. This is the analytic obstruction
needed below; it introduces no growth assumption on the drift. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure Filter

theorem riccati_ray_moment_nonnegative_top
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (φ : Smooth) (hφ : HasCompactSupport φ.1)
    (v : State) (q : Polynomial ℝ) (d : ℕ) (hd : 0 < d)
    (hdegree : q.natDegree ≤ d)
    (hmoment : ∀ t : ℝ, q.eval t =
      ∫ x, globalRiccatiValue f (x + t • v) * (φ.1 x)^2 ∂μ) :
    0 ≤ q.coeff d := by
  by_contra hn
  have hnegative : q.coeff d < 0 := lt_of_not_ge hn
  have hnat : q.natDegree = d :=
    le_antisymm hdegree (Polynomial.le_natDegree_of_ne_zero hnegative.ne)
  have hpos : 0 < q.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
  have hleading : q.leadingCoeff ≤ 0 := by
    rw [← Polynomial.coeff_natDegree, hnat]
    exact hnegative.le
  have htend : Tendsto (fun t : ℝ => q.eval t) atTop atBot :=
    q.tendsto_atBot_of_leadingCoeff_nonpos hpos hleading
  have hevent : ∀ᶠ t : ℝ in atTop, q.eval t < -smoothTestEnergy μ φ :=
    htend.eventually (eventually_lt_atBot (-smoothTestEnergy μ φ))
  obtain ⟨t, ht⟩ := hevent.exists
  have hb := compact_test_translated_global_riccati_lower_bound μ f φ hφ (t • v)
  rw [← hmoment t] at hb
  linarith

end Wong.SmoothModel

#print axioms Wong.SmoothModel.riccati_ray_moment_nonnegative_top


/-! Source segment: RiccatiPolynomialTop -/

/-! A proved compact-test moment connects the actual potential to highest
homogeneous polynomial terms. No drift growth condition is assumed. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure MvPolynomial

theorem rayMoment_polynomialTestFunctional_eval
    (μ : Measure State) [IsAddHaarMeasure μ]
    (φ : Smooth) (hφ : HasCompactSupport φ.1)
    (v : State) (p : RealPoly) (t : ℝ) :
    (rayMoment (polynomialTestFunctional μ φ hφ) v p).eval t =
      ∫ x, eval (x + t • v) p * (φ.1 x)^2 ∂μ := by
  rw [rayMoment_eval, polynomialTestFunctional_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [rayLift_base_eval]

theorem riccati_polynomial_top_nonnegative
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (p : RealPoly)
    (hpotential : ∀ x : State, globalRiccatiValue f x = eval x p)
    (v : State) (d : ℕ) (hd : 0 < d) (hp : p.totalDegree ≤ d) :
    0 ≤ eval v (homogeneousComponent d p) := by
  let φ := riccatiFixedTest
  have hφ : HasCompactSupport φ.1 := riccatiFixedTest_compact
  let F := polynomialTestFunctional μ φ hφ
  let q := rayMoment F v p
  have hm : ∀ t : ℝ, q.eval t =
      ∫ x, globalRiccatiValue f (x + t • v) * (φ.1 x)^2 ∂μ := by
    intro t
    rw [rayMoment_polynomialTestFunctional_eval]
    simp only [hpotential]
  have hn := riccati_ray_moment_nonnegative_top μ f φ hφ v q d hd
    ((rayMoment_degree F v p).trans hp) hm
  have hc : q.coeff d = eval v (homogeneousComponent d p) * smoothTestMass μ φ := by
    rw [rayMoment_top F v p d hp, polynomialTestFunctional_one]
  rw [hc] at hn
  have hM : 0 < smoothTestMass μ φ := riccatiFixedTest_mass_positive μ
  nlinarith

end Wong.SmoothModel

#print axioms Wong.SmoothModel.riccati_polynomial_top_nonnegative


/-! Source segment: AffineObservationsOfQuadraticEta -/

/-! The actual globally smooth Riccati equation excludes quadratic observation
terms when the original eta is quadratic. Compact-test moments supply the
analytic step; observation polynomiality comes from the proved Ocone theorem. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure MvPolynomial

theorem globalRiccatiValue_eq_eta_sub_observations {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (x : State) :
    globalRiccatiValue f x = (eta f h).1 x - ∑ j, (h j).1 x ^ 2 := by
  simp only [eta, globalRiccatiValue, Submodule.coe_add, Submodule.coe_sum,
    Finset.sum_apply, Pi.add_apply, smoothMul_apply, pow_two]
  ring

theorem observations_affine_of_quadratic_eta_polynomials {m : ℕ}
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (Q : RealPoly) (P : Fin m → RealPoly)
    (hQ : Q.totalDegree ≤ 2) (hP : ∀ j, (P j).totalDegree ≤ 2)
    (heta : polynomialSmooth Q = eta f h)
    (hobs : ∀ j, polynomialSmooth (P j) = h j) :
    ∀ j, (P j).totalDegree ≤ 1 := by
  let φ := riccatiFixedTest
  have hφ : HasCompactSupport φ.1 := riccatiFixedTest_compact
  let F := polynomialTestFunctional μ φ hφ
  have hmass : 0 < F 1 := by
    rw [polynomialTestFunctional_one]
    exact riccatiFixedTest_mass_positive μ
  apply quadratic_observations_affine_of_ray_coeff_nonnegative F Q P hQ hP hmass
  intro v
  let q := quadraticObservationMoment F v Q P
  have hpotential (x : State) :
      eval x (Q - ∑ j : Fin m, (P j)^2) = globalRiccatiValue f x := by
    rw [globalRiccatiValue_eq_eta_sub_observations]
    simp only [eval_sub, _root_.map_sum, map_pow]
    rw [← heta, polynomialSmooth_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← hobs j, polynomialSmooth_apply]
  have hmoment : ∀ t : ℝ, q.eval t =
      ∫ x, globalRiccatiValue f (x + t • v) * (φ.1 x)^2 ∂μ := by
    intro t
    have heq : q = rayMoment F v (Q - ∑ j : Fin m, (P j)^2) := by
      rw [rayMoment_sub, rayMoment_sum]
      rfl
    rw [heq, rayMoment_polynomialTestFunctional_eval]
    simp only [hpotential]
  exact riccati_ray_moment_nonnegative_top μ f φ hφ v q 4 (by decide)
    (quadraticObservationMoment_degree F v Q P hQ hP) hmoment

theorem observations_affine_of_quadratic_eta {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (Q : RealPoly) (hQ : Q.totalDegree ≤ 2)
    (heta : polynomialSmooth Q = eta f h) :
    ∀ j, ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = h j := by
  have hpoly (j : Fin m) :
      ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = h j := by
    apply function_element_polynomial_degree_le_two f h (h j)
    exact LieSubalgebra.subset_lieSpan (Or.inr ⟨j, rfl⟩)
  choose P hP he using hpoly
  have hdegree := observations_affine_of_quadratic_eta_polynomials
    (volume : Measure State) f h Q P hQ hP heta he
  exact fun j => ⟨P j, hdegree j, he j⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.observations_affine_of_quadratic_eta


/-! Source segment: AffineObservationsOfVisibleQuadraticEta -/

/-! The compact-test obstruction also applies to a quadratic visible eta
plus an arbitrary smooth hidden profile, when the genuine observations are
hidden independent. The hidden profile is retained in every actual integral. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MeasureTheory Measure MvPolynomial

theorem observations_affine_of_visible_quadratic_eta_polynomials {m : ℕ}
    (μ : Measure State) [IsAddHaarMeasure μ]
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (Q : RealPoly) (P : Fin m → RealPoly) (ψ : Smooth)
    (hQ : Q.totalDegree ≤ 2) (hP : ∀ j, (P j).totalDegree ≤ 2)
    (hhidden : ∀ j, pderiv 2 (P j) = 0)
    (heta : eta f h = polynomialSmooth Q + ψ)
    (hobs : ∀ j, polynomialSmooth (P j) = h j)
    (hψ0 : partialDerivative 0 ψ = 0) (hψ1 : partialDerivative 1 ψ = 0) :
    ∀ j, (P j).totalDegree ≤ 1 := by
  let φ := riccatiFixedTest
  have hφ : HasCompactSupport φ.1 := riccatiFixedTest_compact
  let F := polynomialTestFunctional μ φ hφ
  have hmass : 0 < F 1 := by
    rw [polynomialTestFunctional_one]
    exact riccatiFixedTest_mass_positive μ
  obtain ⟨ρ, _hρsmooth, hρ⟩ := exists_hidden_profile ψ hψ0 hψ1
  have hψint : Integrable (fun x : State => ψ.1 x * (φ.1 x)^2) μ := by
    simpa only [smoothMul_apply, pow_two] using
      smooth_compact_multiplier_integrable μ ψ (smoothMul φ φ) hφ.mul_right
  let cψ : ℝ := ∫ x, ψ.1 x * (φ.1 x)^2 ∂μ
  apply quadratic_observations_affine_of_ray_coeff_nonnegative F Q P hQ hP hmass
  intro v
  let w : State := ![v 0, v 1, 0]
  let R : RealPoly := Q - ∑ j : Fin m, (P j)^2
  let q : Polynomial ℝ := quadraticObservationMoment F w Q P + Polynomial.C cψ
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
    have hbase : quadraticObservationMoment F w Q P = rayMoment F w R := by
      dsimp only [R]
      rw [rayMoment_sub, rayMoment_sum]
      rfl
    have hRint : Integrable (fun x : State => eval (x + t • w) R * (φ.1 x)^2) μ := by
      simpa only [rayLift_base_eval] using polynomial_test_product_integrable μ φ hφ
        ((rayLift w R).eval (MvPolynomial.C t))
    have hψtranslate (x : State) : ψ.1 (x + t • w) = ψ.1 x := by
      rw [hρ, hρ]
      simp [w]
    have hpotential (x : State) : globalRiccatiValue f (x + t • w) =
        eval (x + t • w) R + ψ.1 x := by
      rw [globalRiccatiValue_eq_eta_sub_observations, heta]
      simp only [Submodule.coe_add, Pi.add_apply, polynomialSmooth_apply,
        hψtranslate, R, eval_sub, _root_.map_sum, map_pow]
      have heobs : (∑ j : Fin m, (h j).1 (x + t • w)^2) =
          ∑ j : Fin m, eval (x + t • w) (P j)^2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← hobs j, polynomialSmooth_apply]
      rw [heobs]
      ring
    simp only [q, Polynomial.eval_add, Polynomial.eval_C]
    rw [hbase, rayMoment_polynomialTestFunctional_eval]
    change (∫ x, eval (x + t • w) R * (φ.1 x)^2 ∂μ) +
      (∫ x, ψ.1 x * (φ.1 x)^2 ∂μ) = _
    rw [← integral_add hRint hψint]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hpotential]
    ring
  have hdegree : q.natDegree ≤ 4 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact quadraticObservationMoment_degree F w Q P hQ hP
    · simp
  have hn := riccati_ray_moment_nonnegative_top μ f φ hφ w q 4 (by decide) hdegree hmoment
  have hcoeff : q.coeff 4 = (quadraticObservationMoment F v Q P).coeff 4 := by
    simp only [q, Polynomial.coeff_add, Polynomial.coeff_C, show (4 : ℕ) ≠ 0 by decide,
      if_false, add_zero]
    rw [quadraticObservationMoment_coeff_four F w Q P hQ hP,
      quadraticObservationMoment_coeff_four F v Q P hQ hP]
    simp only [hsame]
  rwa [hcoeff] at hn

theorem observations_affine_of_visible_quadratic_eta {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (Q : RealPoly) (ψ : Smooth) (hQ : Q.totalDegree ≤ 2)
    (heta : eta f h = polynomialSmooth Q + ψ)
    (hobsHidden : ∀ j, partialDerivative 2 (h j) = 0)
    (hψ0 : partialDerivative 0 ψ = 0) (hψ1 : partialDerivative 1 ψ = 0) :
    ∀ j, ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = h j := by
  have hpoly (j : Fin m) : ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = h j := by
    apply function_element_polynomial_degree_le_two f h (h j)
    exact LieSubalgebra.subset_lieSpan (Or.inr ⟨j, rfl⟩)
  choose P hP he using hpoly
  have hpHidden (j : Fin m) : pderiv 2 (P j) = 0 := by
    apply polynomialSmooth_injective
    rw [← partialDerivative_polynomialSmooth, he j, hobsHidden j, polynomialSmooth_zero]
  have hd := observations_affine_of_visible_quadratic_eta_polynomials
    (volume : Measure State) f h Q P ψ hQ hP hpHidden heta he hψ0 hψ1
  exact fun j => ⟨P j, hd j, he j⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.observations_affine_of_visible_quadratic_eta
