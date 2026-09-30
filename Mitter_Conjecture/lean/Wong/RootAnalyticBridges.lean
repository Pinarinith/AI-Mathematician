import Wong.AffineFrameAlgebra
import Wong.CoordinateGenerators
import Wong.HiddenEulerNormalization
import Wong.HiddenProfiles
import Wong.EulerGeneralFinite
import Wong.EulerSpectral
import Wong.EulerFunctionSpace
import Wong.NormalSymbolsOrderBridge
import Wong.AffineGaugeRepresentative
import Wong.NormalFormAlgebra
import Wong.FirstOrderPolynomial
import Wong.PolynomialSmooth
import Wong.EulerNormalizedDiffusion
import Wong.EulerLinearCanonical

/-! Actual analytic and operator bridges are compiled together to share the
Mathlib import cost on this workstation. Original source segments are recorded
in campaign8h/root_analytic_sources. Every theorem retains its original name. -/


/-! Source segment: TranslationModel -/

/-! Pure translations preserve the original unit-diffusion filtering model,
including its defining eta and generated Lie algebra. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

@[simp] theorem actual_multiplication_one : multiplication (1 : Smooth) = (1 : Operator) :=
  multiplication_smoothOne

@[simp] theorem actual_partialDerivative_one (i : Fin 3) : partialDerivative i (1 : Smooth) = 0 := by
  simpa only [one_smul,smoothOne_eq_one] using partialDerivative_const i 1

@[simp] theorem actual_multiPartial_single_one (i : Fin 3) :
    multiPartial (Finsupp.single i 1) = partialDerivative i := by
  simpa only [normalAction_single,multiplication_smoothOne,one_mul] using normalAction_partial i

def translationPullback (b : State) : Smooth ≃ₗ[ℝ] Smooth :=
  affinePullback (ContinuousLinearEquiv.refl ℝ State) b

def translationDrift (b : State) (f : Fin 3 → Smooth) : Fin 3 → Smooth :=
  fun i => translationPullback b (f i)

def translationObservations {m : ℕ} (b : State) (h : Fin m → Smooth) : Fin m → Smooth :=
  fun j => translationPullback b (h j)

abbrev translationAlgebra (b : State) (E : LieSubalgebra ℝ Operator) :
    LieSubalgebra ℝ Operator := affineAlgebra (ContinuousLinearEquiv.refl ℝ State) b E

theorem translationPullback_symm (b : State) :
    (translationPullback b).symm = translationPullback (-b) := by
  ext u x
  simp [translationPullback, affinePullback, sub_eq_add_neg]

@[simp] theorem translationPullback_smoothOne (b : State) :
    translationPullback b smoothOne = smoothOne := rfl

theorem translationPullback_smoothMul (b : State) (u v : Smooth) :
    translationPullback b (smoothMul u v) =
      smoothMul (translationPullback b u) (translationPullback b v) := rfl

theorem partialDerivative_translationPullback (b : State) (i : Fin 3) (u : Smooth) :
    partialDerivative i (translationPullback b u) = translationPullback b (partialDerivative i u) := by
  rw [← coordinate_directionalDerivative]
  change directionalDerivative (coordinateVector i)
    (affinePullback (ContinuousLinearEquiv.refl ℝ State) b u) = _
  rw [directionalDerivative_affinePullback]
  rfl

theorem eta_translationDrift {m : ℕ} (b : State) (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    eta (translationDrift b f) (translationObservations b h) = translationPullback b (eta f h) := by
  simp only [eta, translationDrift, translationObservations,
    partialDerivative_translationPullback, ← translationPullback_smoothMul,
    map_add, map_sum]

theorem translationConjugation_D (b : State) (f : Fin 3 → Smooth) (i : Fin 3) :
    affineConjugation (ContinuousLinearEquiv.refl ℝ State) b (D f i) =
      D (translationDrift b f) i := by
  simp only [D, map_sub, affineConjugation_multiplication,
    ← coordinate_directionalDerivative, affineConjugation_directionalDerivative]
  rfl

theorem translationConjugation_L0 {m : ℕ} (b : State) (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    affineConjugation (ContinuousLinearEquiv.refl ℝ State) b (L0 f h) =
      L0 (translationDrift b f) (translationObservations b h) := by
  simp only [L0, map_sub, map_smul, map_sum, map_mul, translationConjugation_D,
    affineConjugation_multiplication, eta_translationDrift]
  rfl

theorem translationAlgebra_estimationAlgebra {m : ℕ} (b : State)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    translationAlgebra b (estimationAlgebra f h) =
      estimationAlgebra (translationDrift b f) (translationObservations b h) := by
  unfold translationAlgebra affineAlgebra estimationAlgebra
  rw [LieSubalgebra.map_lieSpan]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  congr 1
  · congr 1
    exact translationConjugation_L0 b f h
  · congr 1
    funext j
    exact affineConjugation_multiplication _ _ _

theorem finiteDimensional_translationEstimationAlgebra {m : ℕ} (b : State)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    FiniteDimensional ℝ (estimationAlgebra (translationDrift b f) (translationObservations b h)) := by
  rw [← translationAlgebra_estimationAlgebra]
  exact affineAlgebra_finiteDimensional _ _ _

theorem translationPullback_linearFunction (b a : State) :
    translationPullback b (linearFunction a) =
      linearFunction a + ((linearFunction a).1 b) • smoothOne := by
  apply Subtype.ext
  funext x
  simp [translationPullback, affinePullback_apply, linearFunction,
    smoothOne, mul_add, Finset.sum_add_distrib]

theorem linearCoefficientSpace_translationAlgebra (b : State)
    (E : LieSubalgebra ℝ Operator) (hI : (1 : Operator) ∈ E) :
    linearCoefficientSpace (translationAlgebra b E) = linearCoefficientSpace E := by
  ext a
  change multiplication (linearFunction a) ∈ translationAlgebra b E ↔
    multiplication (linearFunction a) ∈ E
  rw [multiplication_mem_affineAlgebra_iff]
  change multiplication ((translationPullback b).symm (linearFunction a)) ∈ E ↔ _
  rw [translationPullback_symm, translationPullback_linearFunction,
    multiplication_add, multiplication_smul, multiplication_smoothOne]
  constructor
  · intro hp
    have hh := E.sub_mem hp (E.smul_mem ((linearFunction a).1 (-b)) hI)
    simpa only [add_sub_cancel_right] using hh
  · intro hp
    exact E.add_mem hp (E.smul_mem _ hI)

theorem linearRank_translationEstimationAlgebra {m : ℕ} (b : State)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2) :
    linearRank (estimationAlgebra (translationDrift b f) (translationObservations b h)) = 2 := by
  rw [← translationAlgebra_estimationAlgebra]
  change Module.finrank ℝ (linearCoefficientSpace (translationAlgebra b (estimationAlgebra f h))) = 2
  rw [linearCoefficientSpace_translationAlgebra b _
    (one_mem_estimationAlgebra_of_rank_two f h hrank)]
  exact hrank

theorem quadraticFree_translationEstimationAlgebra {m : ℕ} (b : State)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hq : QuadraticFree (estimationAlgebra f h)) :
    QuadraticFree (estimationAlgebra (translationDrift b f) (translationObservations b h)) := by
  rw [← translationAlgebra_estimationAlgebra]
  intro p hp ⟨A, hA, hact⟩
  have hAM : A = multiplication (polynomialSmooth p) := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    exact hact u x
  rw [hAM] at hA
  have hsource := (multiplication_mem_affineAlgebra_iff _ _ (estimationAlgebra f h)
    (polynomialSmooth p)).mp hA
  change multiplication ((translationPullback b).symm (polynomialSmooth p)) ∈
    estimationAlgebra f h at hsource
  obtain ⟨c, a, ha⟩ := quadraticFree_function_element_affine f h hq _ hsource
  have htrans := congrArg (translationPullback b) ha
  rw [LinearEquiv.apply_symm_apply, map_add, map_smul,
    translationPullback_smoothOne, translationPullback_linearFunction] at htrans
  have hpa : polynomialSmooth p =
      (c + (linearFunction a).1 b) • smoothOne + linearFunction a := by
    rw [htrans]
    module
  have hdeg := totalDegree_le_one_of_polynomialSmooth_affine p
    (c + (linearFunction a).1 b) a hpa
  omega

theorem coordinate_mem_translationEstimationAlgebra {m : ℕ} (b : State)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (i : Fin 3) (hx : multiplication (linearFunction (coordinateVector i)) ∈ estimationAlgebra f h) :
    multiplication (linearFunction (coordinateVector i)) ∈
      estimationAlgebra (translationDrift b f) (translationObservations b h) := by
  rw [← translationAlgebra_estimationAlgebra]
  change coordinateVector i ∈ linearCoefficientSpace (translationAlgebra b (estimationAlgebra f h))
  rw [linearCoefficientSpace_translationAlgebra b _
    (one_mem_estimationAlgebra_of_rank_two f h hrank)]
  exact hx

theorem wong_translationDrift (b : State) (f : Fin 3 → Smooth) (i j : Fin 3) :
    wong (translationDrift b f) i j = translationPullback b (wong f i j) := by
  simp only [wong, translationDrift, partialDerivative_translationPullback, map_sub]

theorem WongConstant_translationDrift_iff (b : State) (f : Fin 3 → Smooth) :
    WongConstant (translationDrift b f) ↔ WongConstant f := by
  constructor
  · rintro ⟨Ω, hΩ⟩
    refine ⟨Ω, ?_⟩
    intro i j x
    have hx := hΩ i j (x-b)
    rw [wong_translationDrift] at hx
    simpa [translationPullback, affinePullback_apply] using hx
  · rintro ⟨Ω, hΩ⟩
    refine ⟨Ω, ?_⟩
    intro i j x
    rw [wong_translationDrift]
    exact hΩ i j (x+b)

end Wong.SmoothModel


/-! Source segment: DirectionalDiffusion -/

/-! Explicit faithful normal forms of the actual affine and gauge transported
diffusion, with the original scalar potential retained. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
set_option maxHeartbeats 1000000

theorem directionalDerivative_smoothMul (v : State) (a u : Smooth) :
    directionalDerivative v (smoothMul a u) =
      smoothMul (directionalDerivative v a) u +
        smoothMul a (directionalDerivative v u) := by
  apply Subtype.ext
  funext x
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    partialDerivative_smoothMul, Submodule.coe_add, Submodule.coe_smul,
    Submodule.coe_sum, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
    smoothMul_apply, smul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem directional_square_expanded (v : State) (g : Smooth) :
    (directionalDerivative v - multiplication g) *
        (directionalDerivative v - multiplication g) =
      directionalDerivative v * directionalDerivative v -
        (2 : ℝ) • (multiplication g * directionalDerivative v) -
        multiplication (directionalDerivative v g) + multiplication (smoothMul g g) := by
  apply LinearMap.ext
  intro u
  change directionalDerivative v (directionalDerivative v u - smoothMul g u) -
    smoothMul g (directionalDerivative v u - smoothMul g u) = _
  rw [map_sub, directionalDerivative_smoothMul]
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, multiplication_apply, smoothMul_apply,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

def frameVectors (α β : ℝ) : Fin 3 → State :=
  ![coordinateVector 0 + α • coordinateVector 2,
    coordinateVector 1 + β • coordinateVector 2, coordinateVector 2]

@[simp] theorem frameVectors_zero (α β : ℝ) :
    frameVectors α β 0 = coordinateVector 0 + α • coordinateVector 2 := rfl

@[simp] theorem frameVectors_one (α β : ℝ) :
    frameVectors α β 1 = coordinateVector 1 + β • coordinateVector 2 := rfl

@[simp] theorem frameVectors_two (α β : ℝ) :
    frameVectors α β 2 = coordinateVector 2 := rfl

def frameDrift (f : Fin 3 → Smooth) (α β δ : ℝ) (Λ : Smooth) : Fin 3 → Smooth :=
  fun i => hiddenAffinePullback α β δ (f i) + directionalDerivative (frameVectors α β i) Λ

def frameScalar (g : Fin 3 → Smooth) (V : Smooth) (α β : ℝ) : Smooth :=
  (1/2 : ℝ) • ((∑i, smoothMul (g i) (g i)) -
    (∑i, directionalDerivative (frameVectors α β i) (g i)) - V)

def directionalDiffusion (α β : ℝ) (g : Fin 3 → Smooth) (V : Smooth) : Operator :=
  (1/2 : ℝ) • ∑i,
    (directionalDerivative (frameVectors α β i) - multiplication (g i)) *
      (directionalDerivative (frameVectors α β i) - multiplication (g i)) -
    (1/2 : ℝ) • multiplication V

theorem hiddenShear_symm_coordinate_vectors (α β : ℝ) (i : Fin 3) :
    (hiddenShear α β).symm (coordinateVector i) = frameVectors α β i := by
  obtain ⟨he₀, he₁⟩ := hiddenShear_symm_visible_vectors α β
  fin_cases i
  · exact he₀
  · exact he₁
  · exact hiddenShear_symm_hidden_vector α β

theorem actual_transported_filteringOperator (f : Fin 3 → Smooth) (V : Smooth)
    (α β δ : ℝ) (Λ : Smooth) :
    gaugeConjugation Λ (affineConjugation (hiddenShear α β) ![0,0,-δ]
      (filteringOperator f V)) =
      directionalDiffusion α β (frameDrift f α β δ Λ) (hiddenAffinePullback α β δ V) := by
  simp only [filteringOperator, map_sub, map_smul, map_sum, map_mul,
    hiddenFrame_D, hiddenShear_symm_coordinate_vectors,
    multiplication_neg_smooth]
  simp only [affineConjugation_multiplication, gaugeConjugation_multiplication]
  rfl

theorem directionalDiffusion_expanded (α β : ℝ) (g : Fin 3 → Smooth) (V : Smooth) :
    directionalDiffusion α β g V =
      (1/2 : ℝ) • (∑i, directionalDerivative (frameVectors α β i) *
        directionalDerivative (frameVectors α β i)) -
      (∑i, multiplication (g i) * directionalDerivative (frameVectors α β i)) +
      multiplication (frameScalar g V α β) := by
  simp only [directionalDiffusion, directional_square_expanded, frameScalar,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
    multiplication_smul, multiplication_sub, multiplication_sum,
    smul_add, smul_sub, smul_smul]
  norm_num
  module

def frameSecondNormal (α β : ℝ) : NormalForm :=
  Finsupp.single (Finsupp.single 0 2) ((1/2 : ℝ) • smoothOne) +
  Finsupp.single (Finsupp.single 1 2) ((1/2 : ℝ) • smoothOne) +
  Finsupp.single (Finsupp.single 2 2) (((1+α^2+β^2)/2) • smoothOne) +
  Finsupp.single (Finsupp.single 0 1 + Finsupp.single 2 1) (α • smoothOne) +
  Finsupp.single (Finsupp.single 1 1 + Finsupp.single 2 1) (β • smoothOne)

def frameDiffusionNormal (α β : ℝ) (g : Fin 3 → Smooth) (V : Smooth) : NormalForm :=
  frameSecondNormal α β - Finsupp.single (Finsupp.single 0 1) (g 0) -
    Finsupp.single (Finsupp.single 1 1) (g 1) -
    Finsupp.single (Finsupp.single 2 1) (α • g 0 + β • g 1 + g 2) +
    Finsupp.single 0 (frameScalar g V α β)

theorem normalAction_frameSecondNormal (α β : ℝ) :
    normalAction (frameSecondNormal α β) =
      (1/2 : ℝ) • (∑i, directionalDerivative (frameVectors α β i) *
        directionalDerivative (frameVectors α β i)) := by
  simp only [frameSecondNormal, map_add, normalAction_single, multiplication_smul,
    multiplication_smoothOne, smul_mul_assoc, one_mul]
  simp only [multiPartial, Finsupp.add_apply, Finsupp.single_apply]
  norm_num
  simp only [Fin.sum_univ_three, frameVectors_zero,frameVectors_one,frameVectors_two,
    directionalDerivative_add,
    directionalDerivative_smul, coordinate_directionalDerivative]
  apply LinearMap.ext
  intro u
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    map_add, map_smul, pow_two]
  have h₀ := partialDerivative_commute_apply 0 2 u
  have h₁ := partialDerivative_commute_apply 1 2 u
  rw [h₀, h₁]
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem normalAction_frameDiffusionNormal (α β : ℝ) (g : Fin 3 → Smooth) (V : Smooth) :
    normalAction (frameDiffusionNormal α β g V) = directionalDiffusion α β g V := by
  rw [directionalDiffusion_expanded]
  simp only [frameDiffusionNormal, map_add, map_sub, normalAction_frameSecondNormal,
    normalAction_single, normalAction_scalar, normalAction_partial]
  simp only [multiPartial, Finsupp.single_apply]
  norm_num
  simp only [Fin.sum_univ_three, frameVectors_zero,frameVectors_one,frameVectors_two,
    directionalDerivative_add,
    directionalDerivative_smul, coordinate_directionalDerivative,
    multiplication_add, multiplication_smul]
  apply LinearMap.ext
  intro u
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, multiplication_apply, map_add, map_smul]
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smoothMul_apply, smul_eq_mul]
  ring

@[simp] theorem frameDiffusionNormal_hidden_first (α β : ℝ)
    (g : Fin 3 → Smooth) (V : Smooth) :
    frameDiffusionNormal α β g V (Finsupp.single 2 1) =
      -(α • g 0 + β • g 1 + g 2) := by
  classical
  have h₀ : (Finsupp.single 0 2 : MultiIndex) ≠ Finsupp.single 2 1 := by
    intro he
    have hh := congrArg (fun γ : MultiIndex => γ 0) he
    norm_num [Finsupp.single_apply] at hh
  have h₁ : (Finsupp.single 1 2 : MultiIndex) ≠ Finsupp.single 2 1 := by
    intro he
    have hh := congrArg (fun γ : MultiIndex => γ 1) he
    norm_num [Finsupp.single_apply] at hh
  have h₂ : (Finsupp.single 2 2 : MultiIndex) ≠ Finsupp.single 2 1 := by
    intro he
    have hh := congrArg (fun γ : MultiIndex => γ 2) he
    norm_num [Finsupp.single_apply] at hh
  have h₃ : (Finsupp.single 0 1 + Finsupp.single 2 1 : MultiIndex) ≠ Finsupp.single 2 1 := by
    intro he
    have hh := congrArg (fun γ : MultiIndex => γ 0) he
    norm_num [Finsupp.single_apply] at hh
  have h₄ : (Finsupp.single 1 1 + Finsupp.single 2 1 : MultiIndex) ≠ Finsupp.single 2 1 := by
    intro he
    have hh := congrArg (fun γ : MultiIndex => γ 1) he
    norm_num [Finsupp.single_apply] at hh
  have h₅ : (Finsupp.single 0 1 : MultiIndex) ≠ Finsupp.single 2 1 := by
    intro he
    have hh := congrArg (fun γ : MultiIndex => γ 0) he
    norm_num [Finsupp.single_apply] at hh
  have h₆ : (Finsupp.single 1 1 : MultiIndex) ≠ Finsupp.single 2 1 := by
    intro he
    have hh := congrArg (fun γ : MultiIndex => γ 1) he
    norm_num [Finsupp.single_apply] at hh
  have h₇ : (0 : MultiIndex) ≠ Finsupp.single 2 1 := by
    intro he
    have hh := congrArg (fun γ : MultiIndex => γ 2) he
    norm_num [Finsupp.single_apply] at hh
  simp [frameDiffusionNormal, frameSecondNormal, Finsupp.single_apply,
    h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇]

end Wong.SmoothModel


/-! Source segment: CanonicalGaugeData -/

/-! Complete transport of the original model to its canonical triangular
drift. The transformed Lie algebra is the true image of the original E. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem triangularDrift_hidden_visible_partial_zero (p : Wong.AffineParameters)
    (i : Fin 3) (hi : i ≠ 2) : partialDerivative 2 (triangularDrift p i) = 0 := by
  rw [triangularDrift, partialDerivative_polynomialSmooth]
  fin_cases i <;> simp_all [triangularDriftPolynomials]

theorem triangularDrift_hidden_second_partial_zero (p : Wong.AffineParameters) :
    (partialDerivative 2 ^ 2) (triangularDrift p 2) = 0 := by
  change partialDerivative 2 (partialDerivative 2 (triangularDrift p 2)) = 0
  rw [triangularDrift, partialDerivative_polynomialSmooth,
    partialDerivative_polynomialSmooth]
  simp [triangularDriftPolynomials]

structure CanonicalGaugeData {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) where
  Λ : Smooth
  drift_eq : gaugeDrift Λ f = triangularDrift p
  finiteDimensional : FiniteDimensional ℝ (gaugeAlgebra Λ (estimationAlgebra f h))
  finiteOrder : gaugeAlgebra Λ (estimationAlgebra f h) ≤ finiteOrderAlgebra
  normalForm : gaugeAlgebra Λ (estimationAlgebra f h) ≤ normalFormOperators
  functionSpace : AdaptedFunctionSpace (gaugeAlgebra Λ (estimationAlgebra f h))
  filtering_mem : filteringOperator (triangularDrift p) (eta f h) ∈
    gaugeAlgebra Λ (estimationAlgebra f h)
  D_zero_mem : D (triangularDrift p) 0 ∈ gaugeAlgebra Λ (estimationAlgebra f h)
  D_one_mem : D (triangularDrift p) 1 ∈ gaugeAlgebra Λ (estimationAlgebra f h)
  wong_eq : ∀ i j x, (wong (triangularDrift p) i j).1 x = p.matrix x i j

theorem exists_canonicalGaugeData {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    Nonempty (CanonicalGaugeData f h p) := by
  obtain ⟨Λ, hΛ⟩ := exists_triangular_gauge f p hform
  have hL : filteringOperator f (eta f h) ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  refine ⟨{
    Λ := Λ
    drift_eq := hΛ
    finiteDimensional := gaugeAlgebra_finiteDimensional Λ _
    finiteOrder := gaugeAlgebra_le_finiteOrder Λ _ (estimationAlgebra_le_finiteOrder f h)
    normalForm := gaugeAlgebra_le_normalFormOperators Λ _
      (estimationAlgebra_le_normalFormOperators f h)
    functionSpace := adaptedFunctionSpace_gauge Λ _
      (adaptedFunctionSpace_estimation f h hrank hq hx₀ hx₁)
    filtering_mem := by
      simpa only [hΛ] using filteringOperator_mem_gaugeAlgebra Λ _ f (eta f h) hL
    D_zero_mem := by
      simpa only [hΛ] using D_mem_gaugeAlgebra Λ _ f 0 (D_mem_of_coordinate_mem f h 0 hx₀)
    D_one_mem := by
      simpa only [hΛ] using D_mem_gaugeAlgebra Λ _ f 1 (D_mem_of_coordinate_mem f h 1 hx₁)
    wong_eq := by
      intro i j x
      rw [← hΛ, wong_gaugeDrift]
      exact hform i j x
  }⟩

end Wong.SmoothModel


/-! Source segment: HiddenPolynomialProfiles -/

/-! A genuine smooth slanted hidden profile is polynomial whenever its
actual hidden derivative is nilpotent. The Euler premise is discharged by
the actual finite-dimensional Lie algebra theorem. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem polynomial_slanted_hidden_profile_of_nilpotent (u : Smooth) (α β δ : ℝ)
    (h₀ : directionalDerivative (coordinateVector 0 + α • coordinateVector 2) u = 0)
    (h₁ : directionalDerivative (coordinateVector 1 + β • coordinateVector 2) u = 0)
    (n : ℕ) (hn : (partialDerivative 2 ^ (n+1)) u = 0) :
    ∃ p : Polynomial ℝ, ∀ x : State,
      u.1 x = p.eval (x 2 - α * x 0 - β * x 1 - δ) := by
  obtain ⟨ρ, _hρ, hu⟩ := exists_slanted_hidden_profile u α β δ h₀ h₁
  have hz : iteratedDeriv (n+1) (coordinateSlice u 0 2) = 0 := by
    rw [iteratedDeriv_coordinateSlice, hn]
    rfl
  obtain ⟨q, _hq, he⟩ := Wong.FunctionElements.polynomial_of_iteratedDeriv_eq_zero
    n (coordinateSlice u 0 2) (coordinateSlice_smooth u 0 2) hz
  let p := q.comp (Polynomial.X + Polynomial.C δ)
  have hp (t : ℝ) : p.eval t = ρ t := by
    simp only [p, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, he]
    rw [coordinateSlice, hu]
    simp
  exact ⟨p, fun x => (hu x).trans (hp _).symm⟩

def hiddenFirstOrderNormal (u : Smooth) : NormalForm :=
  Finsupp.single (Finsupp.single 2 1) smoothOne + Finsupp.single 0 u

@[simp] theorem normalAction_hiddenFirstOrderNormal (u : Smooth) :
    normalAction (hiddenFirstOrderNormal u) = partialDerivative 2 + multiplication u := by
  simp [hiddenFirstOrderNormal]

@[simp] theorem hiddenFirstOrderNormal_zero (u : Smooth) :
    hiddenFirstOrderNormal u 0 = u := by
  have he : (Finsupp.single 2 1 : MultiIndex) ≠ 0 := by
    intro hh
    have h := congrArg (fun α : MultiIndex => α 2) hh
    simp at h
  simp [hiddenFirstOrderNormal, he]

theorem finiteEuler_hidden_firstOrder_scalar_nilpotence
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E) (u : Smooth)
    (hP : partialDerivative 2 + multiplication u ∈ E) :
    ∃ n : ℕ, (partialDerivative 2 ^ n) u = 0 := by
  obtain ⟨n, hn⟩ := finiteOrderLieAlgebra_uniform_hidden_nilpotence E hfinite B hB hJ
  have hp : normalAction (hiddenFirstOrderNormal u) ∈ E := by
    simpa using hP
  exact ⟨n, by simpa using hn _ hp 0⟩

end Wong.SmoothModel


/-! Source segment: EulerNormalDecomposition -/

/-! The actual Euler decomposition retains both the faithful normal form and
its polynomial in adH. Membership is proved using adJ, the element of E. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open Polynomial

theorem normalHiddenEuler_polynomial_coefficient (Q : Polynomial ℝ)
    (p : NormalForm) (α : MultiIndex) :
    ((aeval normalHiddenEuler Q) p) α =
      (aeval (shiftedHiddenEuler α) Q) (p α) :=
  Wong.EulerFiniteModule.aeval_intertwiner normalHiddenEuler (shiftedHiddenEuler α)
    (Finsupp.lapply α) (fun q => normalHiddenEuler_apply q α) Q p

theorem normalHiddenEuler_polynomial_action (Q : Polynomial ℝ) (p : NormalForm) :
    normalAction ((aeval normalHiddenEuler Q) p) =
      (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) (normalAction p) :=
  Wong.EulerFiniteModule.aeval_intertwiner normalHiddenEuler
    (LieAlgebra.ad ℝ Operator hiddenEuler) normalAction
    (fun q => normalAction_hiddenEuler q) Q p

theorem finiteEuler_normal_decomposition
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (p : NormalForm) (hp : normalAction p ∈ E) :
    ∃ s : Finset ℤ, ∃ Q : ℤ → Polynomial ℝ,
      (∑w∈s, (aeval normalHiddenEuler (Q w)) p) = p ∧
      ∀ w∈s,
        normalHiddenEuler ((aeval normalHiddenEuler (Q w)) p) =
          (w : ℝ) • ((aeval normalHiddenEuler (Q w)) p) ∧
        normalAction ((aeval normalHiddenEuler (Q w)) p) ∈ E := by
  obtain ⟨n, hn⟩ := finiteOrderLieAlgebra_uniform_hidden_nilpotence E hfinite B hB hJ
  obtain ⟨s, hs⟩ := normalEuler_integer_annihilator p n (hn p hp)
  have hann : (aeval normalHiddenEuler (integerWeightPolynomial s)) p = 0 := by
    apply normalAction_injective
    rw [normalHiddenEuler_polynomial_action, hs, map_zero]
  obtain ⟨Q, hsum, heigen⟩ := Wong.EulerSpectral.integer_spectral_decomposition
    normalHiddenEuler s p hann
  let v : ℤ → Operator := fun w => normalAction ((aeval normalHiddenEuler (Q w)) p)
  have hsumv : (∑w∈s,v w) = normalAction p := by
    rw [← hsum, map_sum]
  have heigenv (w : ℤ) (hw : w∈s) : ⁅hiddenEuler,v w⁆ = (w : ℝ) • v w := by
    rw [← normalAction_hiddenEuler, heigen w hw, map_smul]
  have hvfinite (w : ℤ) (_hw : w∈s) : v w ∈ finiteOrderAlgebra := by
    rw [show v w = (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) (Q w))
      (normalAction p) from normalHiddenEuler_polynomial_action _ _]
    exact hiddenEuler_polynomial_mem_finiteOrderAlgebra (Q w) _ (hfinite hp)
  refine ⟨s,Q,hsum,?_⟩
  intro w hw
  refine ⟨heigen w hw, ?_⟩
  have hmem : (∑w∈s,v w) ∈ E := by rw [hsumv]; exact hp
  obtain ⟨_R, _hR, hE⟩ := actual_euler_weight_projection E B hB hJ s v
    heigenv hvfinite hmem w hw
  exact hE

end Wong.SmoothModel


/-! Source segment: EulerProjectionCalculus -/

/-! Actual Euler projections can prescribe their values at finitely many
known differential weights. This identifies the differential part without
expanding the scalar potential into Taylor coefficients. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open Polynomial
set_option maxHeartbeats 1000000

theorem aeval_end_eigenvalue {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (u : V) (c : ℝ) (hu : A u = c • u)
    (Q : Polynomial ℝ) : (aeval A Q) u = Q.eval c • u := by
  have hp (n : ℕ) : (A^n) u = c^n • u := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change A ((A^n) u) = _
      rw [ih, map_smul, hu, smul_smul, pow_succ]
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      hp, smul_smul, eval_monomial]

theorem integer_linear_polynomial_coprime (i j : ℤ) (hij : i ≠ j) :
    IsCoprime (X - C (i : ℝ)) (X - C (j : ℝ)) := by
  apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
  apply isUnit_iff_ne_zero.mpr
  apply sub_ne_zero.mpr
  exact_mod_cast hij

theorem shiftedHiddenEuler_eigenvalue (α : MultiIndex) (u : Smooth) (c : ℝ)
    (hu : hiddenEuler u = c • u) : shiftedHiddenEuler α u = (c-(α 2:ℝ)) • u := by
  simp only [shiftedHiddenEuler, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, hu]
  module

theorem shiftedHiddenEuler_polynomial_eigenvalue (α : MultiIndex) (u : Smooth) (c : ℝ)
    (hu : hiddenEuler u = c • u) (Q : Polynomial ℝ) :
    (aeval (shiftedHiddenEuler α) Q) u = Q.eval (c-(α 2:ℝ)) • u :=
  aeval_end_eigenvalue _ _ _ (shiftedHiddenEuler_eigenvalue α u c hu) Q

theorem shiftedHiddenEuler_polynomial_zero_of_nilpotent (α : MultiIndex) (u : Smooth)
    (n : ℕ) (hu : (partialDerivative 2 ^ n) u = 0) (Q : Polynomial ℝ)
    (hQ : ∀ k<n, Q.eval ((k:ℝ)-(α 2:ℝ)) = 0) :
    (aeval (shiftedHiddenEuler α) Q) u = 0 := by
  classical
  have hdiv : eulerWeightBlock n (α 2) ∣ Q := by
    apply Finset.prod_dvd_of_coprime
    · intro i _hi j _hj hij
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      apply isUnit_iff_ne_zero.mpr
      apply sub_ne_zero.mpr
      intro he
      apply hij
      have hh : (i:ℝ) = j := by linarith
      exact_mod_cast hh
    · intro k hk
      exact Polynomial.dvd_iff_isRoot.mpr (hQ k (Finset.mem_range.mp hk))
  have he := Wong.EulerAlgebra.aeval_apply_eq_of_dvd_sub (shiftedHiddenEuler α)
    Q 0 (eulerWeightBlock n (α 2)) u (eulerWeightBlock_annihilates n α u hu)
    (by simpa only [sub_zero] using hdiv)
  simpa using he

theorem actual_euler_projection_with_prescribed_weights
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (hnormal : E ≤ normalFormOperators)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (P : Operator) (hP : P ∈ E) (w : ℤ) (K : Finset ℤ) :
    ∃ Q : Polynomial ℝ,
      (∀ j∈K, Q.eval (j : ℝ) = if j=w then 1 else 0) ∧
      (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) P ∈ E ∧
      ⁅hiddenEuler,(aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) P⁆ =
        (w : ℝ) • ((aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) P) := by
  classical
  obtain ⟨s,v,hsum,hv⟩ := finiteOrderLieAlgebra_finite_euler_decomposition
    E hfinite hnormal B hB hJ P hP
  let t := insert w (s ∪ K)
  obtain ⟨Q,hQ⟩ := Wong.EulerAlgebra.exists_coprime_projection t w
    (fun j => X-C (j:ℝ)) (fun j _hj hjw => integer_linear_polynomial_coprime w j hjw.symm)
  have heval (j : ℤ) (hj : j∈t) : Q.eval (j:ℝ) = if j=w then 1 else 0 := by
    have hd := Polynomial.dvd_iff_isRoot.mp (hQ j hj)
    apply sub_eq_zero.mp
    by_cases hjw : j=w <;> simpa [Polynomial.IsRoot,hjw] using hd
  have hs (j : ℤ) (hj : j∈s) : j∈t := Finset.mem_insert_of_mem (Finset.mem_union_left K hj)
  have hk (j : ℤ) (hj : j∈K) : j∈t := Finset.mem_insert_of_mem (Finset.mem_union_right s hj)
  have heach (j : ℤ) (hj : j∈s) :
      (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) (v j) =
        if j=w then v j else 0 := by
    rw [aeval_end_eigenvalue _ _ _ (hv j hj).1 Q, heval j (hs j hj)]
    split_ifs <;> simp
  have hpart : (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) P =
      if w∈s then v w else 0 := by
    rw [← hsum, map_sum]
    calc
      _ = ∑j∈s, if j=w then v j else 0 := Finset.sum_congr rfl heach
      _ = _ := by simp
  refine ⟨Q,fun j hj => heval j (hk j hj), ?_, ?_⟩
  · rw [hpart]
    split_ifs with hw
    · exact (hv w hw).2.choose_spec.2
    · exact E.zero_mem
  · rw [hpart]
    split_ifs with hw
    · exact (hv w hw).1
    · simp

theorem hiddenEuler_kernel_partial_zero (u : Smooth) (hu : hiddenEuler u = 0) :
    partialDerivative 2 u = 0 := by
  apply positive_hiddenEuler_shift_kernel 1 (by norm_num)
  have hz := congrArg (partialDerivative 2) hu
  rw [partial_hiddenEuler_apply, map_zero] at hz
  simpa only [LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, one_smul] using hz

theorem actual_normal_euler_projection_with_prescribed_weights
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (hnormal : E ≤ normalFormOperators)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (p : NormalForm) (hp : normalAction p ∈ E)
    (n : ℕ) (hdeg : NormalDegreeLE n p) (w : ℤ) (K : Finset ℤ) :
    ∃ Q : Polynomial ℝ,
      (∀ j∈K, Q.eval (j : ℝ) = if j=w then 1 else 0) ∧
      normalAction ((aeval normalHiddenEuler Q) p) ∈ E ∧
      normalHiddenEuler ((aeval normalHiddenEuler Q) p) =
        (w:ℝ) • ((aeval normalHiddenEuler Q) p) ∧
      NormalDegreeLE n ((aeval normalHiddenEuler Q) p) := by
  obtain ⟨Q,hval,hmem,heig⟩ := actual_euler_projection_with_prescribed_weights
    E hfinite hnormal B hB hJ (normalAction p) hp w K
  refine ⟨Q,hval,?_,?_,?_⟩
  · rwa [normalHiddenEuler_polynomial_action]
  · apply normalAction_injective
    rw [normalAction_hiddenEuler, map_smul, normalHiddenEuler_polynomial_action]
    exact heig
  · intro α hα
    rw [normalHiddenEuler_polynomial_coefficient, hdeg α hα, map_zero]

theorem normal_euler_eigen_coefficient (p : NormalForm) (w : ℤ)
    (hp : normalHiddenEuler p = (w:ℝ) • p) (α : MultiIndex) :
    hiddenEuler (p α) = ((w:ℝ)+(α 2:ℝ)) • p α := by
  have hh := congrArg (fun q : NormalForm => q α) hp
  rw [normalHiddenEuler_apply, Finsupp.smul_apply] at hh
  change hiddenEuler (p α) - (α 2:ℝ) • p α = (w:ℝ) • p α at hh
  calc
    hiddenEuler (p α) = (w:ℝ) • p α + (α 2:ℝ) • p α := sub_eq_iff_eq_add.mp hh
    _ = _ := (add_smul _ _ _).symm

theorem normal_euler_zero_weight_scalar_hidden_independent (p : NormalForm)
    (hp : normalHiddenEuler p = 0) : partialDerivative 2 (p 0) = 0 := by
  have he : normalHiddenEuler p = ((0:ℤ):ℝ) • p := by simpa using hp
  have hu := normal_euler_eigen_coefficient p 0 he 0
  simp only [Int.cast_zero, Finsupp.zero_apply, Nat.cast_zero, add_zero, zero_smul] at hu
  exact hiddenEuler_kernel_partial_zero _ hu

end Wong.SmoothModel


/-! Source segment: ConstancyReduction -/

/-! Exact reductions of the original main proposition. These do not assert
the missing finite-dimensional-to-zero-slope implication. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem wongConstant_of_affine_zero_slopes (f : Fin 3 → Smooth)
    (p : Wong.AffineParameters) (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hs : p.ZeroSlopes) : WongConstant f := by
  have hc := (Wong.affine_constancy_iff_zero_slopes p).mpr hs
  refine ⟨p.matrix 0, ?_⟩
  intro i j x
  rw [hform]
  exact congrArg (fun A => A i j) (hc x 0)

theorem wongConstant_of_independent_affine_slopes_zero (f : Fin 3 → Smooth)
    (p : Wong.AffineParameters) (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0)
    (hk₁ : p.k₁ = 0) (hk₂ : p.k₂ = 0) (hk₃ : p.k₃ = 0)
    (hh₂ : p.h₂ = 0) (hh₃ : p.h₃ = 0) : WongConstant f := by
  have hh₁ := (affineWong_bianchi_parameters f p hform).trans hk₂
  exact wongConstant_of_affine_zero_slopes f p hform
    ⟨hb₁, hb₂, hk₁, hk₂, hk₃, hh₁, hh₂, hh₃⟩

def AdaptedConstancyClaim : Prop :=
  ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    QuadraticFree (estimationAlgebra f h) →
    multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h →
    multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h →
    WongConstant f

theorem mainClaim_iff_adaptedConstancyClaim : mainClaim ↔ AdaptedConstancyClaim := by
  constructor
  · intro H m f h hFD hrank hq _hx₀ _hx₁
    exact H m f h hFD hrank hq
  · intro H m f h hFD hrank hq
    letI := hFD
    obtain ⟨e, _he, hFD', hrank', hq', hx₀, hx₁, hconst⟩ :=
      estimationAlgebra_adapted_coordinates f h hrank hq
    exact hconst.mp (H m (coordinateDrift e f) (coordinateObservations e h)
      hFD' hrank' hq' hx₀ hx₁)

end Wong.SmoothModel


/-! Source segment: PublishedModelEquivalence -/

/-! The actual covariant filtering generator equals the expanded generator in Shi–Yau 2017. -/

noncomputable section
namespace Wong.SmoothModel

theorem D_square_expanded (f : Fin 3 → Smooth) (i : Fin 3) :
    D f i * D f i = partialDerivative i * partialDerivative i -
      (2 : ℝ) • (multiplication (f i) * partialDerivative i) -
      multiplication (partialDerivative i (f i)) +
      multiplication (smoothMul (f i) (f i)) := by
  apply LinearMap.ext
  intro u
  change partialDerivative i (partialDerivative i u - smoothMul (f i) u) -
    smoothMul (f i) (partialDerivative i u - smoothMul (f i) u) = _
  rw [map_sub, partialDerivative_smoothMul]
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, multiplication_apply, smoothMul_apply,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

def publishedExpandedL0 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) : Operator :=
  (1 / 2 : ℝ) • (∑ i, partialDerivative i * partialDerivative i) -
    (∑ i, multiplication (f i) * partialDerivative i) -
    multiplication (∑ i, partialDerivative i (f i)) -
    (1 / 2 : ℝ) • multiplication (∑ j, smoothMul (h j) (h j))

theorem L0_eq_publishedExpandedL0 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    L0 f h = publishedExpandedL0 f h := by
  simp only [L0, publishedExpandedL0, D_square_expanded, eta,
    multiplication_add, multiplication_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.smul_sum, smul_add, smul_sub, smul_smul]
  norm_num
  module

end Wong.SmoothModel


/-! Source segment: SmoothPolynomialEvaluation -/

/-! Polynomial evaluation takes values in the original ring of globally
smooth real functions. Every derivative below is the actual derivative. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
set_option maxHeartbeats 1000000

 theorem smooth_polynomial_eval_apply (p : Polynomial ℝ) (u : Smooth) (x : State) :
    ((Polynomial.aeval u) p).1 x = p.eval (u.1 x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,Submodule.coe_add,Pi.add_apply,Polynomial.eval_add,hp,hq]
  | monomial n a =>
    simp [Polynomial.aeval_monomial,Polynomial.eval_monomial,
      Algebra.algebraMap_eq_smul_one,Submodule.coe_smul,Pi.smul_apply,
      smul_eq_mul]

theorem smooth_polynomial_eval_partial (p : Polynomial ℝ) (u : Smooth)
    (hu : partialDerivative 2 u = smoothOne) :
    partialDerivative 2 ((Polynomial.aeval u) p) =
      (Polynomial.aeval u) p.derivative := by
  have he := (smoothPartialDerivation 2).map_aeval p u
  simpa only [smoothPartialDerivation_apply,hu,smoothOne_eq_one,
    smul_eq_mul,mul_one] using he

theorem smooth_polynomial_eval_partial_pow (p : Polynomial ℝ) (u : Smooth)
    (hu : partialDerivative 2 u = smoothOne) (n : ℕ) :
    (partialDerivative 2 ^ n) ((Polynomial.aeval u) p) =
      (Polynomial.aeval u) (Polynomial.derivative^[n] p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Module.End.mul_apply,smooth_polynomial_eval_partial p u hu,ih]
    rw [Function.iterate_succ_apply]

theorem polynomial_iterated_derivative_top (p : Polynomial ℝ) :
    Polynomial.derivative^[p.natDegree] p =
      Polynomial.C (p.natDegree.factorial • p.leadingCoeff) := by
  have hd : (Polynomial.derivative^[p.natDegree] p).natDegree ≤ 0 := by
    simpa only [Nat.sub_self] using Polynomial.natDegree_iterate_derivative p p.natDegree
  rw [Polynomial.eq_C_of_natDegree_le_zero hd]
  congr 1
  simpa only [zero_add,Nat.descFactorial_self,Polynomial.leadingCoeff]
    using Polynomial.coeff_iterate_derivative p 0

theorem smooth_polynomial_top_derivative (p : Polynomial ℝ) (u : Smooth)
    (hu : partialDerivative 2 u = smoothOne) :
    (partialDerivative 2 ^ p.natDegree) ((Polynomial.aeval u) p) =
      (p.natDegree.factorial • p.leadingCoeff) • smoothOne := by
  rw [smooth_polynomial_eval_partial_pow p u hu,
    polynomial_iterated_derivative_top,Polynomial.aeval_C]
  exact Algebra.algebraMap_eq_smul_one _

def slantedHiddenCoordinate (α β δ : ℝ) : Smooth :=
  hiddenAffineCoordinate (-α) (-β) (-δ)

@[simp] theorem slantedHiddenCoordinate_apply (α β δ : ℝ) (x : State) :
    (slantedHiddenCoordinate α β δ).1 x = x 2 - α*x 0 - β*x 1 - δ := by
  simp [slantedHiddenCoordinate,hiddenAffineCoordinate,linearFunction,
    Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    coordinateVector,Fin.sum_univ_three,smoothOne]
  ring

@[simp] theorem partial_slantedHiddenCoordinate (α β δ : ℝ) :
    partialDerivative 2 (slantedHiddenCoordinate α β δ) = smoothOne := by
  simp [slantedHiddenCoordinate,hiddenAffineCoordinate,partialDerivative_linearFunction,
    partialDerivative_const,actual_partialDerivative_one,coordinateVector]

theorem smooth_eq_slanted_polynomial (u : Smooth) (p : Polynomial ℝ) (α β δ : ℝ)
    (hu : ∀ x : State, u.1 x = p.eval (x 2 - α*x 0 - β*x 1 - δ)) :
    u = (Polynomial.aeval (slantedHiddenCoordinate α β δ)) p := by
  apply Subtype.ext
  funext x
  rw [smooth_polynomial_eval_apply,slantedHiddenCoordinate_apply,hu]

theorem slanted_polynomial_leading_remainder_nilpotent
    (p : Polynomial ℝ) (α β δ : ℝ) :
    (partialDerivative 2 ^ p.natDegree)
      ((Polynomial.aeval (slantedHiddenCoordinate α β δ)) p -
        p.leadingCoeff • linearFunction (coordinateVector 2) ^ p.natDegree) = 0 := by
  have ht : partialDerivative 2 (linearFunction (coordinateVector 2)) = smoothOne := by
    simp [partialDerivative_linearFunction,coordinateVector]
  have hm : p.leadingCoeff • linearFunction (coordinateVector 2) ^ p.natDegree =
      (Polynomial.aeval (linearFunction (coordinateVector 2)))
        (Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree) := by
    simp [Algebra.algebraMap_eq_smul_one,smul_mul_assoc]
  rw [map_sub,smooth_polynomial_top_derivative p _ (partial_slantedHiddenCoordinate α β δ),hm]
  have hn := smooth_polynomial_eval_partial_pow
    (Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree)
    (linearFunction (coordinateVector 2)) ht p.natDegree
  rw [hn,Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul]
  simp [Nat.descFactorial_self,Algebra.algebraMap_eq_smul_one,smul_eq_mul,
    nsmul_eq_mul,mul_comm]
  apply Subtype.ext
  funext x
  simp [Algebra.algebraMap_eq_smul_one,Submodule.coe_sub,Submodule.coe_smul,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul,smooth_coe_natCast]
  <;> ring

end Wong.SmoothModel


/-! Source segment: SmoothPolynomialGradient -/

/-! Polynomiality of the actual gradient implies polynomiality of its
smooth potential, using genuine coordinate derivative nilpotence. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
set_option maxHeartbeats 1000000
open MvPolynomial

theorem polynomial_partial_pow_monomial_zero (i : Fin 3) (α : MultiIndex)
    (a : ℝ) (n : ℕ) (hn : α i < n) :
    ((pderiv i).toLinearMap ^ n) (monomial α a) = 0 := by
  induction n generalizing α a with
  | zero => omega
  | succ n ih =>
    rw [pow_succ,Module.End.mul_apply]
    change ((pderiv i).toLinearMap ^ n) (pderiv i (monomial α a)) = 0
    rw [pderiv_monomial]
    by_cases hz : α i = 0
    · simp [hz]
    · apply ih
      simp only [Finsupp.tsub_apply,Finsupp.single_eq_same]
      omega

theorem polynomial_partial_pow_zero_of_totalDegree (p : RealPoly) (i : Fin 3)
    (n : ℕ) (hn : p.totalDegree < n) :
    ((pderiv i).toLinearMap ^ n) p = 0 := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro α hα
  apply polynomial_partial_pow_monomial_zero
  have hd : α.degree ≤ p.totalDegree := le_totalDegree hα
  have hs : α.degree = α 0 + α 1 + α 2 := by
    rw [Finsupp.degree_eq_sum,Fin.sum_univ_three]
  fin_cases i
  · change α 0 < n
    omega
  · change α 1 < n
    omega
  · change α 2 < n
    omega

theorem partial_pow_polynomialSmooth (p : RealPoly) (i : Fin 3) (n : ℕ) :
    (partialDerivative i ^ n) (polynomialSmooth p) =
      polynomialSmooth (((pderiv i).toLinearMap ^ n) p) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ,Module.End.mul_apply,Module.End.mul_apply,
      partialDerivative_polynomialSmooth,ih]
    rfl

theorem polynomialSmooth_partial_pow_zero (p : RealPoly) (i : Fin 3) (n : ℕ)
    (hn : p.totalDegree < n) :
    (partialDerivative i ^ n) (polynomialSmooth p) = 0 := by
  rw [partial_pow_polynomialSmooth,polynomial_partial_pow_zero_of_totalDegree p i n hn,
    polynomialSmooth_zero]

theorem polynomial_of_polynomial_gradient (u : Smooth)
    (hu : ∀ i : Fin 3, ∃ p : RealPoly, partialDerivative i u = polynomialSmooth p) :
    ∃ p : RealPoly, u = polynomialSmooth p := by
  classical
  choose p hp using hu
  let N := (Finset.univ : Finset (Fin 3)).sup (fun i => (p i).totalDegree)
  have hd (i : Fin 3) : (p i).totalDegree ≤ N :=
    Finset.le_sup (f:=fun j => (p j).totalDegree) (Finset.mem_univ i)
  have hz (i : Fin 3) : (partialDerivative i ^ ((N+1)+1)) u = 0 := by
    rw [pow_succ,Module.End.mul_apply,hp i]
    exact polynomialSmooth_partial_pow_zero (p i) i (N+1) (by have := hd i; omega)
  obtain ⟨q,_hq,hq⟩ := polynomial_of_partial_nilpotent (N+1) u hz
  refine ⟨q,?_⟩
  apply Subtype.ext
  funext x
  exact (hq x).symm

end Wong.SmoothModel


/-! Source segment: EulerGaugePolynomial -/

/-! Polynomiality of the normalizing gauge follows from the normal form of
 the actual diffusion generator; no hidden covariant derivative membership
 is assumed. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem hidden_power_zero_of_first (u : Smooth) (hu : partialDerivative 2 u = 0)
    (n : ℕ) : (partialDerivative 2 ^ (n+1)) u = 0 := by
  rw [pow_succ, Module.End.mul_apply, hu, map_zero]

theorem hidden_power_zero_of_second (u : Smooth)
    (hu : (partialDerivative 2 ^ 2) u = 0) (n : ℕ) :
    (partialDerivative 2 ^ (n+2)) u = 0 := by
  rw [pow_add, Module.End.mul_apply, hu, map_zero]

theorem normalized_frameDrift_visible_independent
    (E : LieSubalgebra ℝ Operator) (f : Fin 3 → Smooth)
    (α β δ : ℝ) (Λ B : Smooth)
    (hfun : AdaptedFunctionSpace (hiddenFrameAlgebra α β δ Λ E))
    (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ hiddenFrameAlgebra α β δ Λ E)
    (hD₀ : D f 0 ∈ E) (hD₁ : D f 1 ∈ E) :
    partialDerivative 2 (frameDrift f α β δ Λ 0) = 0 ∧
    partialDerivative 2 (frameDrift f α β δ Λ 1) = 0 := by
  obtain ⟨he₀, he₁⟩ := hiddenShear_symm_visible_vectors α β
  have hz (i : Fin 3) (hi : i ≠ 2) (a : ℝ)
      (he : (hiddenShear α β).symm (coordinateVector i) =
        coordinateVector i + a • coordinateVector 2)
      (hD : D f i ∈ E) :
      partialDerivative 2 (hiddenAffinePullback α β δ (f i) +
        (partialDerivative i + a • partialDerivative 2) Λ) = 0 := by
    have hmem := hiddenFrame_image_mem α β δ Λ E (D f i) hD
    rw [hiddenFrame_D, he, directionalDerivative_add, directionalDerivative_smul,
      coordinate_directionalDerivative, coordinate_directionalDerivative] at hmem
    have hu := adapted_firstOrder_hidden_independent _ hfun B
      (-(hiddenAffinePullback α β δ (f i) +
        (partialDerivative i + a • partialDerivative 2) Λ)) hB hJ i hi a hmem
    simpa only [map_neg, neg_eq_zero] using hu
  constructor
  · simpa only [frameDrift, frameVectors, Matrix.cons_val_zero,
      directionalDerivative_add, directionalDerivative_smul,
      coordinate_directionalDerivative, LinearMap.add_apply,
      LinearMap.smul_apply] using hz 0 (by decide) α he₀ hD₀
  · simpa only [frameDrift, frameVectors, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.vecHead, Matrix.vecTail,
      directionalDerivative_add, directionalDerivative_smul,
      coordinate_directionalDerivative, LinearMap.add_apply,
      LinearMap.smul_apply] using hz 1 (by decide) β he₁ hD₁

theorem polynomial_slanted_profile_of_representation_nilpotent
    (u : Smooth) (α β δ : ℝ) (ρ : ℝ → ℝ)
    (hu : ∀ x : State, u.1 x = ρ (x 2 - α*x 0 - β*x 1 - δ))
    (n : ℕ) (hn : (partialDerivative 2 ^ (n+1)) u = 0) :
    ∃ p : Polynomial ℝ, ∀ x : State,
      u.1 x = p.eval (x 2 - α*x 0 - β*x 1 - δ) := by
  have hz : iteratedDeriv (n+1) (coordinateSlice u 0 2) = 0 := by
    rw [iteratedDeriv_coordinateSlice, hn]
    rfl
  obtain ⟨q, _hq, he⟩ := Wong.FunctionElements.polynomial_of_iteratedDeriv_eq_zero
    n (coordinateSlice u 0 2) (coordinateSlice_smooth u 0 2) hz
  let p := q.comp (Polynomial.X + Polynomial.C δ)
  have hp (t : ℝ) : p.eval t = ρ t := by
    simp only [p, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, he]
    rw [coordinateSlice, hu]
    simp
  exact ⟨p, fun x => (hu x).trans (hp _).symm⟩

theorem actual_normalizing_gauge_hidden_polynomial
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra)
    (f : Fin 3 → Smooth) (V : Smooth) (α β δ : ℝ) (Λ B : Smooth)
    (hfun : AdaptedFunctionSpace (hiddenFrameAlgebra α β δ Λ E))
    (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ hiddenFrameAlgebra α β δ Λ E)
    (hL : filteringOperator f V ∈ E) (hD₀ : D f 0 ∈ E) (hD₁ : D f 1 ∈ E)
    (hf₀ : partialDerivative 2 (f 0) = 0) (hf₁ : partialDerivative 2 (f 1) = 0)
    (hf₂ : (partialDerivative 2 ^ 2) (f 2) = 0) :
    ∃ p : Polynomial ℝ, ∀ x : State,
      (partialDerivative 2 Λ).1 x = p.eval (x 2 - α*x 0 - β*x 1 - δ) := by
  let F := hiddenFrameAlgebra α β δ Λ E
  let : FiniteDimensional ℝ F := hiddenFrameAlgebra_finiteDimensional α β δ Λ E
  have hFfinite : F ≤ finiteOrderAlgebra :=
    hiddenFrameAlgebra_le_finiteOrder α β δ Λ E hfinite
  obtain ⟨N, hN⟩ := finiteOrderLieAlgebra_uniform_hidden_nilpotence F hFfinite B hB hJ
  let g := frameDrift f α β δ Λ
  let W := hiddenAffinePullback α β δ V
  have hp : normalAction (frameDiffusionNormal α β g W) ∈ F := by
    rw [normalAction_frameDiffusionNormal]
    rw [← actual_transported_filteringOperator]
    exact hiddenFrame_image_mem α β δ Λ E _ hL
  have hc := hN (frameDiffusionNormal α β g W) hp (Finsupp.single 2 1)
  rw [frameDiffusionNormal_hidden_first] at hc
  have hcM : (partialDerivative 2 ^ (N+2)) (-(α • g 0 + β • g 1 + g 2)) = 0 := by
    rw [Nat.add_comm N 2, pow_add, Module.End.mul_apply, hc, map_zero]
  obtain ⟨hg₀, hg₁⟩ := normalized_frameDrift_visible_independent E f α β δ Λ B
    hfun hB hJ hD₀ hD₁
  have hz₀ := hidden_power_zero_of_first (g 0) hg₀ (N+1)
  have hz₁ := hidden_power_zero_of_first (g 1) hg₁ (N+1)
  have hfP : (partialDerivative 2 ^ 2) (hiddenAffinePullback α β δ (f 2)) = 0 := by
    simp only [pow_two, Module.End.mul_apply, hidden_partial_pullback]
    have he : partialDerivative 2 (partialDerivative 2 (f 2)) = 0 := by
      simpa only [pow_two, Module.End.mul_apply] using hf₂
    rw [he, map_zero]
  have hzP := hidden_power_zero_of_second _ hfP N
  have he₂ : g 2 = hiddenAffinePullback α β δ (f 2) + partialDerivative 2 Λ := by
    simp [g, frameDrift, frameVectors, coordinate_directionalDerivative]
  rw [he₂] at hcM
  have hw : (partialDerivative 2 ^ (N+2)) (partialDerivative 2 Λ) = 0 := by
    simpa only [map_neg, map_add, map_smul, hz₀, hz₁, hzP,
      smul_zero, zero_add, neg_eq_zero] using hcM
  obtain ⟨ρ, _hρ, hu⟩ := normalized_visible_gauge_hidden_profile E f α β δ Λ B
    hfun hB hJ hD₀ hD₁ hf₀ hf₁
  exact polynomial_slanted_profile_of_representation_nilpotent
    (partialDerivative 2 Λ) α β δ ρ hu (N+1) hw

end Wong.SmoothModel


/-! Source segment: EulerBlockExtraction -/

/-! Scalar potentials remain genuine smooth functions during the spectral
projection; only the known differential terms are identified. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
set_option maxHeartbeats 1000000

 theorem euler_polynomial_multiplier (Q : Polynomial ℝ) (u : Smooth) :
    (Polynomial.aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) (multiplication u) =
      multiplication ((Polynomial.aeval hiddenEuler Q) u) := by
  let M : Smooth →ₗ[ℝ] Operator :=
    { toFun := multiplication
      map_add' := multiplication_add
      map_smul' := multiplication_smul }
  exact (Wong.EulerFiniteModule.aeval_intertwiner hiddenEuler
    (LieAlgebra.ad ℝ Operator hiddenEuler) M
    (fun v => (hiddenEuler_lie_multiplier v).symm) Q u).symm

theorem actual_euler_zero_projection_scalar_remainder
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (hnormal : E ≤ normalFormOperators)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (R T U : Operator) (u : Smooth)
    (hR : ⁅hiddenEuler,R⁆ = 0)
    (hT : ⁅hiddenEuler,T⁆ = (-1 : ℝ) • T)
    (hU : ⁅hiddenEuler,U⁆ = (-2 : ℝ) • U)
    (hP : R + T + U + multiplication u ∈ E) :
    ∃ q : Smooth, partialDerivative 2 q = 0 ∧ R + multiplication q ∈ E := by
  classical
  obtain ⟨Q,hval,hmem,heig⟩ := actual_euler_projection_with_prescribed_weights
    E hfinite hnormal B hB hJ (R+T+U+multiplication u) hP 0 {-2,-1,0}
  have hv₀ : Q.eval 0 = 1 := by simpa using hval 0 (by simp)
  have hv₁ : Q.eval (-1) = 0 := by simpa using hval (-1) (by simp)
  have hv₂ : Q.eval (-2) = 0 := by simpa using hval (-2) (by simp)
  have hR' : ⁅hiddenEuler,R⁆ = (0 : ℝ) • R := by simpa using hR
  let q := (Polynomial.aeval hiddenEuler Q) u
  have he : (Polynomial.aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q)
      (R+T+U+multiplication u) = R+multiplication q := by
    simp only [map_add, aeval_end_eigenvalue (LieAlgebra.ad ℝ Operator hiddenEuler) R 0 hR' Q,
      aeval_end_eigenvalue (LieAlgebra.ad ℝ Operator hiddenEuler) T (-1) hT Q,
      aeval_end_eigenvalue (LieAlgebra.ad ℝ Operator hiddenEuler) U (-2) hU Q, euler_polynomial_multiplier,
      hv₀,hv₁,hv₂,one_smul,zero_smul,add_zero,q]
  rw [he] at hmem heig
  have hq : hiddenEuler q = 0 := by
    have hz : multiplication (hiddenEuler q) = multiplication 0 := by
      simpa only [lie_add,hR,zero_add,hiddenEuler_lie_multiplier,
        Int.cast_zero,zero_smul,multiplication_zero] using heig
    exact multiplication_injective hz
  exact ⟨q,hiddenEuler_kernel_partial_zero q hq,hmem⟩

end Wong.SmoothModel


/-! Source segment: EulerLowFrame -/

/-! The linear hidden coefficient obstruction for the actual sheared
 diffusion, with arbitrary smooth scalar potential. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
set_option maxHeartbeats 1000000

 theorem hiddenEuler_of_hidden_independent (u : Smooth)
    (hu : partialDerivative 2 u = 0) : hiddenEuler u = 0 := by
  simp only [hiddenEuler,Module.End.mul_apply,hu,map_zero]

theorem hiddenEuler_lie_visibleBlock_zero (a₀ a₁ u : Smooth)
    (h₀ : partialDerivative 2 a₀ = 0) (h₁ : partialDerivative 2 a₁ = 0)
    (hu : partialDerivative 2 u = 0) :
    ⁅hiddenEuler,visibleDiffusionBlock a₀ a₁ u⁆ = 0 := by
  simp only [visibleDiffusionBlock,lie_add,lie_smul,euler_lie_mul,
    euler_lie_pow hiddenEuler (partialDerivative 0) 0 (by simp),
    euler_lie_pow hiddenEuler (partialDerivative 1) 0 (by simp),
    hiddenEuler_lie_multiplier,hiddenEuler_of_hidden_independent _ h₀,
    hiddenEuler_of_hidden_independent _ h₁,hiddenEuler_of_hidden_independent _ hu,
    hiddenEuler_lie_partial,show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 2 from by decide,ite_false,multiplication_zero,
    mul_zero,zero_mul,zero_add,add_zero,zero_smul,mul_zero,smul_zero]

theorem hiddenEuler_lie_linearBlock_zero (k l c : ℝ) (a₀ a₁ : Smooth)
    (h₀ : partialDerivative 2 a₀ = 0) (h₁ : partialDerivative 2 a₁ = 0) :
    ⁅hiddenEuler,linearEulerBlock k l c a₀ a₁ 0⁆ = 0 := by
  have hs : hiddenEuler (visibleSlope k l) = 0 :=
    hiddenEuler_of_hidden_independent _ (partial_two_visibleSlope k l)
  simp only [linearEulerBlock,lie_sub,hiddenEuler_lie_visibleBlock_zero a₀ a₁ 0 h₀ h₁
    (by simp),euler_lie_mul,lie_add,hiddenEuler_lie_multiplier,hs,
    multiplication_zero,lie_scalar_identity,lie_self,
    zero_smul,mul_zero,zero_mul,add_zero,sub_zero,zero_sub]

def negativeHiddenFrameBlock (α β : ℝ) (v : Smooth) : Operator :=
  α • (partialDerivative 0 * partialDerivative 2) +
    β • (partialDerivative 1 * partialDerivative 2) -
    multiplication v * partialDerivative 2

theorem hiddenEuler_lie_negativeHiddenFrameBlock (α β : ℝ) (v : Smooth)
    (hv : partialDerivative 2 v = 0) :
    ⁅hiddenEuler,negativeHiddenFrameBlock α β v⁆ =
      (-1 : ℝ) • negativeHiddenFrameBlock α β v := by
  simp only [negativeHiddenFrameBlock,lie_sub,lie_add,lie_smul,euler_lie_mul,
    hiddenEuler_lie_partial,show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 2 from by decide,ite_false,ite_true,
    hiddenEuler_lie_multiplier,hiddenEuler_of_hidden_independent _ hv,
    multiplication_zero,zero_smul,zero_mul,zero_add,mul_smul_comm]
  module

theorem hiddenEuler_lie_hiddenSquare (c : ℝ) :
    ⁅hiddenEuler,c • partialDerivative 2 ^ 2⁆ =
      (-2 : ℝ) • (c • partialDerivative 2 ^ 2) := by
  rw [lie_smul,euler_lie_pow hiddenEuler (partialDerivative 2) (-1) (by simp)]
  norm_num
  module

theorem frameDiffusion_normal_linear_decomposition
    (α β k l c : ℝ) (g : Fin 3 → Smooth) (V v : Smooth)
    (he : α • g 0 + β • g 1 + g 2 =
      smoothMul (visibleSlope k l + c • smoothOne)
        (linearFunction (coordinateVector 2)) + v) :
    directionalDiffusion α β g V =
      linearEulerBlock k l c (-g 0) (-g 1) 0 +
      negativeHiddenFrameBlock α β v +
      ((1+α^2+β^2)/2) • partialDerivative 2 ^ 2 +
      multiplication (frameScalar g V α β) := by
  rw [← normalAction_frameDiffusionNormal]
  simp only [frameDiffusionNormal,map_add,map_sub,normalAction_single]
  rw [he]
  simp only [multiplication_add,← multiplication_mul,multiplication_smul,
    multiplication_smoothOne]
  simp only [frameSecondNormal,map_add,normalAction_single,multiplication_smul,
    multiplication_smoothOne,smul_mul_assoc,one_mul]
  simp only [multiPartial,Finsupp.add_apply,Finsupp.single_apply]
  norm_num
  simp only [linearEulerBlock,visibleDiffusionBlock,negativeHiddenFrameBlock,
    multiplication_neg_smooth,multiplication_zero,hiddenEuler,mul_assoc,
    add_mul,mul_add,neg_mul,mul_neg,zero_mul,mul_zero,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  apply LinearMap.ext
  intro u
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.neg_apply,LinearMap.zero_apply,Module.End.mul_apply,multiplication_apply,
    map_add,map_sub,map_smul,map_neg]
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,
    Submodule.coe_neg,Submodule.coe_zero,Pi.add_apply,Pi.sub_apply,
    Pi.smul_apply,Pi.neg_apply,Pi.zero_apply,
    smoothMul_apply,smul_eq_mul] <;> ring

theorem actual_low_frameDiffusion_hidden_slopes_zero
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (hnormal : E ≤ normalFormOperators)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (α β k l c : ℝ) (g : Fin 3 → Smooth) (V v : Smooth)
    (hg₀ : partialDerivative 2 (g 0) = 0) (hg₁ : partialDerivative 2 (g 1) = 0)
    (hv : partialDerivative 2 v = 0)
    (he : α • g 0 + β • g 1 + g 2 =
      smoothMul (visibleSlope k l + c • smoothOne)
        (linearFunction (coordinateVector 2)) + v)
    (hL : directionalDiffusion α β g V ∈ E)
    (hHeat : partialDerivative 2 ^ 2 ∈ E) : k = 0 ∧ l = 0 := by
  rw [frameDiffusion_normal_linear_decomposition α β k l c g V v he] at hL
  obtain ⟨q,hq,hmem⟩ := actual_euler_zero_projection_scalar_remainder E hfinite hnormal B hB hJ
    (linearEulerBlock k l c (-g 0) (-g 1) 0)
    (negativeHiddenFrameBlock α β v)
    (((1+α^2+β^2)/2) • partialDerivative 2 ^ 2)
    (frameScalar g V α β)
    (hiddenEuler_lie_linearBlock_zero k l c _ _ (by simp [hg₀]) (by simp [hg₁]))
    (hiddenEuler_lie_negativeHiddenFrameBlock α β v hv)
    (hiddenEuler_lie_hiddenSquare _) hL
  have hblock : linearEulerBlock k l c (-g 0) (-g 1) q ∈ E := by
    have heq : linearEulerBlock k l c (-g 0) (-g 1) q =
        linearEulerBlock k l c (-g 0) (-g 1) 0 + multiplication q := by
      simp only [linearEulerBlock,visibleDiffusionBlock,multiplication_zero]
      abel
    rwa [heq]
  exact linearEulerBlock_visible_slopes_zero E hfinite k l c _ _ q
    (by simp [hg₀]) (by simp [hg₁]) hq hblock hHeat

end Wong.SmoothModel
