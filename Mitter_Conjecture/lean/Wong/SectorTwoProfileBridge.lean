import Wong.SectorTwoCalculus
import Wong.RootAnalyticBridges
import Wong.SectorTwoDiagonalization
import Wong.WeightedSymbolBridgeCore
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option maxHeartbeats 1200000

/- Source section: SectorTwoTranslation -/

/-! A true translation of the original filtering model eliminates the
remaining constant in the nonzero first hidden Wong entry. -/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads

def translatedParameters (z : State) (p : Wong.AffineParameters) : Wong.AffineParameters :=
  { p with b₀ := p.w12 z, k₀ := p.w13 z, h₀ := p.w23 z }

theorem translatedParameters_matrix (z : State) (p : Wong.AffineParameters) (x : State) :
    (translatedParameters z p).matrix x = p.matrix (x + z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translatedParameters, Wong.AffineParameters.matrix,
      Wong.AffineParameters.w12, Wong.AffineParameters.w13, Wong.AffineParameters.w23] <;> ring

theorem wong_translation_parameters (z : State) (f : Fin 3 → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    ∀ i j x, (wong (translationDrift z f) i j).1 x =
      (translatedParameters z p).matrix x i j := by
  intro i j x
  rw [wong_translationDrift, translatedParameters_matrix]
  exact hp i j (x + z)

def firstHiddenConstantShift (p : Wong.AffineParameters) : State :=
  ![-p.k₀ / p.k₁, 0, 0]

theorem translated_firstHidden_constant_zero (p : Wong.AffineParameters)
    (hk : p.k₁ ≠ 0) : (translatedParameters (firstHiddenConstantShift p) p).k₀ = 0 := by
  simp [translatedParameters, firstHiddenConstantShift, Wong.AffineParameters.w13]
  field_simp [hk] <;> ring

/-- This is a translation of the real filtering model, so the transported
eta, observations and generated Lie algebra retain every required hypothesis. -/
theorem translated_sector_two_model {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hk : p.k₁ ≠ 0) :
    let z := firstHiddenConstantShift p
    let q := translatedParameters z p
    (∀ i j x, (wong (translationDrift z f) i j).1 x = q.matrix x i j) ∧
      FiniteDimensional ℝ (estimationAlgebra (translationDrift z f) (translationObservations z h)) ∧
      linearRank (estimationAlgebra (translationDrift z f) (translationObservations z h)) = 2 ∧
      QuadraticFree (estimationAlgebra (translationDrift z f) (translationObservations z h)) ∧
      multiplication (linearFunction (coordinateVector 0)) ∈
        estimationAlgebra (translationDrift z f) (translationObservations z h) ∧
      multiplication (linearFunction (coordinateVector 1)) ∈
        estimationAlgebra (translationDrift z f) (translationObservations z h) ∧
      q.k₀ = 0 ∧ q.k₁ ≠ 0 := by
  dsimp only
  exact ⟨wong_translation_parameters _ f p hp,
    finiteDimensional_translationEstimationAlgebra _ f h,
    linearRank_translationEstimationAlgebra _ f h hrank,
    quadraticFree_translationEstimationAlgebra _ f h hq,
    coordinate_mem_translationEstimationAlgebra _ f h hrank 0 h₀,
    coordinate_mem_translationEstimationAlgebra _ f h hrank 1 h₁,
    translated_firstHidden_constant_zero p hk, hk⟩

end Wong.SmoothModel.VisibleHeads

/- Source section: SectorTwoPolynomialProfile -/

/-! The hidden potential profile obtained from actual brackets is polynomial;
its degree bound comes from kernel-checked smooth polynomial differentiation. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

theorem polynomial_profile {m : ℕ} (f : Fin 3 → Smooth) (obs : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f obs)]
    (Λ : Smooth) (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0)
    (hΛ : gaugeDrift Λ f = drift b k h c)
    (hE : AdaptedFunctionSpace (gaugeAlgebra Λ (estimationAlgebra f obs)))
    (hL : filteringOperator (drift b k h c) V ∈ gaugeAlgebra Λ (estimationAlgebra f obs))
    (h₀ : D (drift b k h c) 0 ∈ gaugeAlgebra Λ (estimationAlgebra f obs))
    (h₁ : D (drift b k h c) 1 ∈ gaugeAlgebra Λ (estimationAlgebra f obs)) :
    ∃ (ε e V₀ : Smooth) (a₀ a₁ : ℝ) (p : RealPoly),
      partialDerivative 0 ε = 0 ∧ partialDerivative 1 ε = 0 ∧
      partialDerivative 0 e = 0 ∧ partialDerivative 1 e = 0 ∧
      partialDerivative 2 V₀ = 0 ∧ partialDerivative 2 ε = q k V ∧
      ε = polynomialSmooth p ∧
      V = V₀ + (2 : ℝ) • (ε * F k h c) + e +
        x 2 * (a₀ • x 0 + a₁ • x 1) := by
  obtain ⟨ε, e, V₀, a₀, a₁, hε₀, hε₁, he₀, he₁, hV₀, hε₂, hV⟩ :=
    potential_profile _ hE b k h c V hk hL h₀ h₁
  obtain ⟨pg, hpg⟩ := polynomial_of_polynomial_gradient (g b k h c V)
    (scalar_gradient_polynomial f obs Λ b k h c V hk hΛ hL h₀)
  have hq : q k V = polynomialSmooth (MvPolynomial.pderiv 2 pg) := by
    rw [← partial_g b k h c V, hpg, partialDerivative_polynomialSmooth]
  have hgrad : ∀ i : Fin 3, ∃ p : RealPoly, partialDerivative i ε = polynomialSmooth p := by
    intro i
    fin_cases i
    · exact ⟨0, hε₀.trans polynomialSmooth_zero.symm⟩
    · exact ⟨0, hε₁.trans polynomialSmooth_zero.symm⟩
    · exact ⟨MvPolynomial.pderiv 2 pg, hε₂.trans hq⟩
  obtain ⟨p, hp⟩ := polynomial_of_polynomial_gradient ε hgrad
  exact ⟨ε, e, V₀, a₀, a₁, p, hε₀, hε₁, he₀, he₁, hV₀, hε₂, hp, hV⟩

theorem polynomial_hiddenDegreeLE (p : RealPoly) :
    HiddenDegreeLE (p.totalDegree : ℤ) (polynomialSmooth p) := by
  intro n hn
  exact polynomialSmooth_partial_pow_zero p 2 n (by exact_mod_cast hn)

end Wong.SmoothModel.SectorTwo

/- Source section: SectorTwoUnivariate -/

/-! Exact hidden degree and leading term of a genuine univariate smooth
polynomial profile. The coefficient is the actual nonzero leading coefficient. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

theorem hiddenCoordinate_power_degree (n : ℕ) : HiddenDegreeLE (n : ℤ) (x 2 ^ n) := by
  have hx : HiddenDegreeLE 1 (x 2) := by
    apply (hiddenDegreeLE_nat_iff 1 (x 2)).mpr
    change partialDerivative 2 (partialDerivative 2 (x 2)) = 0
    simp
  induction n with
  | zero => simpa using HiddenDegreeLE.constant (1 : ℝ)
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one] using ih.mul hx

theorem hiddenDegree_sum {ι : Type*} (s : Finset ι) (u : ι → Smooth) (N : ℤ)
    (h : ∀ i ∈ s, HiddenDegreeLE N (u i)) : HiddenDegreeLE N (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HiddenDegreeLE.zero N
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem univariate_profile_sum (P : Polynomial ℝ) (ε : Smooth)
    (hε : ∀ z : State, ε.1 z = P.eval (z 2)) :
    ε = ∑ n ∈ Finset.range (P.natDegree + 1), (P.coeff n) • (x 2 ^ n) := by
  apply Subtype.ext
  funext z
  have hp := (hε z).trans (Polynomial.eval_eq_sum_range (p := P) (z 2))
  simpa [Submodule.coe_sum, Finset.sum_apply, x, linearFunction,
    coordinateVector, Fin.sum_univ_three] using hp

theorem univariate_profile_degree (P : Polynomial ℝ) (ε : Smooth)
    (hε : ∀ z : State, ε.1 z = P.eval (z 2)) : HiddenDegreeLE (P.natDegree : ℤ) ε := by
  rw [univariate_profile_sum P ε hε]
  apply hiddenDegree_sum
  intro n hn
  apply ((hiddenCoordinate_power_degree n).smul (P.coeff n)).mono
  have hn' := Finset.mem_range.mp hn
  omega

theorem univariate_profile_leading_remainder (P : Polynomial ℝ) (ε : Smooth)
    (hε : ∀ z : State, ε.1 z = P.eval (z 2)) :
    HiddenDegreeLE ((P.natDegree : ℤ) - 1)
      (ε - P.leadingCoeff • (x 2 ^ P.natDegree)) := by
  have he := univariate_profile_sum P ε hε
  rw [Finset.sum_range_succ, Polynomial.coeff_natDegree] at he
  rw [he, add_sub_cancel_right]
  apply hiddenDegree_sum
  intro n hn
  apply ((hiddenCoordinate_power_degree n).smul (P.coeff n)).mono
  have hn' := Finset.mem_range.mp hn
  omega

theorem univariate_profile_low_remainder (P : Polynomial ℝ) (ε : Smooth)
    (hε : ∀ z : State, ε.1 z = P.eval (z 2)) (hd : P.natDegree ≤ 2) :
    ∃ a : ℝ, HiddenDegreeLE 1 (ε - a • (x 2 * x 2)) := by
  have he : ε = (P.coeff 0) • smoothOne + (P.coeff 1) • x 2 +
      (P.coeff 2) • (x 2 * x 2) := by
    apply Subtype.ext
    funext z
    have hp := (hε z).trans (Polynomial.eval_eq_sum_range' (p := P)
      (n := 3) (by omega) (z 2))
    simpa [Finset.sum_range_succ, x, linearFunction, coordinateVector,
      Fin.sum_univ_three, smoothOne, pow_two] using hp
  refine ⟨P.coeff 2, ?_⟩
  rw [he, add_sub_cancel_right]
  exact ((HiddenDegreeLE.constant (P.coeff 0)).mono (by norm_num)).add
    (by simpa using (hiddenCoordinate_power_degree 1).smul (P.coeff 1))

theorem univariate_profile_nonzero_leading (P : Polynomial ℝ) (hd : 3 ≤ P.natDegree) :
    P.leadingCoeff ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro hz
  simp [hz] at hd

/-- Polynomiality plus actual hidden-only dependence produces a true univariate profile. -/
theorem exists_univariate_profile (ε : Smooth) (p : RealPoly) (hp : ε = polynomialSmooth p)
    (h₀ : partialDerivative 0 ε = 0) (h₁ : partialDerivative 1 ε = 0) :
    ∃ P : Polynomial ℝ, ∀ z : State, ε.1 z = P.eval (z 2) := by
  have hn : (partialDerivative 2 ^ (p.totalDegree + 1)) ε = 0 := by
    rw [hp]
    exact polynomialSmooth_partial_pow_zero p 2 _ (by omega)
  have h₀' : directionalDerivative (coordinateVector 0 + (0 : ℝ) • coordinateVector 2) ε = 0 := by
    simpa [coordinate_directionalDerivative] using h₀
  have h₁' : directionalDerivative (coordinateVector 1 + (0 : ℝ) • coordinateVector 2) ε = 0 := by
    simpa [coordinate_directionalDerivative] using h₁
  obtain ⟨P, hP⟩ := polynomial_slanted_hidden_profile_of_nilpotent ε 0 0 0 h₀' h₁' p.totalDegree hn
  exact ⟨P, by simpa using hP⟩

end Wong.SmoothModel.SectorTwo
