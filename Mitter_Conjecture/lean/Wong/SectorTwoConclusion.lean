import Wong.SectorTwoProfileBridge
import Wong.SectorTwoWeightedBridge

set_option maxHeartbeats 1800000

/- Source section: SectorTwoActualObstruction -/

/-! The final second-sector obstruction is applied to the actual original
estimation algebra after two genuine gauges. All profile and degree hypotheses
of the weighted theorem are proved upstream from real Lie membership. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

theorem canonicalWeightedOperator_normalized (b : ℝ) (F ε r U₀ U₁ : Smooth) :
    canonicalWeightedOperator (b • x 0) F ε (U₀ + x 2 * U₁) r =
      normalizedGenerator b F ε r U₀ U₁ := by
  simp only [canonicalWeightedOperator, normalizedGenerator, stationaryGenerator,
    multiplication_smul, smul_mul_assoc]
  module

theorem actual_canonical_obstruction {n : ℕ} (f : Fin 3 → Smooth) (obs : Fin n → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f obs)]
    (Λ : Smooth) (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0)
    (hΛ : gaugeDrift Λ f = drift b k h c)
    (hE : AdaptedFunctionSpace (gaugeAlgebra Λ (estimationAlgebra f obs)))
    (hL : filteringOperator (drift b k h c) V ∈ gaugeAlgebra Λ (estimationAlgebra f obs))
    (h₀ : D (drift b k h c) 0 ∈ gaugeAlgebra Λ (estimationAlgebra f obs))
    (h₁ : D (drift b k h c) 1 ∈ gaugeAlgebra Λ (estimationAlgebra f obs)) : False := by
  obtain ⟨ε, e, V₀, a₀, a₁, p, hε₀, hε₁, he₀, he₁, hV₀, hε₂, hp, hV⟩ :=
    polynomial_profile f obs Λ b k h c V hk hΛ hE hL h₀ h₁
  obtain ⟨P, hP⟩ := exists_univariate_profile ε p hp hε₀ hε₁
  let d := P.natDegree
  let m := max 2 d
  have heps : HiddenDegreeLE (m : ℤ) ε :=
    (univariate_profile_degree P ε hP).mono (by dsimp [m, d]; omega)
  have hepsnil : (partialDerivative 2 ^ (m + 1)) ε = 0 :=
    (hiddenDegreeLE_nat_iff m ε).mp heps
  have hrnil := actual_scalarTail_nilpotent _ hE b k h c a₀ a₁ V ε e V₀ hk hL h₀
    hε₀ hε₁ he₀ he₁ hV₀ hε₂ hV m (by dsimp [m]; omega) hepsnil
  have hr : HiddenDegreeLE (m : ℤ) (scalarTail ε e) :=
    (hiddenDegreeLE_nat_iff m _).mpr hrnil
  let E := gaugeAlgebra (hiddenPrimitive ε) (gaugeAlgebra Λ (estimationAlgebra f obs))
  let _ : FiniteDimensional ℝ (gaugeAlgebra Λ (estimationAlgebra f obs)) :=
    gaugeAlgebra_finiteDimensional Λ _
  let _ : FiniteDimensional ℝ E := gaugeAlgebra_finiteDimensional _ _
  let U₀ := visiblePotential b k h c V₀
  let U₁ := visibleLinearPotential a₀ a₁
  have hnorm : normalizedGenerator b (F k h c) ε (scalarTail ε e) U₀ U₁ ∈ E := by
    rw [normalizedGenerator_eq_filtering b k h c a₀ a₁ ε e V₀ V hV,
      ← hidden_gauge_drift b k h c ε hε₀ hε₁]
    exact filteringOperator_mem_gaugeAlgebra _ _ _ V hL
  have hw : canonicalWeightedOperator (b • x 0) (F k h c) ε
      (U₀ + x 2 * U₁) (scalarTail ε e) ∈ E := by
    rw [canonicalWeightedOperator_normalized]
    exact hnorm
  have hx : partialDerivative 0 ∈ E := by
    have hh := D_mem_gaugeAlgebra (hiddenPrimitive ε) _ (drift b k h c) 0 h₀
    rw [hidden_gauge_drift b k h c ε hε₀ hε₁] at hh
    have hd : D (shiftedDrift b k h c ε) 0 = partialDerivative 0 := by
      simp [D, shiftedDrift]
    rw [hd] at hh
    exact hh
  obtain ⟨hU₀, hU₁, hr₀, hr₁⟩ := normalized_profiles_hidden_zero b k h c a₀ a₁ ε e V₀
    hV₀ hε₀ hε₁ he₀ he₁
  have hg : HiddenDegreeLE 0 (b • x 0) :=
    HiddenDegreeLE.of_hiddenDerivative_eq_zero _ (by simp)
  have hF : HiddenDegreeLE 0 (F k h c) :=
    HiddenDegreeLE.of_hiddenDerivative_eq_zero _ (by simp)
  have hVP : HiddenDegreeLE 1 (U₀ + x 2 * U₁) := by
    apply ((HiddenDegreeLE.of_hiddenDerivative_eq_zero U₀ hU₀).mono (by norm_num)).add
    have ht : HiddenDegreeLE 1 (x 2) := by simpa using hiddenCoordinate_power_degree 1
    simpa using ht.mul (HiddenDegreeLE.of_hiddenDerivative_eq_zero U₁ hU₁)
  have hεvis : ∀ i : Fin 3, i ≠ 2 → partialDerivative i ε = 0 := by
    intro i hi
    fin_cases i
    · change partialDerivative 0 ε = 0
      exact hε₀
    · change partialDerivative 1 ε = 0
      exact hε₁
    · exact (hi rfl).elim
  have hrvis : ∀ i : Fin 3, i ≠ 2 → partialDerivative i (scalarTail ε e) = 0 := by
    intro i hi
    fin_cases i
    · change partialDerivative 0 (scalarTail ε e) = 0
      exact hr₀
    · change partialDerivative 1 (scalarTail ε e) = 0
      exact hr₁
    · exact (hi rfl).elim
  have hF0 : partialDerivative 0 (F k h c) = k • linearFunction (coordinateVector 0) := by
    simp [u, x]
  by_cases hd : d ≤ 2
  · have hm : m = 2 := max_eq_left hd
    obtain ⟨a, ha⟩ := univariate_profile_low_remainder P ε hP hd
    exact sectorTwo_quadratic_actual_obstruction E (b • x 0) (F k h c) ε
      (U₀ + x 2 * U₁) (scalarTail ε e) a k hk hw hx hg hF
      (by simpa [hm] using heps) hεvis hVP (by simpa [hm] using hr) hrvis hF0
      (by simp) (by simpa only [quadraticHiddenProfile, x] using ha)
  · have hd' : 3 ≤ d := by omega
    have hm : m = d := max_eq_right (by omega)
    exact sectorTwo_high_actual_obstruction E (b • x 0) (F k h c) ε
      (U₀ + x 2 * U₁) (scalarTail ε e) P.leadingCoeff k d
      (univariate_profile_nonzero_leading P hd') hk hd' hw hx hg hF
      (by simpa [hm] using heps) hεvis hVP (by simpa [hm] using hr) hrvis hF0
      (by simpa only [powerHiddenProfile, x] using univariate_profile_leading_remainder P ε hP)

end Wong.SmoothModel.SectorTwo

/- Source section: SectorTwoRemainingSlopes -/

/-! Discharging the remaining visible affine slopes on the original model.
Orthogonal diagonalization, translation, both gauges, the eta profile and
both weighted branches are actual constructions, not extra hypotheses. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

theorem triangularDrift_sector_two (p : Wong.AffineParameters)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) (hk₂ : p.k₂ = 0)
    (hk₃ : p.k₃ = 0) (hh₃ : p.h₃ = 0) (hk₀ : p.k₀ = 0) :
    triangularDrift p = drift p.b₀ p.k₁ p.h₂ p.h₀ := by
  funext i
  apply Subtype.ext
  funext z
  fin_cases i <;>
    simp [triangularDrift, triangularDriftPolynomials, polynomialSmooth,
      drift, F, x, linearFunction, coordinateVector, Fin.sum_univ_three,
      hb₁, hb₂, hk₂, hk₃, hh₃, hk₀] <;> ring

theorem nonzero_visible_matrix_impossible {n : ℕ} (f : Fin 3 → Smooth) (obs : Fin n → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f obs)]
    (hrank : linearRank (estimationAlgebra f obs) = 2)
    (hq : QuadraticFree (estimationAlgebra f obs))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f obs)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f obs)
    (p : Wong.AffineParameters) (hp : ∀ i j z, (wong f i j).1 z = p.matrix z i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) (hk₃ : p.k₃ = 0) (hh₃ : p.h₃ = 0)
    (hne : p.k₁ ≠ 0 ∨ p.k₂ ≠ 0 ∨ p.h₂ ≠ 0) : False := by
  obtain ⟨e, q, he, hqform, hfdq, hrq, hqq, hxq₀, hxq₁,
      hbq₁, hbq₂, hkq₃, hhq₃, hkq, hkq₂, _hhq₁⟩ :=
    VisibleHeads.diagonal_sector_two_model f obs hrank hq hx₀ hx₁ p hp hb₁ hb₂ hk₃ hh₃ hne
  let f₁ := coordinateDrift e f
  let obs₁ := coordinateObservations e obs
  let _ : FiniteDimensional ℝ (estimationAlgebra f₁ obs₁) := hfdq
  let z := VisibleHeads.firstHiddenConstantShift q
  let q' := VisibleHeads.translatedParameters z q
  let f₂ := translationDrift z f₁
  let obs₂ := translationObservations z obs₁
  obtain ⟨hqform', hfd', hr', hqq', hx'₀, hx'₁, hk'₀, hk'⟩ :=
    VisibleHeads.translated_sector_two_model f₁ obs₁ hrq hqq hxq₀ hxq₁ q hqform hkq
  let _ : FiniteDimensional ℝ (estimationAlgebra f₂ obs₂) := hfd'
  have htri : triangularDrift q' = drift q'.b₀ q'.k₁ q'.h₂ q'.h₀ :=
    triangularDrift_sector_two q' hbq₁ hbq₂ hkq₂ hkq₃ hhq₃ hk'₀
  obtain ⟨cg⟩ := exists_canonicalGaugeData f₂ obs₂ hr' hqq' hx'₀ hx'₁ q' hqform'
  apply actual_canonical_obstruction f₂ obs₂ cg.Λ q'.b₀ q'.k₁ q'.h₂ q'.h₀
    (eta f₂ obs₂) hk' (cg.drift_eq.trans htri) cg.functionSpace
  · simpa only [htri] using cg.filtering_mem
  · simpa only [htri] using cg.D_zero_mem
  · simpa only [htri] using cg.D_one_mem

/-- This is exactly the remaining-slopes conclusion with the original f,h,
finite-dimensionality, rank-two, quadratic-free and adapted-coordinate hypotheses. -/
theorem remaining_visible_affine_slopes {n : ℕ} (f : Fin 3 → Smooth) (obs : Fin n → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f obs)]
    (hrank : linearRank (estimationAlgebra f obs) = 2)
    (hq : QuadraticFree (estimationAlgebra f obs))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f obs)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f obs)
    (p : Wong.AffineParameters) (hp : ∀ i j z, (wong f i j).1 z = p.matrix z i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) (hk₃ : p.k₃ = 0) (hh₃ : p.h₃ = 0) :
    p.k₁ = 0 ∧ p.k₂ = 0 ∧ p.h₂ = 0 := by
  by_contra! hn
  have hne : p.k₁ ≠ 0 ∨ p.k₂ ≠ 0 ∨ p.h₂ ≠ 0 := by tauto
  exact nonzero_visible_matrix_impossible f obs hrank hq hx₀ hx₁ p hp hb₁ hb₂ hk₃ hh₃ hne

end Wong.SmoothModel.SectorTwo
