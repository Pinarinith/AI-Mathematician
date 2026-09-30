import Wong.HiddenEulerElement
import Wong.AffineFrameAlgebra
import Wong.GaugeNormalForm
import Wong.SmoothHiddenPrimitive
import Wong.EulerFunctionSpace
import Wong.HiddenProfiles

/-! Normalization uses the image of the actual algebra and genuine smooth
global gauges. All membership and finite-order premises are transported. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open scoped ContDiff

abbrev hiddenFrameAlgebra (α β δ : ℝ) (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) : LieSubalgebra ℝ Operator :=
  gaugeAlgebra Λ (affineAlgebra (hiddenShear α β) ![0, 0, -δ] E)

theorem hiddenFrameAlgebra_finiteDimensional (α β δ : ℝ) (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (hiddenFrameAlgebra α β δ Λ E) := by
  let := affineAlgebra_finiteDimensional (hiddenShear α β) ![0, 0, -δ] E
  exact gaugeAlgebra_finiteDimensional Λ _

theorem hiddenFrameAlgebra_le_normalFormOperators (α β δ : ℝ) (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (hE : E ≤ normalFormOperators) :
    hiddenFrameAlgebra α β δ Λ E ≤ normalFormOperators :=
  gaugeAlgebra_le_normalFormOperators Λ _ (affineAlgebra_le_normalFormOperators _ _ E hE)

theorem hiddenFrameAlgebra_le_finiteOrder (α β δ : ℝ) (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (hE : E ≤ finiteOrderAlgebra) :
    hiddenFrameAlgebra α β δ Λ E ≤ finiteOrderAlgebra :=
  gaugeAlgebra_le_finiteOrder Λ _ (affineAlgebra_le_finiteOrder _ _ E hE)

theorem hiddenFrameAlgebra_adaptedFunctionSpace (α β δ : ℝ) (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (hE : AdaptedFunctionSpace E) :
    AdaptedFunctionSpace (hiddenFrameAlgebra α β δ Λ E) :=
  adaptedFunctionSpace_gauge Λ _ (adaptedFunctionSpace_hiddenAffine α β δ E hE)

theorem hiddenFrame_image_mem (α β δ : ℝ) (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (A : Operator) (hA : A ∈ E) :
    gaugeConjugation Λ (affineConjugation (hiddenShear α β) ![0, 0, -δ] A) ∈
      hiddenFrameAlgebra α β δ Λ E :=
  ⟨affineConjugation (hiddenShear α β) ![0, 0, -δ] A, ⟨A, hA, rfl⟩, rfl⟩

theorem exists_normalized_hiddenEuler (E : LieSubalgebra ℝ Operator)
    (f : Fin 3 → Smooth) (V : Smooth) (p : Wong.AffineParameters)
    (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hμ : hiddenSlopeNorm p ≠ 0) (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0)
    (hL : filteringOperator f V ∈ E) (hD₀ : D f 0 ∈ E) (hD₁ : D f 1 ∈ E) :
    ∃ Λ B : Smooth, partialDerivative 2 B = 0 ∧
      hiddenEuler + multiplication B ∈
        hiddenFrameAlgebra (hiddenSlopeAlpha p) (hiddenSlopeBeta p) (hiddenSlopeDelta p) Λ E := by
  let r := hiddenAffinePullback (hiddenSlopeAlpha p) (hiddenSlopeBeta p)
    (hiddenSlopeDelta p) (hiddenEulerScalar f V p)
  obtain ⟨Λ, hΛ⟩ := exists_hidden_euler_gauge r
  refine ⟨Λ, hiddenRestriction r, partialDerivative_hiddenRestriction r, ?_⟩
  have hJ := hiddenEulerLieWord_mem E f V p hL hD₀ hD₁
  have hmem := hiddenFrame_image_mem (hiddenSlopeAlpha p) (hiddenSlopeBeta p)
    (hiddenSlopeDelta p) Λ E (hiddenEulerLieWord f V p) hJ
  rw [hiddenEulerLieWord_affine_frame f V p hform hμ hb₁ hb₂] at hmem
  exact hΛ ▸ hmem

theorem gaugeConjugation_directionalDerivative (Λ : Smooth) (v : State) :
    gaugeConjugation Λ (directionalDerivative v) =
      directionalDerivative v - multiplication (directionalDerivative v Λ) := by
  simp only [directionalDerivative, map_sum, map_smul,
    gaugeConjugation_partialDerivative, smul_sub, Finset.sum_sub_distrib,
    LinearMap.sum_apply, LinearMap.smul_apply, multiplication_sum, multiplication_smul]

theorem hiddenShear_symm_visible_vectors (α β : ℝ) :
    (hiddenShear α β).symm (coordinateVector 0) =
      coordinateVector 0 + α • coordinateVector 2 ∧
    (hiddenShear α β).symm (coordinateVector 1) =
      coordinateVector 1 + β • coordinateVector 2 := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [hiddenShear, hiddenShearLinear, coordinateVector]

theorem multiplication_neg_smooth (u : Smooth) :
    multiplication (-u) = -multiplication u := by
  simpa using multiplication_sub (0 : Smooth) u

theorem hiddenFrame_D (f : Fin 3 → Smooth) (α β δ : ℝ) (Λ : Smooth) (i : Fin 3) :
    gaugeConjugation Λ (affineConjugation (hiddenShear α β) ![0, 0, -δ] (D f i)) =
      directionalDerivative ((hiddenShear α β).symm (coordinateVector i)) +
        multiplication (-(hiddenAffinePullback α β δ (f i) +
          directionalDerivative ((hiddenShear α β).symm (coordinateVector i)) Λ)) := by
  simp only [D, map_sub, ← coordinate_directionalDerivative,
    affineConjugation_directionalDerivative, affineConjugation_multiplication,
    gaugeConjugation_directionalDerivative, gaugeConjugation_multiplication]
  rw [multiplication_neg_smooth, multiplication_add]
  abel

theorem partialDerivative_directionalDerivative_commute (i : Fin 3) (v : State) (u : Smooth) :
    partialDerivative i (directionalDerivative v u) =
      directionalDerivative v (partialDerivative i u) := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, partialDerivative_commute_apply]

theorem hidden_partial_pullback (α β δ : ℝ) (u : Smooth) :
    partialDerivative 2 (hiddenAffinePullback α β δ u) =
      hiddenAffinePullback α β δ (partialDerivative 2 u) := by
  rw [← coordinate_directionalDerivative]
  change directionalDerivative (coordinateVector 2)
    (affinePullback (hiddenShear α β) ![0, 0, -δ] u) = _
  rw [directionalDerivative_affinePullback]
  have he : hiddenShear α β (coordinateVector 2) = coordinateVector 2 := by
    funext i
    fin_cases i <;> simp [hiddenShear, hiddenShearLinear, coordinateVector]
  rw [he, coordinate_directionalDerivative]
  rfl

theorem normalized_visible_gauge_hidden_profile
    (E : LieSubalgebra ℝ Operator) (f : Fin 3 → Smooth) (α β δ : ℝ) (Λ B : Smooth)
    (hfun : AdaptedFunctionSpace (hiddenFrameAlgebra α β δ Λ E))
    (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ hiddenFrameAlgebra α β δ Λ E)
    (hD₀ : D f 0 ∈ E) (hD₁ : D f 1 ∈ E)
    (hf₀ : partialDerivative 2 (f 0) = 0) (hf₁ : partialDerivative 2 (f 1) = 0) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧
      ∀ x : State, (partialDerivative 2 Λ).1 x =
        ρ (x 2 - α * x 0 - β * x 1 - δ) := by
  obtain ⟨he₀, he₁⟩ := hiddenShear_symm_visible_vectors α β
  have hz (i : Fin 3) (hi : i ≠ 2) (a : ℝ)
      (he : (hiddenShear α β).symm (coordinateVector i) =
        coordinateVector i + a • coordinateVector 2)
      (hD : D f i ∈ E) (hf : partialDerivative 2 (f i) = 0) :
      directionalDerivative (coordinateVector i + a • coordinateVector 2)
        (partialDerivative 2 Λ) = 0 := by
    have hmem := hiddenFrame_image_mem α β δ Λ E (D f i) hD
    rw [hiddenFrame_D, he, directionalDerivative_add, directionalDerivative_smul,
      coordinate_directionalDerivative, coordinate_directionalDerivative] at hmem
    have hu := adapted_firstOrder_hidden_independent _ hfun B
      (-(hiddenAffinePullback α β δ (f i) +
        (partialDerivative i + a • partialDerivative 2) Λ)) hB hJ i hi a hmem
    have hp : partialDerivative 2 (hiddenAffinePullback α β δ (f i)) = 0 := by
      rw [hidden_partial_pullback, hf, map_zero]
    have hc : partialDerivative 2 ((partialDerivative i + a • partialDerivative 2) Λ) =
        directionalDerivative (coordinateVector i + a • coordinateVector 2)
          (partialDerivative 2 Λ) := by
      have ho : partialDerivative i + a • partialDerivative 2 =
          directionalDerivative (coordinateVector i + a • coordinateVector 2) := by
        rw [directionalDerivative_add, directionalDerivative_smul,
          coordinate_directionalDerivative, coordinate_directionalDerivative]
      rw [ho, partialDerivative_directionalDerivative_commute]
    simpa only [map_neg, map_add, hp, zero_add, hc, neg_eq_zero] using hu
  apply exists_slanted_hidden_profile _ α β δ
  · exact hz 0 (by decide) α he₀ hD₀ hf₀
  · exact hz 1 (by decide) β he₁ hD₁ hf₁

end Wong.SmoothModel
