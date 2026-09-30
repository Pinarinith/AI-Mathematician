import Wong.AffineFrame
import Wong.AdaptedGauge
import Wong.EulerFiniteModule

/-! The genuine hidden Euler Lie element obtained from nonzero affine hidden slopes. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

def hiddenSlopeNorm (p : Wong.AffineParameters) : ℝ := p.k₃ ^ 2 + p.h₃ ^ 2

def hiddenSlopeAlpha (p : Wong.AffineParameters) : ℝ :=
  (p.k₃ * p.k₁ + p.h₃ * p.k₂) / hiddenSlopeNorm p

def hiddenSlopeBeta (p : Wong.AffineParameters) : ℝ :=
  (p.k₃ * p.k₂ + p.h₃ * p.h₂) / hiddenSlopeNorm p

def hiddenSlopeDelta (p : Wong.AffineParameters) : ℝ :=
  (p.k₃ * p.k₀ + p.h₃ * p.h₀) / hiddenSlopeNorm p

def hiddenSlopeCoordinate (f : Fin 3 → Smooth) (p : Wong.AffineParameters) : Smooth :=
  (hiddenSlopeNorm p)⁻¹ • (p.k₃ • wong f 0 2 + p.h₃ • wong f 1 2)

def hiddenEulerLieWord (f : Fin 3 → Smooth) (V : Smooth) (p : Wong.AffineParameters) : Operator :=
  (hiddenSlopeNorm p)⁻¹ •
    (p.k₃ • (⁅filteringOperator f V, D f 0⁆ - p.b₀ • D f 1) +
      p.h₃ • (⁅filteringOperator f V, D f 1⁆ + p.b₀ • D f 0))

def hiddenEulerScalar (f : Fin 3 → Smooth) (V : Smooth) (p : Wong.AffineParameters) : Smooth :=
  (hiddenSlopeNorm p)⁻¹ •
    (p.k₃ • filteringRemainder f V 0 + p.h₃ • filteringRemainder f V 1) -
    smoothMul (hiddenSlopeCoordinate f p) (f 2)

theorem hiddenSlopeNorm_pos (p : Wong.AffineParameters)
    (hne : p.k₃ ≠ 0 ∨ p.h₃ ≠ 0) : 0 < hiddenSlopeNorm p := by
  dsimp [hiddenSlopeNorm]
  rcases hne with hk | hh
  · nlinarith [sq_pos_of_ne_zero hk, sq_nonneg p.h₃]
  · nlinarith [sq_pos_of_ne_zero hh, sq_nonneg p.k₃]

theorem hiddenSlopeCoordinate_eq_affine (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hμ : hiddenSlopeNorm p ≠ 0) :
    hiddenSlopeCoordinate f p =
      hiddenAffineCoordinate (hiddenSlopeAlpha p) (hiddenSlopeBeta p) (hiddenSlopeDelta p) := by
  have hb := affineWong_bianchi_parameters f p hform
  apply Subtype.ext
  funext x
  simp [hiddenSlopeCoordinate, hform, Wong.AffineParameters.matrix,
    Wong.AffineParameters.w13, Wong.AffineParameters.w23, hiddenAffineCoordinate,
    hiddenSlopeAlpha, hiddenSlopeBeta, hiddenSlopeDelta, linearFunction, smoothOne,
    Fin.sum_univ_three, hb]
  field_simp [hμ]
  simp only [hiddenSlopeNorm]
  ring

theorem hiddenEulerLieWord_mem (E : LieSubalgebra ℝ Operator)
    (f : Fin 3 → Smooth) (V : Smooth) (p : Wong.AffineParameters)
    (hL : filteringOperator f V ∈ E) (hD₀ : D f 0 ∈ E) (hD₁ : D f 1 ∈ E) :
    hiddenEulerLieWord f V p ∈ E := by
  exact E.smul_mem _ (E.add_mem
    (E.smul_mem _ (E.sub_mem (E.lie_mem hL hD₀) (E.smul_mem _ hD₁)))
    (E.smul_mem _ (E.add_mem (E.lie_mem hL hD₁) (E.smul_mem _ hD₀))))

theorem hiddenEulerLieWord_eq (f : Fin 3 → Smooth) (V : Smooth) (p : Wong.AffineParameters)
    (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) :
    hiddenEulerLieWord f V p =
      multiplication (hiddenSlopeCoordinate f p) * partialDerivative 2 +
        multiplication (hiddenEulerScalar f V p) := by
  have hw : wong f 0 1 = p.b₀ • smoothOne := by
    apply Subtype.ext
    funext x
    simp [hform, Wong.AffineParameters.matrix, Wong.AffineParameters.w12,
      hb₁, hb₂, smoothOne]
  have hw' : wong f 1 0 = -(p.b₀ • smoothOne) := (wong_skew f 0 1).trans (congrArg Neg.neg hw)
  simp only [hiddenEulerLieWord, lie_filteringOperator_D, Fin.sum_univ_three,
    wong_self, hw, hw', hiddenEulerScalar, hiddenSlopeCoordinate]
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.mul_apply,
    multiplication_apply, D, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_zero, Pi.add_apply,
    Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, smoothMul_apply,
    smoothOne, smul_eq_mul]
  ring

theorem hiddenShear_symm_hidden_vector (α β : ℝ) :
    (hiddenShear α β).symm (coordinateVector 2) = coordinateVector 2 := by
  funext i
  fin_cases i <;> simp [hiddenShear, hiddenShearLinear, coordinateVector]

theorem hiddenEulerLieWord_affine_frame (f : Fin 3 → Smooth) (V : Smooth)
    (p : Wong.AffineParameters) (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hμ : hiddenSlopeNorm p ≠ 0) (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) :
    affineConjugation (hiddenShear (hiddenSlopeAlpha p) (hiddenSlopeBeta p))
      ![0, 0, -hiddenSlopeDelta p] (hiddenEulerLieWord f V p) =
    hiddenEuler + multiplication
      (hiddenAffinePullback (hiddenSlopeAlpha p) (hiddenSlopeBeta p) (hiddenSlopeDelta p)
        (hiddenEulerScalar f V p)) := by
  rw [hiddenEulerLieWord_eq f V p hform hb₁ hb₂,
    map_add, map_mul, affineConjugation_multiplication,
    ← coordinate_directionalDerivative, affineConjugation_directionalDerivative,
    hiddenShear_symm_hidden_vector, coordinate_directionalDerivative,
    affineConjugation_multiplication, hiddenSlopeCoordinate_eq_affine f p hform hμ]
  rw [show affinePullback (hiddenShear (hiddenSlopeAlpha p) (hiddenSlopeBeta p))
      ![0, 0, -hiddenSlopeDelta p] =
      hiddenAffinePullback (hiddenSlopeAlpha p) (hiddenSlopeBeta p) (hiddenSlopeDelta p) from rfl,
    hiddenAffinePullback_coordinate]
  rfl

end Wong.SmoothModel
