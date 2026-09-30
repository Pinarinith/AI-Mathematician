import Wong.EulerLinearLadder

/-!
# The canonical Sector-I linear Euler block

Every first commutator required by the actual order-doubling obstruction
is calculated here from the real partial derivatives and multiplication
operators. Smooth visible coefficients are unrestricted apart from their
stated independence of the hidden coordinate.
-/
noncomputable section
namespace Wong.SmoothModel
set_option maxHeartbeats 1200000

@[simp] theorem actual_mul_scalar_one (A : Operator) (c : ℝ) :
    A * (c • (1 : Operator)) = c • A := by
  apply LinearMap.ext
  intro u
  exact map_smul A c u

@[simp] theorem actual_scalar_one_mul (A : Operator) (c : ℝ) :
    (c • (1 : Operator)) * A = c • A := rfl

def visibleSlope (k l : ℝ) : Smooth :=
  k • linearFunction (coordinateVector 0) + l • linearFunction (coordinateVector 1)

def visibleSlopeDirection (k l : ℝ) : Operator :=
  k • partialDerivative 0 + l • partialDerivative 1

@[simp] theorem partial_zero_visibleSlope (k l : ℝ) :
    partialDerivative 0 (visibleSlope k l) = k • smoothOne := by
  simp [visibleSlope, partialDerivative_linearFunction, coordinateVector]

@[simp] theorem partial_one_visibleSlope (k l : ℝ) :
    partialDerivative 1 (visibleSlope k l) = l • smoothOne := by
  simp [visibleSlope, partialDerivative_linearFunction, coordinateVector]

@[simp] theorem partial_two_visibleSlope (k l : ℝ) :
    partialDerivative 2 (visibleSlope k l) = 0 := by
  simp [visibleSlope, partialDerivative_linearFunction, coordinateVector]

theorem hidden_independent_multiplier_commute (u : Smooth) (hu : partialDerivative 2 u = 0) :
    Commute (multiplication u) (partialDerivative 2) := by
  have hh := lie_partial_multiplication 2 u
  rw [hu, multiplication_zero] at hh
  exact (sub_eq_zero.mp hh).symm

/-- The visible second-order part, with arbitrary smooth visible coefficients. -/
def visibleDiffusionBlock (a₀ a₁ u₀ : Smooth) : Operator :=
  (1 / 2 : ℝ) • (partialDerivative 0 ^ 2 + partialDerivative 1 ^ 2) +
    multiplication a₀ * partialDerivative 0 +
    multiplication a₁ * partialDerivative 1 + multiplication u₀

def linearEulerBlock (k l c : ℝ) (a₀ a₁ u₀ : Smooth) : Operator :=
  visibleDiffusionBlock a₀ a₁ u₀ -
    (multiplication (visibleSlope k l) + c • 1) * hiddenEuler

def linearEulerFirstBracket (k l : ℝ) (a₀ a₁ : Smooth) : Operator :=
  visibleSlopeDirection k l + multiplication (k • a₀ + l • a₁)

theorem visibleDiffusionBlock_commute_hidden (a₀ a₁ u₀ : Smooth)
    (h₀ : partialDerivative 2 a₀ = 0) (h₁ : partialDerivative 2 a₁ = 0)
    (hu : partialDerivative 2 u₀ = 0) :
    Commute (visibleDiffusionBlock a₀ a₁ u₀) (partialDerivative 2) := by
  have hc₀ : Commute (partialDerivative 0) (partialDerivative 2) := partialDerivative_commute 0 2
  have hc₁ : Commute (partialDerivative 1) (partialDerivative 2) := partialDerivative_commute 1 2
  exact (((((hc₀.pow_left 2).add_left (hc₁.pow_left 2)).smul_left (1 / 2 : ℝ)).add_left
    ((hidden_independent_multiplier_commute a₀ h₀).mul_left hc₀)).add_left
    ((hidden_independent_multiplier_commute a₁ h₁).mul_left hc₁)).add_left
    (hidden_independent_multiplier_commute u₀ hu)

theorem linearEulerBlock_lie_hidden (k l c : ℝ) (a₀ a₁ u₀ : Smooth)
    (h₀ : partialDerivative 2 a₀ = 0) (h₁ : partialDerivative 2 a₁ = 0)
    (hu : partialDerivative 2 u₀ = 0) :
    ⁅linearEulerBlock k l c a₀ a₁ u₀, partialDerivative 2⁆ =
      (multiplication (visibleSlope k l) + c • 1) * partialDerivative 2 := by
  have hvis := actual_lie_zero_of_commute _ _ (visibleDiffusionBlock_commute_hidden a₀ a₁ u₀ h₀ h₁ hu)
  have hcoef : ⁅multiplication (visibleSlope k l) + c • (1 : Operator), partialDerivative 2⁆ = 0 := by
    apply actual_lie_zero_of_commute
    exact (hidden_independent_multiplier_commute _ (partial_two_visibleSlope k l)).add_left
      (actual_commute_scalar_identity (partialDerivative 2) c).symm
  rw [linearEulerBlock, sub_lie, hvis, zero_sub, operator_lie_mul_left,
    hcoef, zero_mul, add_zero, hiddenEuler_lie_partial]
  simp only [ite_true, neg_one_smul]
  apply LinearMap.ext
  intro u
  simp only [LinearMap.neg_apply, Module.End.mul_apply, map_neg, neg_neg]

theorem lie_partial_square_multiplier (i : Fin 3) (u : Smooth) :
    ⁅partialDerivative i ^ 2, multiplication u⁆ =
      (2 : ℝ) • (multiplication (partialDerivative i u) * partialDerivative i) +
        multiplication (partialDerivative i (partialDerivative i u)) := by
  simpa only [D, Pi.zero_apply, multiplication_zero, sub_zero, pow_two] using
    lie_D_square_multiplication (fun _ => 0) i u

theorem visibleDiffusionBlock_lie_slope (k l : ℝ) (a₀ a₁ u₀ : Smooth) :
    ⁅visibleDiffusionBlock a₀ a₁ u₀, multiplication (visibleSlope k l)⁆ =
      linearEulerFirstBracket k l a₀ a₁ := by
  simp only [visibleDiffusionBlock, add_lie, smul_lie, lie_partial_square_multiplier,
    partial_zero_visibleSlope, partial_one_visibleSlope, partialDerivative_const,
    multiplication_smul, multiplication_smoothOne, multiplication_zero, add_zero,
    actual_scalar_one_mul, operator_lie_mul_left, lie_partial_multiplication,
    lie_multiplication_multiplication, zero_mul, actual_mul_scalar_one,
    linearEulerFirstBracket, visibleSlopeDirection, multiplication_add]
  module

theorem linearEulerBlock_lie_slope (k l c : ℝ) (a₀ a₁ u₀ : Smooth) :
    ⁅linearEulerBlock k l c a₀ a₁ u₀, multiplication (visibleSlope k l)⁆ =
      linearEulerFirstBracket k l a₀ a₁ := by
  have hh : ⁅(multiplication (visibleSlope k l) + c • (1 : Operator)) * hiddenEuler,
      multiplication (visibleSlope k l)⁆ = 0 := by
    apply actual_lie_zero_of_commute
    exact ((Commute.refl _).add_left
      (actual_commute_scalar_identity (multiplication (visibleSlope k l)) c).symm).mul_left
      (hiddenEuler_commute_multiplier _ (partial_two_visibleSlope k l))
  rw [linearEulerBlock, sub_lie, hh, sub_zero, visibleDiffusionBlock_lie_slope]

theorem linearEulerFirstBracket_commute_hidden (k l : ℝ) (a₀ a₁ : Smooth)
    (h₀ : partialDerivative 2 a₀ = 0) (h₁ : partialDerivative 2 a₁ = 0) :
    Commute (linearEulerFirstBracket k l a₀ a₁) (partialDerivative 2) := by
  have hc₀ : Commute (partialDerivative 0) (partialDerivative 2) := partialDerivative_commute 0 2
  have hc₁ : Commute (partialDerivative 1) (partialDerivative 2) := partialDerivative_commute 1 2
  have hm : partialDerivative 2 (k • a₀ + l • a₁) = 0 := by simp [h₀, h₁]
  exact ((hc₀.smul_left k).add_left (hc₁.smul_left l)).add_left
    (hidden_independent_multiplier_commute _ hm)

theorem visibleSlope_lie_linearEulerFirstBracket (k l : ℝ) (a₀ a₁ : Smooth) :
    ⁅multiplication (visibleSlope k l), linearEulerFirstBracket k l a₀ a₁⁆ =
      -(k ^ 2 + l ^ 2) • (1 : Operator) := by
  have hrev : ⁅linearEulerFirstBracket k l a₀ a₁, multiplication (visibleSlope k l)⁆ =
      (k ^ 2 + l ^ 2) • (1 : Operator) := by
    simp only [linearEulerFirstBracket, visibleSlopeDirection, add_lie, smul_lie,
      lie_multiplication_multiplication, add_zero, lie_partial_multiplication,
      partial_zero_visibleSlope, partial_one_visibleSlope, multiplication_smul,
      multiplication_smoothOne, smul_smul]
    module
  rw [← lie_skew, hrev]
  exact (neg_smul _ _).symm

/-- Complete actual Sector-I linear-slope contradiction: no formal symbol
or unproved bracket hypothesis remains in this theorem. -/
theorem linearEulerBlock_visible_slopes_zero
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (k l c : ℝ) (a₀ a₁ u₀ : Smooth)
    (h₀ : partialDerivative 2 a₀ = 0) (h₁ : partialDerivative 2 a₁ = 0)
    (hu : partialDerivative 2 u₀ = 0)
    (hLE : linearEulerBlock k l c a₀ a₁ u₀ ∈ E)
    (hPE : partialDerivative 2 ^ 2 ∈ E) : k = 0 ∧ l = 0 := by
  have hz := actual_linear_euler_ladder_obstruction E hfinite
    (linearEulerBlock k l c a₀ a₁ u₀) (multiplication (visibleSlope k l))
    (linearEulerFirstBracket k l a₀ a₁) c (k ^ 2 + l ^ 2) hLE hPE
    (linearEulerBlock_lie_hidden k l c a₀ a₁ u₀ h₀ h₁ hu)
    (linearEulerBlock_lie_slope k l c a₀ a₁ u₀)
    (hidden_independent_multiplier_commute _ (partial_two_visibleSlope k l))
    (linearEulerFirstBracket_commute_hidden k l a₀ a₁ h₀ h₁)
    (visibleSlope_lie_linearEulerFirstBracket k l a₀ a₁)
  constructor <;> nlinarith [sq_nonneg k, sq_nonneg l]

end Wong.SmoothModel
