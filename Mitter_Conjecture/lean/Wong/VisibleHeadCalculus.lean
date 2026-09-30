import Wong.CovariantWords
import Wong.SharpDifferentialOrder
import Wong.PublishedAffineStatement

/-! Genuine commutator calculus for the visible generator heads. -/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads

def slopes (p : Wong.AffineParameters) : Fin 3 → Fin 3 → State :=
  !![0, ![p.b₁, p.b₂, 0], ![p.k₁, p.k₂, p.k₃];
    -![p.b₁, p.b₂, 0], 0, ![p.h₁, p.h₂, p.h₃];
    -![p.k₁, p.k₂, p.k₃], -![p.h₁, p.h₂, p.h₃], 0]

def constants (p : Wong.AffineParameters) : Fin 3 → Fin 3 → ℝ :=
  !![0, p.b₀, p.k₀; -p.b₀, 0, p.h₀; -p.k₀, -p.h₀, 0]

theorem wong_affine_eq (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) (i j : Fin 3) :
    wong f i j = constants p i j • smoothOne + linearFunction (slopes p i j) := by
  apply Subtype.ext
  funext x
  rw [hp]
  fin_cases i <;> fin_cases j <;>
    simp [constants, slopes, smoothOne, linearFunction, Wong.AffineParameters.matrix,
      Wong.AffineParameters.w12, Wong.AffineParameters.w13, Wong.AffineParameters.w23,
      Fin.sum_univ_three] <;> ring

theorem partial_wong_affine (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) (k i j : Fin 3) :
    partialDerivative k (wong f i j) = slopes p i j k • smoothOne := by
  rw [wong_affine_eq f p hp i j, map_add, partialDerivative_const,
    partialDerivative_linearFunction, zero_add]

theorem partial_partial_wong_affine (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) (k l i j : Fin 3) :
    partialDerivative k (partialDerivative l (wong f i j)) = 0 := by
  rw [partial_wong_affine f p hp, partialDerivative_const]

theorem bianchi_slopes (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) : p.h₁ = p.k₂ := by
  have hb := wong_bianchi f 0 1 2
  simp only [partial_wong_affine f p hp] at hb
  have hz := congrArg (fun u : Smooth => u.1 (0 : State)) hb
  have hz' : -p.k₂ + p.h₁ = 0 := by simpa [slopes, smoothOne] using hz
  linarith

theorem partial_generatorRemainder {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (r i : Fin 3) :
    partialDerivative i (generatorRemainder f h r) =
      (1 / 2 : ℝ) • partialDerivative i (partialDerivative r (eta f h)) := by
  simp only [generatorRemainder, map_smul, map_add, map_sum,
    partial_partial_wong_affine f p hp, Finset.sum_const_zero, zero_add]

theorem partial_partial_generatorRemainder {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) (r i j : Fin 3) :
    partialDerivative i (partialDerivative j (generatorRemainder f h r)) =
      (1 / 2 : ℝ) • partialDerivative r (partialDerivative i (partialDerivative j (eta f h))) := by
  rw [partial_generatorRemainder f h p hp, map_smul,
    partialDerivative_commute_apply j r, partialDerivative_commute_apply i r]

def δ (i : Fin 3) : Module.End ℝ Operator :=
  commuteWithMultiplier (linearFunction (coordinateVector i))

@[simp] theorem δ_multiplication (i : Fin 3) (u : Smooth) : δ i (multiplication u) = 0 :=
  lie_multiplication_multiplication u _

@[simp] theorem δ_D (f : Fin 3 → Smooth) (i j : Fin 3) :
    δ i (D f j) = coordinateVector i j • (1 : Operator) := by
  simp only [δ, commuteWithMultiplier_apply, lie_D_multiplication,
    partialDerivative_linearFunction, multiplication_smul, multiplication_smoothOne]

@[simp] theorem δ_L0 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) (i : Fin 3) :
    δ i (L0 f h) = D f i := by
  simp only [δ, commuteWithMultiplier_apply, lie_L0_linearFunction, directionD,
    coordinateVector, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem δ_lie_L0 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3) (A : Operator) :
    δ i ⁅L0 f h, A⁆ = ⁅L0 f h, δ i A⁆ + ⁅D f i, A⁆ := by
  change commuteWithMultiplier (linearFunction (coordinateVector i)) ⁅L0 f h, A⁆ = _
  rw [commuteWithMultiplier_lie]
  change ⁅L0 f h, δ i A⁆ + ⁅δ i (L0 f h), A⁆ = _
  rw [δ_L0]

theorem δ_lie_D (f : Fin 3 → Smooth) (i j : Fin 3) (A : Operator) :
    δ i ⁅D f j, A⁆ = ⁅D f j, δ i A⁆ := by
  rw [δ, commuteWithMultiplier_lie]
  change ⁅D f j, δ i A⁆ + ⁅δ i (D f j), A⁆ = ⁅D f j, δ i A⁆
  rw [δ_D, scalar_identity_lie, add_zero]

theorem operator_lie_mul_right (A B C : Operator) :
    ⁅A, B * C⁆ = ⁅A, B⁆ * C + B * ⁅A, C⁆ := by
  apply LinearMap.ext
  intro u
  change A (B (C u)) - B (C (A u)) =
    (A (B (C u)) - B (A (C u))) + B (A (C u) - C (A u))
  rw [map_sub]
  abel

theorem lie_D_firstOrder (f a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    ⁅D f i, firstOrder f a b⁆ =
      firstOrder f (fun j => partialDerivative i (a j))
        ((∑ j, smoothMul (a j) (wong f j i)) + partialDerivative i b) := by
  simp only [firstOrder, lie_add, lie_sum, operator_lie_mul_right,
    lie_D_multiplication, lie_D_D, multiplication_mul, multiplication_add,
    multiplication_sum, Finset.sum_add_distrib]
  abel

@[simp] theorem firstOrder_zero (f : Fin 3 → Smooth) (b : Smooth) :
    firstOrder f (fun _ => 0) b = multiplication b := by
  simp [firstOrder]

@[simp] theorem δ_firstOrder (f a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    δ i (firstOrder f a b) = multiplication (a i) := by
  rw [δ, commuteWithLinear_firstOrder, coefficientAlong_coordinate]

theorem lie_L0_multiplication_affine {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (a : Smooth) (s : State) (ha : ∀ j, partialDerivative j a = s j • smoothOne) :
    ⁅L0 f h, multiplication a⁆ = ∑ j, s j • D f j := by
  rw [lie_L0_multiplication]
  simp only [ha, partialDerivative_const, Finset.sum_const_zero, multiplication_zero,
    smul_zero, add_zero, multiplication_smul, multiplication_smoothOne, smul_mul_assoc, one_mul]

def H {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) : Operator := ⁅L0 f h, D f 0⁆
def X {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) : Operator := ⁅L0 f h, H f h⁆
def Y {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) : Operator := ⁅L0 f h, X f h⁆

theorem H_eq_firstOrder {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    H f h = firstOrder f (wong f 0) (generatorRemainder f h 0) := lie_L0_D_eq_firstOrder f h 0

theorem δ_H {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) (i : Fin 3) :
    δ i (H f h) = multiplication (wong f 0 i) := by
  rw [H_eq_firstOrder, δ_firstOrder]

def remainderX {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) (i : Fin 3) : Smooth :=
  (∑ j, smoothMul (wong f 0 j) (wong f j i)) +
    partialDerivative i (generatorRemainder f h 0)

theorem δ_X {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (i : Fin 3) :
    δ i (X f h) = firstOrder f
      (fun j => partialDerivative j (wong f 0 i) + partialDerivative i (wong f 0 j))
      (remainderX f h i) := by
  rw [X, δ_lie_L0, δ_H, H_eq_firstOrder, lie_D_firstOrder, lie_L0_multiplication]
  simp only [partial_partial_wong_affine f p hp, Finset.sum_const_zero,
    multiplication_zero, smul_zero, add_zero, firstOrder, multiplication_add,
    add_mul, Finset.sum_add_distrib, remainderX]
  abel

theorem δ_δ_X {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (i j : Fin 3) :
    δ i (δ j (X f h)) = multiplication
      ((slopes p 0 j i + slopes p 0 i j) • smoothOne) := by
  rw [δ_X f h p hp, δ_firstOrder]
  simp only [partial_wong_affine f p hp, add_smul]

def doubleHead {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i j : Fin 3) : Smooth :=
  ((∑ k, smoothMul (partialDerivative k (wong f 0 j) + partialDerivative j (wong f 0 k))
      (wong f k i)) + partialDerivative i (remainderX f h j)) +
  ((∑ k, smoothMul (partialDerivative k (wong f 0 i) + partialDerivative i (wong f 0 k))
      (wong f k j)) + partialDerivative j (remainderX f h i))

theorem δ_δ_Y {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (i j : Fin 3) :
    δ i (δ j (Y f h)) = multiplication (doubleHead f h i j) := by
  rw [Y, δ_lie_L0, map_add, δ_lie_L0, δ_lie_D, δ_δ_X f h p hp]
  simp only [multiplication_smul, multiplication_smoothOne, lie_scalar_identity,
    zero_add, δ_X f h p hp, lie_D_firstOrder, map_add,
    partial_partial_wong_affine f p hp, zero_add, firstOrder_zero,
    doubleHead, multiplication_add]

end Wong.SmoothModel.VisibleHeads
