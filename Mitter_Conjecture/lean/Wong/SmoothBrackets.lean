import Wong.MainStatement
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.NoncommRing

/-!
# Genuine smooth differential-operator brackets

All operators in this file act on the globally smooth functions from
`MainStatement`. The assertions below are identities of actual linear
endomorphisms, not of formal symbols or an assumed operator calculus.
-/

noncomputable section
namespace Wong.SmoothModel
open scoped ContDiff

@[simp] theorem smoothMul_apply (u v : Smooth) (x : State) :
    (smoothMul u v).1 x = u.1 x * v.1 x := rfl

@[simp] theorem multiplication_apply (u v : Smooth) :
    multiplication u v = smoothMul u v := rfl

@[simp] theorem smoothMul_one (u : Smooth) : smoothMul u smoothOne = u := by
  apply Subtype.ext
  funext x
  exact mul_one (u.1 x)

theorem smoothMul_comm (u v : Smooth) : smoothMul u v = smoothMul v u := by
  apply Subtype.ext
  funext x
  exact mul_comm (u.1 x) (v.1 x)

theorem smoothMul_assoc (u v w : Smooth) :
    smoothMul (smoothMul u v) w = smoothMul u (smoothMul v w) := by
  apply Subtype.ext
  funext x
  exact mul_assoc (u.1 x) (v.1 x) (w.1 x)

@[simp] theorem multiplication_add (u v : Smooth) :
    multiplication (u + v) = multiplication u + multiplication v := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext x
  exact add_mul (u.1 x) (v.1 x) (w.1 x)

@[simp] theorem multiplication_smul (c : ℝ) (u : Smooth) :
    multiplication (c • u) = c • multiplication u := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext x
  exact mul_assoc c (u.1 x) (w.1 x)

@[simp] theorem multiplication_zero : multiplication 0 = 0 := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext x
  exact zero_mul (w.1 x)

@[simp] theorem multiplication_sub (u v : Smooth) :
    multiplication (u - v) = multiplication u - multiplication v := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext x
  exact sub_mul (u.1 x) (v.1 x) (w.1 x)

/-- Multiplication by a scalar function is a linear embedding into actual operators. -/
def multiplicationLinear : Smooth →ₗ[ℝ] Operator where
  toFun := multiplication
  map_add' := multiplication_add
  map_smul' := multiplication_smul

theorem multiplication_injective : Function.Injective multiplication := by
  intro u v huv
  have h := congrArg (fun A : Operator => A smoothOne) huv
  simpa using h

@[simp] theorem multiplication_mul (u v : Smooth) :
    multiplication u * multiplication v = multiplication (smoothMul u v) := by
  apply LinearMap.ext
  intro w
  exact (smoothMul_assoc u v w).symm

theorem multiplication_commute (u v : Smooth) :
    multiplication u * multiplication v = multiplication v * multiplication u := by
  rw [multiplication_mul, multiplication_mul, smoothMul_comm]

@[simp] theorem lie_multiplication_multiplication (u v : Smooth) :
    ⁅multiplication u, multiplication v⁆ = 0 := by
  change multiplication u * multiplication v - multiplication v * multiplication u = 0
  rw [multiplication_commute, sub_self]

theorem partialDerivative_smoothMul (i : Fin 3) (u v : Smooth) :
    partialDerivative i (smoothMul u v) =
      smoothMul (partialDerivative i u) v + smoothMul u (partialDerivative i v) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun y => u.1 y * v.1 y) x (coordinateVector i) = _
  rw [fderiv_fun_mul
    (((smooth u).differentiable (by simp)).differentiableAt)
    (((smooth v).differentiable (by simp)).differentiableAt)]
  change u.1 x * fderiv ℝ v.1 x (coordinateVector i) +
    v.1 x * fderiv ℝ u.1 x (coordinateVector i) =
      fderiv ℝ u.1 x (coordinateVector i) * v.1 x +
      u.1 x * fderiv ℝ v.1 x (coordinateVector i)
  ring

theorem lie_partial_multiplication (i : Fin 3) (u : Smooth) :
    ⁅partialDerivative i, multiplication u⁆ = multiplication (partialDerivative i u) := by
  apply LinearMap.ext
  intro v
  change partialDerivative i (smoothMul u v) - smoothMul u (partialDerivative i v) = _
  rw [partialDerivative_smoothMul, add_sub_cancel_right]
  rfl

/-- The partial derivatives commute because the second Fréchet derivative is symmetric. -/
theorem partialDerivative_commute_apply (i j : Fin 3) (u : Smooth) :
    partialDerivative i (partialDerivative j u) =
      partialDerivative j (partialDerivative i u) := by
  apply Subtype.ext
  funext x
  have hdf : DifferentiableAt ℝ (fderiv ℝ u.1) x :=
    (((contDiff_infty_iff_fderiv.mp (smooth u)).2).differentiable (by simp)).differentiableAt
  change fderiv ℝ (fun y => fderiv ℝ u.1 y (coordinateVector j)) x
      (coordinateVector i) =
    fderiv ℝ (fun y => fderiv ℝ u.1 y (coordinateVector i)) x
      (coordinateVector j)
  rw [fderiv_clm_apply hdf (differentiableAt_const (coordinateVector j)),
    fderiv_clm_apply hdf (differentiableAt_const (coordinateVector i))]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact ((smooth u).contDiffAt.isSymmSndFDerivAt (by simp))
    (coordinateVector i) (coordinateVector j)

theorem partialDerivative_commute (i j : Fin 3) :
    partialDerivative i * partialDerivative j = partialDerivative j * partialDerivative i := by
  apply LinearMap.ext
  exact partialDerivative_commute_apply i j

@[simp] theorem lie_partial_partial (i j : Fin 3) :
    ⁅partialDerivative i, partialDerivative j⁆ = 0 := by
  change partialDerivative i * partialDerivative j - partialDerivative j * partialDerivative i = 0
  rw [partialDerivative_commute, sub_self]

theorem lie_D_multiplication (f : Fin 3 → Smooth) (i : Fin 3) (u : Smooth) :
    ⁅D f i, multiplication u⁆ = multiplication (partialDerivative i u) := by
  simp [D, sub_lie, lie_partial_multiplication]

theorem lie_D_D (f : Fin 3 → Smooth) (i j : Fin 3) :
    ⁅D f j, D f i⁆ = multiplication (wong f i j) := by
  simp only [D, sub_lie, lie_sub, lie_partial_partial,
    lie_partial_multiplication, lie_multiplication_multiplication, sub_zero, zero_sub]
  rw [lie_skew, lie_partial_multiplication]
  simp only [wong, multiplication_sub]

theorem operator_lie_def (A B : Operator) : ⁅A, B⁆ = A * B - B * A := rfl

theorem operator_lie_mul_left (A B C : Operator) :
    ⁅A * B, C⁆ = A * ⁅B, C⁆ + ⁅A, C⁆ * B := by
  apply LinearMap.ext
  intro v
  change A (B (C v)) - C (A (B v)) =
    A (B (C v) - C (B v)) + (A (C (B v)) - C (A (B v)))
  rw [map_sub]
  abel

theorem D_mul_multiplication (f : Fin 3 → Smooth) (i : Fin 3) (u : Smooth) :
    D f i * multiplication u =
      multiplication u * D f i + multiplication (partialDerivative i u) := by
  have h := lie_D_multiplication f i u
  rw [operator_lie_def] at h
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)

theorem lie_D_square_multiplication (f : Fin 3 → Smooth) (i : Fin 3) (u : Smooth) :
    ⁅D f i * D f i, multiplication u⁆ =
      (2 : ℝ) • (multiplication (partialDerivative i u) * D f i) +
        multiplication (partialDerivative i (partialDerivative i u)) := by
  rw [operator_lie_mul_left, lie_D_multiplication, D_mul_multiplication]
  simp only [two_smul]
  abel

@[simp] theorem multiplication_sum {ι : Type*} [Fintype ι] (u : ι → Smooth) :
    multiplication (∑ i, u i) = ∑ i, multiplication (u i) :=
  map_sum multiplicationLinear u Finset.univ

/-- The exact generator/multiplier commutator, in the manuscript's normalization. -/
theorem lie_L0_multiplication {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (u : Smooth) :
    ⁅L0 f h, multiplication u⁆ =
      (∑ i, multiplication (partialDerivative i u) * D f i) +
        (1 / 2 : ℝ) • multiplication (∑ i, partialDerivative i (partialDerivative i u)) := by
  simp only [L0, sub_lie, smul_lie, lie_multiplication_multiplication,
    smul_zero, sub_zero, sum_lie, lie_D_square_multiplication,
    Finset.smul_sum, smul_add, smul_smul, multiplication_sum]
  norm_num
  rw [Finset.sum_add_distrib]

/-- The true carré-du-champ identity; all zero-order potential and drift terms cancel. -/
theorem double_lie_L0_multiplication {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (u v : Smooth) :
    ⁅⁅L0 f h, multiplication u⁆, multiplication v⁆ =
      multiplication (∑ i, smoothMul (partialDerivative i u) (partialDerivative i v)) := by
  rw [lie_L0_multiplication]
  simp only [add_lie, sum_lie, smul_lie, lie_multiplication_multiplication,
    Finset.sum_const_zero, smul_zero, add_zero, operator_lie_mul_left, lie_D_multiplication,
    zero_mul, add_zero, multiplication_mul, multiplication_sum]

/-- The antisymmetric Wong entries satisfy the actual smooth Bianchi identity. -/
theorem wong_bianchi (f : Fin 3 → Smooth) (i j k : Fin 3) :
    partialDerivative k (wong f i j) - partialDerivative j (wong f i k) +
      partialDerivative i (wong f j k) = 0 := by
  simp only [wong, map_sub]
  rw [partialDerivative_commute_apply k i, partialDerivative_commute_apply k j,
    partialDerivative_commute_apply j i]
  abel

end Wong.SmoothModel
