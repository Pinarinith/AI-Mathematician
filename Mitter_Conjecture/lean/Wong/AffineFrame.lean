import Wong.OrthogonalCoordinates
import Wong.NormalFormAlgebra
import Wong.DifferentialOrder

/-!
# Genuine global affine coordinate frames

The hidden coordinate t=x₂+αx₀+βx₁+δ is a global affine coordinate.
The associated pullback is an actual linear equivalence of smooth
functions and its conjugation is an actual Lie-algebra equivalence.
No orthogonality claim is made for this shear.
-/

noncomputable section
namespace Wong.SmoothModel

def affinePullback (e : State ≃L[ℝ] State) (b : State) : Smooth ≃ₗ[ℝ] Smooth where
  toFun u := ⟨fun x => u.1 (e x + b), (smooth u).comp (e.contDiff.add contDiff_const)⟩
  invFun u := ⟨fun x => u.1 (e.symm (x - b)),
    (smooth u).comp (e.symm.contDiff.comp (contDiff_id.sub contDiff_const))⟩
  left_inv u := by
    apply Subtype.ext
    funext x
    simp
  right_inv u := by
    apply Subtype.ext
    funext x
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem affinePullback_apply (e : State ≃L[ℝ] State) (b : State)
    (u : Smooth) (x : State) : (affinePullback e b u).1 x = u.1 (e x + b) := rfl

theorem affinePullback_symm (e : State ≃L[ℝ] State) (b : State) :
    (affinePullback e b).symm = affinePullback e.symm (-e.symm b) := by
  ext u x
  simp [affinePullback, sub_eq_add_neg]

theorem directionalDerivative_affinePullback (e : State ≃L[ℝ] State)
    (b v : State) (u : Smooth) :
    directionalDerivative v (affinePullback e b u) =
      affinePullback e b (directionalDerivative (e v) u) := by
  apply Subtype.ext
  funext x
  rw [directionalDerivative_apply, affinePullback_apply, directionalDerivative_apply]
  change fderiv ℝ (u.1 ∘ (fun y => e y + b)) x v = _
  rw [fderiv_comp x (((smooth u).differentiable (by simp)).differentiableAt)
    (e.differentiableAt.add_const b), fderiv_add_const, e.fderiv]
  rfl

def affineConjugation (e : State ≃L[ℝ] State) (b : State) : Operator ≃ₐ[ℝ] Operator :=
  (affinePullback e b).conjAlgEquiv ℝ

def affineLieEquiv (e : State ≃L[ℝ] State) (b : State) : Operator ≃ₗ⁅ℝ⁆ Operator :=
  (affineConjugation e b).toLieEquiv

@[simp] theorem affineConjugation_apply (e : State ≃L[ℝ] State) (b : State)
    (A : Operator) (u : Smooth) : affineConjugation e b A u =
      affinePullback e b (A ((affinePullback e b).symm u)) := rfl

@[simp] theorem affineConjugation_multiplication (e : State ≃L[ℝ] State)
    (b : State) (u : Smooth) : affineConjugation e b (multiplication u) =
      multiplication (affinePullback e b u) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext x
  change u.1 (e x + b) * v.1 (e.symm (e x + b - b)) = u.1 (e x + b) * v.1 x
  simp

@[simp] theorem affineConjugation_directionalDerivative (e : State ≃L[ℝ] State)
    (b v : State) : affineConjugation e b (directionalDerivative v) =
      directionalDerivative (e.symm v) := by
  apply LinearMap.ext
  intro u
  rw [affineConjugation_apply, affinePullback_symm, directionalDerivative_affinePullback,
    ← affinePullback_symm]
  exact (affinePullback e b).apply_symm_apply _

def hiddenShearLinear (α β : ℝ) : State ≃ₗ[ℝ] State where
  toFun x := ![x 0, x 1, x 2 - α * x 0 - β * x 1]
  invFun x := ![x 0, x 1, x 2 + α * x 0 + β * x 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp
    all_goals ring
  right_inv x := by
    funext i
    fin_cases i <;> simp
    all_goals ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp
    all_goals ring

def hiddenShear (α β : ℝ) : State ≃L[ℝ] State :=
  (hiddenShearLinear α β).toContinuousLinearEquiv

def hiddenAffinePullback (α β δ : ℝ) : Smooth ≃ₗ[ℝ] Smooth :=
  affinePullback (hiddenShear α β) ![0, 0, -δ]

def hiddenAffineCoordinate (α β δ : ℝ) : Smooth :=
  linearFunction ![α, β, 1] + δ • smoothOne

theorem hiddenAffinePullback_coordinate (α β δ : ℝ) :
    hiddenAffinePullback α β δ (hiddenAffineCoordinate α β δ) =
      linearFunction (coordinateVector 2) := by
  apply Subtype.ext
  funext x
  simp [hiddenAffinePullback, hiddenAffineCoordinate, affinePullback_apply,
    hiddenShear, hiddenShearLinear, linearFunction, smoothOne, coordinateVector,
    Fin.sum_univ_three]
  ring

theorem hiddenAffinePullback_visible_coordinate (α β δ : ℝ) (i : Fin 3)
    (hi : i ≠ 2) : hiddenAffinePullback α β δ (linearFunction (coordinateVector i)) =
      linearFunction (coordinateVector i) := by
  apply Subtype.ext
  funext x
  fin_cases i <;>
    simp_all [hiddenAffinePullback, affinePullback_apply, hiddenShear, hiddenShearLinear,
      linearFunction, coordinateVector, Fin.sum_univ_three]

end Wong.SmoothModel
