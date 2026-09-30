import Wong.FunctionElements
import Wong.AffineFrame

/-! Actual smooth dependence on only the hidden coordinate, including after a global affine shear. -/

noncomputable section
namespace Wong.SmoothModel
open scoped ContDiff

theorem smooth_update_eq_of_partial_zero (u : Smooth) (i : Fin 3)
    (hz : partialDerivative i u = 0) (x : State) (t : ℝ) :
    u.1 (Function.update x i t) = u.1 x := by
  have hd (s : ℝ) : deriv (coordinateSlice u x i) s = 0 := by
    rw [deriv_coordinateSlice, hz]
    rfl
  have he := is_const_of_deriv_eq_zero
    ((coordinateSlice_smooth u x i).differentiable (by simp)) hd t (x i)
  simpa only [coordinateSlice, Function.update_eq_self] using he

theorem exists_hidden_profile (u : Smooth)
    (h₀ : partialDerivative 0 u = 0) (h₁ : partialDerivative 1 u = 0) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ ∀ x : State, u.1 x = ρ (x 2) := by
  refine ⟨coordinateSlice u 0 2, coordinateSlice_smooth u 0 2, ?_⟩
  intro x
  have he : Function.update (Function.update x 0 0) 1 0 =
      Function.update (0 : State) 2 (x 2) := by
    funext i
    fin_cases i <;> simp
  calc
    u.1 x = u.1 (Function.update x 0 0) := (smooth_update_eq_of_partial_zero u 0 h₀ x 0).symm
    _ = u.1 (Function.update (Function.update x 0 0) 1 0) :=
      (smooth_update_eq_of_partial_zero u 1 h₁ (Function.update x 0 0) 0).symm
    _ = _ := by rw [he]; rfl

theorem exists_slanted_hidden_profile (u : Smooth) (α β δ : ℝ)
    (h₀ : directionalDerivative (coordinateVector 0 + α • coordinateVector 2) u = 0)
    (h₁ : directionalDerivative (coordinateVector 1 + β • coordinateVector 2) u = 0) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧
      ∀ x : State, u.1 x = ρ (x 2 - α * x 0 - β * x 1 - δ) := by
  let e := hiddenShear (-α) (-β)
  let b : State := ![0, 0, δ]
  let v := affinePullback e b u
  have he₀ : e (coordinateVector 0) = coordinateVector 0 + α • coordinateVector 2 := by
    funext i
    fin_cases i <;> simp [e, hiddenShear, hiddenShearLinear, coordinateVector]
  have he₁ : e (coordinateVector 1) = coordinateVector 1 + β • coordinateVector 2 := by
    funext i
    fin_cases i <;> simp [e, hiddenShear, hiddenShearLinear, coordinateVector]
  have hv₀ : partialDerivative 0 v = 0 := by
    rw [← coordinate_directionalDerivative, directionalDerivative_affinePullback,
      he₀, h₀, map_zero]
  have hv₁ : partialDerivative 1 v = 0 := by
    rw [← coordinate_directionalDerivative, directionalDerivative_affinePullback,
      he₁, h₁, map_zero]
  obtain ⟨ρ, hρ, hr⟩ := exists_hidden_profile v hv₀ hv₁
  refine ⟨ρ, hρ, ?_⟩
  intro x
  have hx := hr (e.symm (x - b))
  have hv : v.1 (e.symm (x - b)) = u.1 x := by
    simp [v, affinePullback_apply]
  have hc : (e.symm (x - b)) 2 = x 2 - α * x 0 - β * x 1 - δ := by
    simp [e, b, hiddenShear, hiddenShearLinear, Matrix.vecHead, Matrix.vecTail]
    all_goals ring
  rw [hv, hc] at hx
  exact hx

end Wong.SmoothModel
