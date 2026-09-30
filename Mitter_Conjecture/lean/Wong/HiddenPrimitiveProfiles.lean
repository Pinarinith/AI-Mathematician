import Wong.HiddenProfiles
import Wong.SmoothHiddenPrimitive

/-! The genuine global hidden primitive preserves dependence on the hidden
coordinate alone. The proof uses its actual integral value. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem partialDerivative_zero_of_hidden_profile (u : Smooth) (ψ : ℝ → ℝ)
    (hu : ∀ x : State, u.1 x = ψ (x 2)) (i : Fin 3) (hi : i ≠ 2) :
    partialDerivative i u = 0 := by
  apply Subtype.ext
  funext x
  have hconst : coordinateSlice u x i = fun _ => ψ (x 2) := by
    funext t
    rw [coordinateSlice, hu, Function.update_of_ne hi.symm]
  have he := congrFun (deriv_coordinateSlice u x i) (x i)
  rw [hconst, deriv_const] at he
  simpa only [coordinateSlice, Function.update_eq_self,
    Submodule.coe_zero, Pi.zero_apply] using he.symm

theorem hiddenPrimitive_visible_partials (q : Smooth)
    (h₀ : partialDerivative 0 q = 0) (h₁ : partialDerivative 1 q = 0) :
    partialDerivative 0 (hiddenPrimitive q) = 0 ∧
      partialDerivative 1 (hiddenPrimitive q) = 0 := by
  obtain ⟨ρ,_hρ,hq⟩ := exists_hidden_profile q h₀ h₁
  let ψ : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, ρ s
  have hp (x : State) : (hiddenPrimitive q).1 x = ψ (x 2) := by
    rw [hiddenPrimitive_value]
    have hs : coordinateSlice q x 2 = ρ := by
      funext t
      rw [coordinateSlice,hq]
      simp
    rw [hs]
  exact ⟨partialDerivative_zero_of_hidden_profile _ ψ hp 0 (by decide),
    partialDerivative_zero_of_hidden_profile _ ψ hp 1 (by decide)⟩

end Wong.SmoothModel
