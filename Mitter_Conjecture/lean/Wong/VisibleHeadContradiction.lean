import Wong.JacobiVisible

/-! The visible-head contradiction, now proved by Jacobi identities. -/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads

/-- Constant actual visible heads force the normalized slope to vanish.
The proof delegates to the actual-operator Jacobi argument and uses no
explicit potential derivative head formula. -/
theorem normalized_slope_zero_of_constant_heads {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (c₁ c : ℝ)
    (h11 : δ 1 (δ 1 (Y f h)) = multiplication (c₁ • smoothOne))
    (h01 : δ 0 (δ 1 (Y f h)) = multiplication (c • smoothOne)) : p.b₂ = 0 :=
  normalized_slope_zero_by_jacobi f h p hp hb₁ c₁ c h11 h01

end Wong.SmoothModel.VisibleHeads
