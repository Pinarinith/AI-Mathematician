import Wong.VisibleGeneratorHeads

/-! The actual mixed-derivative contradiction after the two visible heads are constant. -/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads

/-- Equality of the actual constant heads of the generator word forces the
normalized visible slope to vanish. The fourth derivative of the potential
cancels by genuine symmetry of smooth partial derivatives. -/
theorem normalized_slope_zero_of_constant_heads {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (c₁ c : ℝ)
    (h11 : δ 1 (δ 1 (Y f h)) = multiplication (c₁ • smoothOne))
    (h01 : δ 0 (δ 1 (Y f h)) = multiplication (c • smoothOne)) : p.b₂ = 0 := by
  have he11 := multiplication_injective ((head11 f h p hp).symm.trans h11)
  have he01 := multiplication_injective ((head01 f h p hp).symm.trans h01)
  have hd11 := congrArg (partialDerivative 0) he11
  have hd01 := congrArg (partialDerivative 1) he01
  have hone (i : Fin 3) : partialDerivative i smoothOne = 0 := by
    simpa only [one_smul] using partialDerivative_const i 1
  simp only [map_add, map_smul, hone, smul_zero, partial_wong_affine f p hp] at hd11 hd01
  rw [partialDerivative_commute_apply 1 0 (partialDerivative 0 (partialDerivative 1 (eta f h))),
    partialDerivative_commute_apply 1 0 (partialDerivative 1 (eta f h))] at hd01
  have hv11 := congrArg (fun u : Smooth => u.1 (0 : State)) hd11
  have hv01 := congrArg (fun u : Smooth => u.1 (0 : State)) hd01
  simp [slopes, smoothOne, hb₁, bianchi_slopes f p hp] at hv11 hv01
  nlinarith [sq_nonneg p.b₂]

end Wong.SmoothModel.VisibleHeads
