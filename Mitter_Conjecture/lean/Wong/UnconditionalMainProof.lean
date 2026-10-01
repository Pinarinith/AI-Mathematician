import Wong.MainProof

/-! Compatibility names for the public main theorem, which already has no
quadratic-freeness premise. -/
noncomputable section
namespace Wong.SmoothModel

/-- The original smooth rank-two Wong conclusion with no quadratic-free premise. -/
abbrev UnconditionalMainClaim : Prop := mainClaim

theorem unconditional_main_theorem : UnconditionalMainClaim := main_theorem

theorem omega12_constant_without_quadraticFree {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2) :
    ∃ c : ℝ, ∀ x : State, (wong f 0 1).1 x = c := by
  obtain ⟨Ω, hΩ⟩ := unconditional_main_theorem m f h inferInstance hrank
  exact ⟨Ω 0 1, hΩ 0 1⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.unconditional_main_theorem
#print axioms Wong.SmoothModel.omega12_constant_without_quadraticFree
