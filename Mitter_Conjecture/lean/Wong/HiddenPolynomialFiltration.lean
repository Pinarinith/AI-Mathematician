import Wong.NormalForm

/-!
# Uniform hidden polynomial degree for actual normal forms

Polynomial dependence in the hidden variable is expressed by nilpotence of
the genuine third partial derivative on each coefficient. Finite dimensionality
gives a uniform bound on the subspace with that property; no assumption that
the whole estimation algebra has hidden polynomial coefficients is made.
-/

noncomputable section
namespace Wong.SmoothModel

theorem end_power_zero_mono (P : Operator) (u : Smooth) {m n : ℕ}
    (hmn : m ≤ n) (hm : (P ^ m) u = 0) : (P ^ n) u = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_comm m d, pow_add]
  change (P ^ d) ((P ^ m) u) = 0
  rw [hm, map_zero]

def hiddenCoefficientFiltration (n : ℕ) : Submodule ℝ NormalForm :=
  ⨅ α : MultiIndex, ((partialDerivative 2 ^ n).ker).comap (Finsupp.lapply α)

theorem mem_hiddenCoefficientFiltration (p : NormalForm) (n : ℕ) :
    p ∈ hiddenCoefficientFiltration n ↔ ∀ α, (partialDerivative 2 ^ n) (p α) = 0 := by
  simp [hiddenCoefficientFiltration, Submodule.mem_iInf, Finsupp.lapply_apply]

theorem hiddenCoefficientFiltration_monotone : Monotone hiddenCoefficientFiltration := by
  intro m n hmn p hp
  rw [mem_hiddenCoefficientFiltration] at hp ⊢
  intro α
  exact end_power_zero_mono _ _ hmn (hp α)

/-- Finitely many nonzero coefficients give a common hidden-degree bound
for one normal form. -/
theorem exists_hiddenCoefficientFiltration (p : NormalForm)
    (hp : ∀ α, ∃ n, (partialDerivative 2 ^ n) (p α) = 0) :
    ∃ n, p ∈ hiddenCoefficientFiltration n := by
  classical
  choose n hn using hp
  refine ⟨p.support.sup n, (mem_hiddenCoefficientFiltration _ _).mpr ?_⟩
  intro α
  by_cases hα : α ∈ p.support
  · exact end_power_zero_mono _ _ (Finset.le_sup hα) (hn α)
  · rw [Finsupp.notMem_support_iff.mp hα, map_zero]

def hiddenPolynomialForms : Submodule ℝ NormalForm where
  carrier := {p | ∃ n, p ∈ hiddenCoefficientFiltration n}
  zero_mem' := ⟨0, (hiddenCoefficientFiltration 0).zero_mem⟩
  add_mem' := by
    rintro p q ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨max m n, (hiddenCoefficientFiltration (max m n)).add_mem
      (hiddenCoefficientFiltration_monotone (le_max_left _ _) hm)
      (hiddenCoefficientFiltration_monotone (le_max_right _ _) hn)⟩
  smul_mem' := by
    rintro c p ⟨n, hn⟩
    exact ⟨n, (hiddenCoefficientFiltration n).smul_mem c hn⟩

/-- Finite generators bound a monotone filtration; its differential operator
need not preserve the finite-dimensional space. -/
theorem finiteDimensional_uniform_hiddenFiltration (V : Submodule ℝ NormalForm)
    [Module.Finite ℝ V] (hV : V ≤ hiddenPolynomialForms) :
    ∃ n, V ≤ hiddenCoefficientFiltration n := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℝ) (M := V)
  choose n hn using fun v : V => hV v.property
  let N := s.sup n
  refine ⟨N, ?_⟩
  have hspan : Submodule.span ℝ (s : Set V) ≤
      (hiddenCoefficientFiltration N).comap V.subtype := by
    apply Submodule.span_le.mpr
    intro v hv
    exact hiddenCoefficientFiltration_monotone (Finset.le_sup hv) (hn v)
  rw [hs] at hspan
  intro p hp
  exact hspan (show (⟨p, hp⟩ : V) ∈ (⊤ : Submodule ℝ V) from Submodule.mem_top)

/-- A uniform hidden-degree bound on the polynomial-coefficient part of an
actual finite-dimensional operator space, using the faithful normal action. -/
theorem actual_uniform_hidden_degree_bound (E : Submodule ℝ Operator)
    [FiniteDimensional ℝ E] :
    ∃ N, ∀ p : NormalForm, normalAction p ∈ E →
      (∀ α, ∃ n, (partialDerivative 2 ^ n) (p α) = 0) →
      ∀ α, (partialDerivative 2 ^ N) (p α) = 0 := by
  let V : Submodule ℝ NormalForm := normalFormsIn E ⊓ hiddenPolynomialForms
  let inc : V →ₗ[ℝ] normalFormsIn E := Submodule.inclusion inf_le_left
  have hi : Function.Injective inc := Submodule.inclusion_injective inf_le_left
  let act : V →ₗ[ℝ] E := (normalFormsIn_action E).comp inc
  let : Module.Finite ℝ V := Module.Finite.of_injective act
    ((normalFormsIn_action_injective E).comp hi)
  obtain ⟨N, hN⟩ := finiteDimensional_uniform_hiddenFiltration V inf_le_right
  refine ⟨N, ?_⟩
  intro p hp hpoly
  apply (mem_hiddenCoefficientFiltration p N).mp
  exact hN ⟨hp, exists_hiddenCoefficientFiltration p hpoly⟩

end Wong.SmoothModel
