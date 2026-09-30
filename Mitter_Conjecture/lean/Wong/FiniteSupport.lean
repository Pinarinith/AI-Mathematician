import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finset.Lattice.Fold

/-!
Finite-dimensional spaces of finite normal forms have uniformly bounded weight.
The coefficient module is arbitrary: it may be a space of smooth functions.
This file does not define composition or Lie brackets of differential operators.
-/

namespace Wong

variable {K I C : Type*} [Field K] [AddCommGroup C] [Module K C]

theorem finiteDimensional_uniform_weight_bound
    (E : Submodule K (I →₀ C)) [FiniteDimensional K E] (weight : I → ℕ) :
    ∃ N : ℕ, ∀ p ∈ E, ∀ i, N < weight i → p i = 0 := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional E).mpr inferInstance
  let N := s.sup (fun p => p.support.sup weight)
  have hle : E ≤ Finsupp.supported C K {i | weight i ≤ N} := by
    rw [← hs]
    refine Submodule.span_le.mpr ?_
    intro p hp
    change (p.support : Set I) ⊆ {i | weight i ≤ N}
    intro i hi
    have hi' : weight i ≤ p.support.sup weight := Finset.le_sup hi
    have hp' : p ∈ s := hp
    have hpbound : p.support.sup weight ≤ N := by
      exact Finset.le_sup (f := fun p : I →₀ C => p.support.sup weight) hp'
    exact le_trans hi' hpbound
  refine ⟨N, ?_⟩
  intro p hp i hi
  exact (Finsupp.mem_supported' K p).mp (hle hp) i (Nat.not_le.mpr hi)

theorem no_unbounded_weight_family
    (E : Submodule K (I →₀ C)) [FiniteDimensional K E]
    (weight : I → ℕ)
    (hunbounded : ∀ N : ℕ, ∃ p ∈ E, ∃ i, N < weight i ∧ p i ≠ 0) :
    False := by
  obtain ⟨N, hN⟩ := finiteDimensional_uniform_weight_bound E weight
  obtain ⟨p, hp, i, hi, hpi⟩ := hunbounded N
  exact hpi (hN p hp i hi)

/-- Ordinary order for a three-dimensional normally ordered derivative monomial. -/
def ordinaryOrder (α : Fin 3 → ℕ) : ℕ := ∑ i, α i

/-- The sector-II weight on `t^p ∂₁^q₁ ∂₂^q₂ ∂₃^q₃`. -/
def sectorTwoWeight (a : ℕ × (Fin 3 → ℕ)) : ℕ :=
  a.1 + a.2 0 + a.2 1 + 2 * a.2 2

end Wong
