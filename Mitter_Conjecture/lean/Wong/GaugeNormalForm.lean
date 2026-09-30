import Wong.Gauge
import Wong.NormalFormAlgebra
import Wong.DifferentialOrder

/-! Gauge transport preserves actual finite normal forms and differential order. -/

noncomputable section
namespace Wong.SmoothModel

def normalGauge (Λ : Smooth) (p : NormalForm) : NormalForm :=
  normalCompose (normalCompose (Finsupp.single 0 (smoothExp Λ)) p)
    (Finsupp.single 0 (smoothExp (-Λ)))

theorem normalAction_normalGauge (Λ : Smooth) (p : NormalForm) :
    normalAction (normalGauge Λ p) = gaugeConjugation Λ (normalAction p) := by
  rw [normalGauge, normalAction_compose, normalAction_compose,
    normalAction_scalar, normalAction_scalar]
  apply LinearMap.ext
  intro u
  rfl

theorem gaugeAlgebra_le_normalFormOperators (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (hE : E ≤ normalFormOperators) :
    gaugeAlgebra Λ E ≤ normalFormOperators := by
  rintro A ⟨B, hB, rfl⟩
  obtain ⟨p, rfl⟩ := hE hB
  exact ⟨normalGauge Λ p, normalAction_normalGauge Λ p⟩

theorem gaugeConjugation_commuteWithMultiplier (Λ u : Smooth) (A : Operator) :
    commuteWithMultiplier u (gaugeConjugation Λ A) =
      gaugeConjugation Λ (commuteWithMultiplier u A) := by
  simp only [commuteWithMultiplier_apply]
  have he := (gaugeLieEquiv Λ).map_lie A (multiplication u)
  simpa only [gaugeLieEquiv_apply, gaugeConjugation_multiplication] using he.symm

theorem gaugeConjugation_mem_orderSpace (Λ : Smooth) (n : ℕ) (A : Operator)
    (hA : A ∈ orderSpace n) : gaugeConjugation Λ A ∈ orderSpace n := by
  induction n generalizing A with
  | zero =>
    apply mem_orderSpace_zero.mpr
    intro u
    rw [gaugeConjugation_commuteWithMultiplier, mem_orderSpace_zero.mp hA u, map_zero]
  | succ n ih =>
    apply mem_orderSpace_succ.mpr
    intro u
    rw [gaugeConjugation_commuteWithMultiplier]
    exact ih _ (mem_orderSpace_succ.mp hA u)

theorem gaugeAlgebra_uniform_order_bound (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (K : ℕ)
    (hK : ∀ A ∈ E, A ∈ orderSpace K) :
    ∀ A ∈ gaugeAlgebra Λ E, A ∈ orderSpace K := by
  rintro A ⟨B, hB, rfl⟩
  exact gaugeConjugation_mem_orderSpace Λ K B (hK B hB)

theorem gaugeAlgebra_le_finiteOrder (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (hE : E ≤ finiteOrderAlgebra) :
    gaugeAlgebra Λ E ≤ finiteOrderAlgebra := by
  rintro A ⟨B, hB, rfl⟩
  obtain ⟨n, hn⟩ := hE hB
  exact ⟨n, gaugeConjugation_mem_orderSpace Λ n B hn⟩

end Wong.SmoothModel
