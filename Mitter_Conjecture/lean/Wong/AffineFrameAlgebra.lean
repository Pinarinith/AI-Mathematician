import Wong.AffineFrame
import Wong.AdaptedGauge

/-! Actual affine transport preserves finite order, finite normal forms and visible function space. -/

noncomputable section
namespace Wong.SmoothModel

theorem normalFormOperators_mul_mem (A B : Operator)
    (hA : A ∈ normalFormOperators) (hB : B ∈ normalFormOperators) :
    A * B ∈ normalFormOperators := by
  obtain ⟨p, rfl⟩ := hA
  obtain ⟨q, rfl⟩ := hB
  exact ⟨normalCompose p q, normalAction_compose p q⟩

theorem normalFormOperators_one_mem : (1 : Operator) ∈ normalFormOperators := by
  exact ⟨Finsupp.single 0 smoothOne, by simp⟩

theorem normalFormOperators_pow_mem (A : Operator) (hA : A ∈ normalFormOperators) (n : ℕ) :
    A ^ n ∈ normalFormOperators := by
  induction n with
  | zero => simpa using normalFormOperators_one_mem
  | succ n ih => rw [pow_succ]; exact normalFormOperators_mul_mem _ _ ih hA

theorem normalFormOperators_directionalDerivative_mem (v : State) :
    directionalDerivative v ∈ normalFormOperators := by
  apply normalFormOperators.sum_mem
  intro i _
  exact normalFormOperators.smul_mem (v i)
    ⟨Finsupp.single (Finsupp.single i 1) smoothOne, normalAction_partial i⟩

theorem affineConjugation_normalAction_mem (e : State ≃L[ℝ] State)
    (b : State) (p : NormalForm) :
    affineConjugation e b (normalAction p) ∈ normalFormOperators := by
  classical
  have hm (α : MultiIndex) : affineConjugation e b (multiPartial α) ∈ normalFormOperators := by
    simp only [multiPartial, map_mul, map_pow, ← coordinate_directionalDerivative,
      affineConjugation_directionalDerivative]
    exact normalFormOperators_mul_mem _ _
      (normalFormOperators_mul_mem _ _
        (normalFormOperators_pow_mem _ (normalFormOperators_directionalDerivative_mem _) _)
        (normalFormOperators_pow_mem _ (normalFormOperators_directionalDerivative_mem _) _))
      (normalFormOperators_pow_mem _ (normalFormOperators_directionalDerivative_mem _) _)
  have hp : normalAction p = p.sum (fun α u => multiplication u * multiPartial α) := rfl
  rw [hp]
  simp only [Finsupp.sum, map_sum, map_mul, affineConjugation_multiplication]
  apply normalFormOperators.sum_mem
  intro α _
  exact normalFormOperators_mul_mem _ _
    ⟨Finsupp.single 0 (affinePullback e b (p α)), normalAction_scalar _⟩ (hm α)

abbrev affineAlgebra (e : State ≃L[ℝ] State) (b : State) (E : LieSubalgebra ℝ Operator) :
    LieSubalgebra ℝ Operator := E.map (affineLieEquiv e b).toLieHom

def affineAlgebraEquiv (e : State ≃L[ℝ] State) (b : State) (E : LieSubalgebra ℝ Operator) :
    E ≃ₗ⁅ℝ⁆ affineAlgebra e b E :=
  (affineLieEquiv e b).ofSubalgebras E (affineAlgebra e b E) rfl

theorem affineAlgebra_finiteDimensional (e : State ≃L[ℝ] State) (b : State)
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (affineAlgebra e b E) :=
  (affineAlgebraEquiv e b E).toLinearEquiv.finiteDimensional

theorem affineAlgebra_le_normalFormOperators (e : State ≃L[ℝ] State) (b : State)
    (E : LieSubalgebra ℝ Operator) (hE : E ≤ normalFormOperators) :
    affineAlgebra e b E ≤ normalFormOperators := by
  rintro A ⟨B, hB, rfl⟩
  obtain ⟨p, rfl⟩ := hE hB
  exact affineConjugation_normalAction_mem e b p

theorem affineConjugation_commuteWithMultiplier (e : State ≃L[ℝ] State)
    (b : State) (u : Smooth) (A : Operator) :
    commuteWithMultiplier u (affineConjugation e b A) =
      affineConjugation e b (commuteWithMultiplier ((affinePullback e b).symm u) A) := by
  simp only [commuteWithMultiplier_apply]
  have he := (affineLieEquiv e b).map_lie A
    (multiplication ((affinePullback e b).symm u))
  change affineConjugation e b ⁅A, multiplication ((affinePullback e b).symm u)⁆ =
    ⁅affineConjugation e b A,
      affineConjugation e b (multiplication ((affinePullback e b).symm u))⁆ at he
  simpa only [affineConjugation_multiplication, LinearEquiv.apply_symm_apply] using he.symm

theorem affineConjugation_mem_orderSpace (e : State ≃L[ℝ] State) (b : State)
    (n : ℕ) (A : Operator) (hA : A ∈ orderSpace n) :
    affineConjugation e b A ∈ orderSpace n := by
  induction n generalizing A with
  | zero =>
    apply mem_orderSpace_zero.mpr
    intro u
    rw [affineConjugation_commuteWithMultiplier, mem_orderSpace_zero.mp hA, map_zero]
  | succ n ih =>
    apply mem_orderSpace_succ.mpr
    intro u
    rw [affineConjugation_commuteWithMultiplier]
    exact ih _ (mem_orderSpace_succ.mp hA _)

theorem affineAlgebra_le_finiteOrder (e : State ≃L[ℝ] State) (b : State)
    (E : LieSubalgebra ℝ Operator) (hE : E ≤ finiteOrderAlgebra) :
    affineAlgebra e b E ≤ finiteOrderAlgebra := by
  rintro A ⟨B, hB, rfl⟩
  obtain ⟨n, hn⟩ := hE hB
  exact ⟨n, affineConjugation_mem_orderSpace e b n B hn⟩

theorem multiplication_mem_affineAlgebra_iff (e : State ≃L[ℝ] State) (b : State)
    (E : LieSubalgebra ℝ Operator) (u : Smooth) :
    multiplication u ∈ affineAlgebra e b E ↔
      multiplication ((affinePullback e b).symm u) ∈ E := by
  constructor
  · rintro ⟨A, hA, he⟩
    change affineConjugation e b A = multiplication u at he
    have he' : affineConjugation e b A =
        affineConjugation e b (multiplication ((affinePullback e b).symm u)) := by
      simpa only [affineConjugation_multiplication, LinearEquiv.apply_symm_apply] using he
    exact (affineConjugation e b).injective he' ▸ hA
  · intro hu
    refine ⟨multiplication ((affinePullback e b).symm u), hu, ?_⟩
    exact (affineConjugation_multiplication e b _).trans
      (congrArg multiplication ((affinePullback e b).apply_symm_apply u))

theorem adaptedFunctionSpace_hiddenAffine (α β δ : ℝ) (E : LieSubalgebra ℝ Operator)
    (hE : AdaptedFunctionSpace E) :
    AdaptedFunctionSpace (affineAlgebra (hiddenShear α β) ![0, 0, -δ] E) := by
  intro u hu
  obtain ⟨c, a₀, a₁, he⟩ := hE _
    ((multiplication_mem_affineAlgebra_iff _ _ E u).mp hu)
  refine ⟨c, a₀, a₁, ?_⟩
  have hp := congrArg (hiddenAffinePullback α β δ) he
  have hleft : hiddenAffinePullback α β δ ((affinePullback (hiddenShear α β)
      ![0, 0, -δ]).symm u) = u := (hiddenAffinePullback α β δ).apply_symm_apply u
  have hOne : hiddenAffinePullback α β δ smoothOne = smoothOne := rfl
  simpa only [hleft, map_add, map_smul, hOne,
    hiddenAffinePullback_visible_coordinate α β δ 0 (by decide),
    hiddenAffinePullback_visible_coordinate α β δ 1 (by decide)] using hp

end Wong.SmoothModel
