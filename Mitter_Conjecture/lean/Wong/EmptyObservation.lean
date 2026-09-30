import Wong.RankStructure

/-! The zero-observation branch is vacuous for the original rank-two claim. -/

noncomputable section
namespace Wong.SmoothModel

theorem estimationAlgebra_zero_observation_span (f : Fin 3 → Smooth)
    (h : Fin 0 → Smooth) :
    (estimationAlgebra f h).toSubmodule = Submodule.span ℝ {L0 f h} := by
  have hempty : Set.range (fun j : Fin 0 => multiplication (h j)) = ∅ := by
    ext A
    simp
  change (LieSubalgebra.lieSpan ℝ Operator
    ({L0 f h} ∪ Set.range (fun j => multiplication (h j)))).toSubmodule = _
  rw [hempty, Set.union_empty]
  apply LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero
  intro A hA B hB
  simp only [Set.mem_singleton_iff] at hA hB
  subst A
  subst B
  exact lie_self _

theorem linearCoefficientSpace_zero_observation (f : Fin 3 → Smooth)
    (h : Fin 0 → Smooth) :
    linearCoefficientSpace (estimationAlgebra f h) = ⊥ := by
  apply bot_unique
  intro a ha
  change a = 0
  change linearMultiplication a ∈ (estimationAlgebra f h).toSubmodule at ha
  rw [estimationAlgebra_zero_observation_span] at ha
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
  let u := linearFunction (coordinateVector 0)
  let δ := commuteWithMultiplier u
  have hLL : (δ ^ 2) (L0 f h) = 1 := by
    change ⁅⁅L0 f h, multiplication u⁆, multiplication u⁆ = 1
    rw [lie_L0_linearFunction, lie_directionD_linearFunction]
    simp [coordinateVector, Pi.single_apply]
  have hz : (δ ^ 2) (linearMultiplication a) = 0 := by
    change ⁅⁅multiplication (linearFunction a), multiplication u⁆, multiplication u⁆ = 0
    rw [lie_multiplication_multiplication, zero_lie]
  have he := congrArg (fun A : Operator => (δ ^ 2) A) hc
  rw [map_smul, hLL, hz] at he
  have hc0 : c = 0 := by
    have hp := congrArg (fun A : Operator => (A smoothOne).1 (0 : State)) he
    simpa [smoothOne] using hp
  have ha0 : linearMultiplication a = linearMultiplication 0 := by
    rw [← hc, hc0, zero_smul, map_zero]
  exact linearMultiplication_injective ha0

theorem linearRank_zero_observation (f : Fin 3 → Smooth) (h : Fin 0 → Smooth) :
    linearRank (estimationAlgebra f h) = 0 := by
  rw [linearRank, linearCoefficientSpace_zero_observation]
  simp

end Wong.SmoothModel
