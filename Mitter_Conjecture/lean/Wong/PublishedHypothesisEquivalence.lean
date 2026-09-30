import Wong.RankStructure

/-!
# The adapted rank hypothesis in the published affine theorem

Shi–Yau use coordinate functions plus arbitrary constants. On the actual
estimation algebra, rank two supplies the identity multiplier; consequently
that convention is equivalent to homogeneous membership of the first two
coordinates. The forbidden third affine coordinate is then a theorem of
rank two, rather than an extra hypothesis. Neither finite dimensionality nor
quadratic-freeness is used in this equivalence.
-/

noncomputable section
namespace Wong.SmoothModel

/-- The rank-two adapted-coordinate assumption in the published theorem,
with the paper's coordinates `1,2,3` represented by `0,1,2`. -/
def PublishedAdaptedRankHypothesis {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) : Prop :=
  linearRank (estimationAlgebra f h) = 2 ∧
    ∃ c₀ c₁ : ℝ,
      multiplication (linearFunction (coordinateVector 0) + c₀ • smoothOne) ∈
        estimationAlgebra f h ∧
      multiplication (linearFunction (coordinateVector 1) + c₁ • smoothOne) ∈
        estimationAlgebra f h ∧
      ∀ c : ℝ,
        multiplication (linearFunction (coordinateVector 2) + c • smoothOne) ∉
          estimationAlgebra f h

theorem affine_coordinate_mem_iff_of_rank_two {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (hrank : linearRank (estimationAlgebra f h) = 2)
    (i : Fin 3) (c : ℝ) :
    multiplication (linearFunction (coordinateVector i) + c • smoothOne) ∈
        estimationAlgebra f h ↔
      multiplication (linearFunction (coordinateVector i)) ∈ estimationAlgebra f h := by
  have hc : multiplication (c • smoothOne) ∈ estimationAlgebra f h := by
    simpa using (estimationAlgebra f h).smul_mem c
      (smoothOne_mem_estimationAlgebra_of_rank_two f h hrank)
  rw [multiplication_add]
  constructor
  · intro hi
    simpa using (estimationAlgebra f h).sub_mem hi hc
  · intro hi
    exact (estimationAlgebra f h).add_mem hi hc

/-- Exact equivalence of the affine-coordinate convention in the source
and the homogeneous-coordinate convention of the external theorem interface. -/
theorem publishedAdaptedRankHypothesis_iff {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) : PublishedAdaptedRankHypothesis f h ↔
      linearRank (estimationAlgebra f h) = 2 ∧
      multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h ∧
      multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h := by
  constructor
  · rintro ⟨hrank, c₀, c₁, h₀, h₁, _⟩
    exact ⟨hrank,
      (affine_coordinate_mem_iff_of_rank_two f h hrank 0 c₀).mp h₀,
      (affine_coordinate_mem_iff_of_rank_two f h hrank 1 c₁).mp h₁⟩
  · rintro ⟨hrank, h₀, h₁⟩
    refine ⟨hrank, 0, 0, ?_, ?_, ?_⟩
    · simpa using h₀
    · simpa using h₁
    · intro c hc
      have h₂ := (affine_coordinate_mem_iff_of_rank_two f h hrank 2 c).mp hc
      have hzero := rank_two_adapted_coefficient_zero (estimationAlgebra f h)
        hrank h₀ h₁ (coordinateVector 2) h₂
      norm_num [coordinateVector] at hzero

end Wong.SmoothModel
