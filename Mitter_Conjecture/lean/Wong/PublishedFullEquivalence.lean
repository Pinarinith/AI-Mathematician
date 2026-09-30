import Wong.PublishedAffineStatement
import Wong.PublishedHypothesisEquivalence

/-!
# Full equivalence of the published affine input interface

Both adapted-coordinate hypotheses and polynomial conclusions are
converted in both directions. This equivalence itself uses no external
mathematical input; it identifies exactly which published proposition the
sole authorized external declaration represents.
-/

noncomputable section
namespace Wong.SmoothModel

def PublishedAffineStructureLiteral : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    PublishedAdaptedRankHypothesis f h → PublishedPolynomialWong f

def PublishedAffineStructureParametric : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    PublishedAdaptedRankHypothesis f h → AffineWong f

theorem shiYauAffineStructure_iff_literal :
    ShiYauAffineStructure ↔ PublishedAffineStructureLiteral := by
  constructor
  · intro H m hm f h hFD hp
    obtain ⟨hrank, hx₀, hx₁⟩ := (publishedAdaptedRankHypothesis_iff f h).mp hp
    exact H m hm f h hFD hrank hx₀ hx₁
  · intro H m hm f h hFD hrank hx₀ hx₁
    exact H m hm f h hFD
      ((publishedAdaptedRankHypothesis_iff f h).mpr ⟨hrank, hx₀, hx₁⟩)

theorem publishedAffineStructureLiteral_iff_parametric :
    PublishedAffineStructureLiteral ↔ PublishedAffineStructureParametric := by
  constructor
  · intro H m hm f h hFD hp
    exact (affineWong_iff_publishedPolynomialWong f).mpr (H m hm f h hFD hp)
  · intro H m hm f h hFD hp
    exact (affineWong_iff_publishedPolynomialWong f).mp (H m hm f h hFD hp)

theorem shiYauAffineStructure_iff_parametric :
    ShiYauAffineStructure ↔ PublishedAffineStructureParametric :=
  shiYauAffineStructure_iff_literal.trans publishedAffineStructureLiteral_iff_parametric

end Wong.SmoothModel
