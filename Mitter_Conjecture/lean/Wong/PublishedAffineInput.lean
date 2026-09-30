import Wong.PublishedAffineStatement
import Wong.PublishedVisibleComplete
import Wong.PublishedMixedAffinityProof
import Wong.EmptyObservation

/-! Internal proof of the exact Shi–Yau 2017 adapted-coordinate statement.
Both visible and mixed conclusions are derived for the original smooth
filtering model without a quadratic-freeness assumption. No published
mathematical result is introduced as an external axiom. -/

noncomputable section
namespace Wong.Published

/-- Shi–Yau 2017, Theorems 3.4 and 3.10, with the same exact statement that
was previously the campaign's sole literature axiom. -/
theorem shi_yau_affinity : Wong.SmoothModel.ShiYauAffineStructure := by
  intro m _hm f h hfd hrank hx₀ hx₁
  letI := hfd
  obtain ⟨p₀₁, hd₀₁, hh₀₁, he₀₁⟩ :=
    Wong.SmoothModel.visible_wong_published_polynomial_without_quadraticFree
      f h hrank hx₀ hx₁
  obtain ⟨p₀₂, p₁₂, hd₀₂, hd₁₂, he₀₂, he₁₂⟩ :=
    Wong.SmoothModel.mixed_wong_published_polynomials_of_visible_affinity
      f h hrank hx₀ hx₁ p₀₁ hd₀₁ hh₀₁ he₀₁
  exact ⟨p₀₁, p₀₂, p₁₂, hd₀₁, hd₀₂, hd₁₂, hh₀₁, he₀₁, he₀₂, he₁₂⟩

end Wong.Published

namespace Wong.SmoothModel

/-- Affine structure for the original model. The positive-dimensional
published statement is internally proved; the zero-observation extension
is vacuous by the independently proved rank-zero result. -/
theorem shi_yau_affine_structure {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    AffineWong f := by
  by_cases hm : 0 < m
  · exact (affineWong_iff_publishedPolynomialWong f).mpr
      (Wong.Published.shi_yau_affinity m hm f h inferInstance hrank hx₀ hx₁)
  · have hm0 : m = 0 := by omega
    subst m
    have hz := linearRank_zero_observation f h
    omega

end Wong.SmoothModel

#print axioms Wong.Published.shi_yau_affinity
