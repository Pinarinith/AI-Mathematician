import Wong.SectorIHiddenBridge
import Wong.SectorTwoConclusion
import Wong.ShiYau2020MainProof

/-! Final assembly for the paper's main claim. The independent Shi–Yau 2020
function-element theorem supplies quadratic-freeness before slope elimination;
the public theorem requires only finite-dimensionality and linear rank two. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem remainingVisibleAffineSlopesClaim_proved :
    RemainingVisibleAffineSlopesClaim := by
  intro m f h hFD hrank hq hx₀ hx₁ p hform hb₁ hb₂ hk₃ hh₃
  letI := hFD
  exact SectorTwo.remaining_visible_affine_slopes f h hrank hq hx₀ hx₁
    p hform hb₁ hb₂ hk₃ hh₃

/-- Conditional intermediate: slope elimination under quadratic-freeness. -/
theorem quadraticFree_main_theorem : QuadraticFreeMainClaim :=
  quadraticFreeMainClaim_of_remaining_visible_affine_slopes
    remainingVisibleAffineSlopesClaim_proved

/-- In the actual three-dimensional filtering model, quadratic-freeness follows
from finite-dimensionality and linear rank two by the independently proved
Shi–Yau 2020 function-element theorem. -/
theorem quadraticFree_of_finiteDimensional_rank_two {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2) :
    QuadraticFree (estimationAlgebra f h) :=
  quadraticFree_of_functionElementsAffine (estimationAlgebra f h)
    (shiYau2020_mitter_theorem m f h inferInstance hrank)

/-- The paper's main theorem, with no quadratic-freeness premise. -/
theorem main_theorem : mainClaim := by
  intro m f h hfd hrank
  letI := hfd
  exact quadraticFree_main_theorem m f h hfd hrank
    (quadraticFree_of_finiteDimensional_rank_two f h hrank)

end Wong.SmoothModel

#print axioms Wong.SmoothModel.main_theorem
#print axioms Wong.SmoothModel.quadraticFree_of_finiteDimensional_rank_two
