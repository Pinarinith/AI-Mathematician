import Wong.SectorIHiddenBridge
import Wong.SectorTwoConclusion

/-! Final assembly for the frozen original mainClaim. All slope elimination
and the exact Shi–Yau affine-structure statement are proved internally. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem remainingVisibleAffineSlopesClaim_proved :
    RemainingVisibleAffineSlopesClaim := by
  intro m f h hFD hrank hq hx₀ hx₁ p hform hb₁ hb₂ hk₃ hh₃
  letI := hFD
  exact SectorTwo.remaining_visible_affine_slopes f h hrank hq hx₀ hx₁
    p hform hb₁ hb₂ hk₃ hh₃

/-- The original global smooth rank-two, quadratic-free estimation-algebra
constancy theorem, retaining precisely the frozen original hypotheses. -/
theorem main_theorem : mainClaim :=
  mainClaim_of_remaining_visible_affine_slopes remainingVisibleAffineSlopesClaim_proved

end Wong.SmoothModel

#print axioms Wong.SmoothModel.main_theorem
