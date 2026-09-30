import Wong.VisibleHeadConstraints
import Wong.NormalSymbolsHeads

/-! Reconstruct the exact visible symbol from actual operator heads. -/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads
open MvPolynomial

/-- Reconstruct the exact projected principal symbol from the three
actual double coordinate commutators. -/
theorem projected_symbol_of_normalized_heads (p : NormalForm) (c₀ a₀ c₁ c a : ℝ)
    (h00 : δ 0 (δ 0 (normalAction p)) = multiplication (visibleAffine c₀ 0 a₀))
    (h11 : δ 1 (δ 1 (normalAction p)) = multiplication (c₁ • smoothOne))
    (h01 : δ 0 (δ 1 (normalAction p)) = multiplication (visibleAffine c 0 a)) :
    projectHiddenSymbol (normalSymbol 2 p) =
      (C ((a₀ / 2) • linearFunction (coordinateVector 1) + (c₀ / 2) • smoothOne) * MvPolynomial.X 0 ^ 2 +
        C ((c₁ / 2) • smoothOne) * MvPolynomial.X 1 ^ 2 +
        C (a • linearFunction (coordinateVector 1) + c • smoothOne) * MvPolynomial.X 0 * MvPolynomial.X 1) := by
  have hh := normalSymbol_two_projected_heads p _ _ _
    (normalSymbol_two_head p 0 0 _ h00) (normalSymbol_two_head p 1 1 _ h11)
    (normalSymbol_two_head p 0 1 _ h01)
  have htwo (x : State) : (2 : Smooth).1 x = 2 := smooth_coe_natCast 2 x
  have hc₀ : visibleAffine c₀ 0 a₀ = (2 : Smooth) *
      ((a₀ / 2) • linearFunction (coordinateVector 1) + (c₀ / 2) • smoothOne) := by
    apply Subtype.ext
    funext x
    simp [visibleAffine, smoothOne, htwo]
    ring
  have hc₁ : c₁ • smoothOne = (2 : Smooth) * ((c₁ / 2) • smoothOne) := by
    apply Subtype.ext
    funext x
    simp [smoothOne, htwo]
    ring
  have hc : visibleAffine c 0 a = a • linearFunction (coordinateVector 1) + c • smoothOne := by
    simp [visibleAffine, add_comm]
  have hscale :
      C (visibleAffine c₀ 0 a₀) * MvPolynomial.X 0 ^ 2 + C (c₁ • smoothOne) * MvPolynomial.X 1 ^ 2 +
        2 * C (visibleAffine c 0 a) * MvPolynomial.X 0 * MvPolynomial.X 1 =
      (2 : SmoothSymbol) * (C ((a₀ / 2) • linearFunction (coordinateVector 1) + (c₀ / 2) • smoothOne) * MvPolynomial.X 0 ^ 2 +
        C ((c₁ / 2) • smoothOne) * MvPolynomial.X 1 ^ 2 +
        C (a • linearFunction (coordinateVector 1) + c • smoothOne) * MvPolynomial.X 0 * MvPolynomial.X 1) := by
    rw [hc₀, hc₁, hc]
    simp only [map_mul, map_ofNat]
    ring
  have he := hh.trans hscale
  apply MvPolynomial.ext
  intro α
  apply Subtype.ext
  funext x
  have hv := congrArg (fun q : SmoothSymbol => (q.coeff α).1 x) he
  have hcoeff (P Q : SmoothSymbol) : ((P + Q).coeff α).1 x =
      (P.coeff α).1 x + (Q.coeff α).1 x := rfl
  simp only [two_mul, hcoeff] at hv ⊢
  linarith only [hv]

end Wong.SmoothModel.VisibleHeads
