import Wong.VisibleRotation
import Wong.VisibleSymbolReconstruction
import Wong.VisibleHeadContradiction
import Wong.NormalSymbolsVisible

/-!
# Elimination of both visible Wong slopes on the actual estimation algebra

The proof joins the genuine operator heads, finite-dimensional pure-head
obstruction, smooth principal-symbol ladder, and actual orthogonal coordinate
transport. Affine Wong structure is the only structural input to this module;
no constant-head or vanishing-slope premise is added.
-/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads
open MvPolynomial

/-- Finite dimensionality removes the final mixed slope from every actual
second-order Lie element once the visible Wong entry has been normalized. -/
theorem normalized_heads_constant {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ ≠ 0)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (B : Operator) (hBE : B ∈ estimationAlgebra f h) (hB : B ∈ orderSpace 2) :
    ∃ c₁ c : ℝ, δ 1 (δ 1 B) = multiplication (c₁ • smoothOne) ∧
      δ 0 (δ 1 B) = multiplication (c • smoothOne) := by
  obtain ⟨c₀, a₀, c₁, c, a, h00, h11, h01⟩ :=
    normalized_visible_heads f h hrank hq p hp hb₁ hb₂ h₀ h₁ B hBE hB
  obtain ⟨nf, hnf, _⟩ := estimationAlgebra_unique_normalForm f h B hBE
  have hnE : normalAction nf ∈ estimationAlgebra f h := by rwa [hnf]
  have hn : NormalDegreeLE 2 nf := normalDegreeLE_of_action_order nf 2 (by rwa [hnf])
  have hqnf : projectHiddenSymbol (normalSymbol 2 nf) =
      visibleQuadratic (a₀ / 2) a (c₀ / 2) (c₁ / 2) c := by
    simpa only [visibleQuadratic, realCoefficient_apply] using
      projected_symbol_of_normalized_heads nf c₀ a₀ c₁ c a
        (by rwa [hnf]) (by rwa [hnf]) (by rwa [hnf])
  have ha := visible_mixed_slope_zero f h nf hnE hn (a₀ / 2) a (c₀ / 2) (c₁ / 2) c hqnf
  exact ⟨c₁, c, h11, by simpa [visibleAffine, ha] using h01⟩

/-- The normalized nonzero-slope case is impossible in the actual model. -/
theorem normalized_visible_slope_zero {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) : p.b₂ = 0 := by
  by_contra hb₂
  obtain ⟨c₁, c, h11, h01⟩ := normalized_heads_constant f h hrank hq p hp hb₁ hb₂ h₀ h₁
    (Y f h) (Y_mem_of_coordinate_mem f h h₀) (Y_mem_orderSpace_two f h p hp)
  exact hb₂ (normalized_slope_zero_of_constant_heads f h p hp hb₁ c₁ c h11 h01)

/-- Both visible affine Wong slopes vanish under the original adapted
rank-two, finite-dimensional, quadratic-free assumptions. -/
theorem visible_slopes_zero {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    p.b₁ = 0 ∧ p.b₂ = 0 := by
  by_contra hh
  have hne : p.b₁ ≠ 0 ∨ p.b₂ ≠ 0 := by tauto
  obtain ⟨e, q, _, hqf, hfd, hr, hfree, he₀, he₁, hq₁, hq₂⟩ :=
    normalized_visible_model f h hrank hq h₀ h₁ p hp hne
  let := hfd
  have hz := normalized_visible_slope_zero (coordinateDrift e f) (coordinateObservations e h)
    hr hfree q hqf hq₁ he₀ he₁
  linarith

end Wong.SmoothModel.VisibleHeads
