import Wong.VisibleRotation

/-!
# Genuine orthogonal diagonalization for the second sector

The two-dimensional real spectral calculation is explicit. The same actual
visible-plane rotation already proved to transport the filtering model
then diagonalizes the symmetric remaining Wong slope matrix. No diagonal
coordinate assumption is introduced into the main claim.
-/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads

/-- A nonzero symmetric real two-by-two matrix has a nonzero eigenvalue
and a Euclidean unit eigenvector, oriented as the first column `(a,-b)` of
our visible rotation. -/
theorem symmetric_two_nonzero_unit_eigenvector (k l h : ℝ)
    (hne : k ≠ 0 ∨ l ≠ 0 ∨ h ≠ 0) :
    ∃ a b lam : ℝ, a ^ 2 + b ^ 2 = 1 ∧ lam ≠ 0 ∧
      k * a - l * b = lam * a ∧ l * a - h * b = -lam * b := by
  by_cases hl : l = 0
  · by_cases hk : k = 0
    · have hh : h ≠ 0 := by tauto
      exact ⟨0, 1, h, by norm_num, hh, by simp [hl], by ring⟩
    · exact ⟨1, 0, k, by norm_num, hk, by ring, by simp [hl]⟩
  · let d := Real.sqrt ((k - h) ^ 2 + 4 * l ^ 2)
    have hd : 0 < d := Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_ne_zero hl, sq_nonneg (k-h)])
    have hd₂ : d ^ 2 = (k - h) ^ 2 + 4 * l ^ 2 := Real.sq_sqrt (by positivity)
    obtain ⟨t, ht₂, ht⟩ : ∃ t : ℝ,
        t ^ 2 = (k - h) ^ 2 + 4 * l ^ 2 ∧ k + h + t ≠ 0 := by
      by_cases hs : 0 ≤ k + h
      · exact ⟨d, hd₂, by linarith⟩
      · exact ⟨-d, by simpa using hd₂, by linarith⟩
    let lam := (k + h + t) / 2
    have hlam : lam ≠ 0 := by
      intro hz
      apply ht
      dsimp [lam] at hz
      linarith
    have hchar : lam ^ 2 - (k + h) * lam + k * h - l ^ 2 = 0 := by
      dsimp [lam]
      linear_combination (1 / 4 : ℝ) * ht₂
    let ρ := Real.sqrt (l ^ 2 + (k - lam) ^ 2)
    have hρ : 0 < ρ := Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_ne_zero hl, sq_nonneg (k-lam)])
    have hρ₂ : ρ ^ 2 = l ^ 2 + (k - lam) ^ 2 := Real.sq_sqrt (by positivity)
    have hρne : ρ ≠ 0 := ne_of_gt hρ
    refine ⟨l / ρ, (k - lam) / ρ, lam, ?_, hlam, ?_, ?_⟩
    · field_simp
      nlinarith [hρ₂]
    · ring
    · calc
        l * (l / ρ) - h * ((k - lam) / ρ) = (l ^ 2 - h * (k - lam)) / ρ := by ring
        _ = (-lam * (k - lam)) / ρ := by congr 1; linear_combination -hchar
        _ = -lam * ((k - lam) / ρ) := by ring

/-- Diagonalization of the actual parameter transformation, keeping a
nonzero eigenvalue in the first visible coordinate. -/
theorem exists_diagonalizing_planeRotation (p : Wong.AffineParameters)
    (hsym : p.h₁ = p.k₂) (hne : p.k₁ ≠ 0 ∨ p.k₂ ≠ 0 ∨ p.h₂ ≠ 0) :
    ∃ (a b : ℝ) (_hab : a ^ 2 + b ^ 2 = 1),
      (rotatedParameters a b p).k₁ ≠ 0 ∧
      (rotatedParameters a b p).k₂ = 0 ∧ (rotatedParameters a b p).h₁ = 0 := by
  obtain ⟨a, b, lam, hab, hlam, he₀, he₁⟩ :=
    symmetric_two_nonzero_unit_eigenvector p.k₁ p.k₂ p.h₂ hne
  have hk : (rotatedParameters a b p).k₁ = lam := by
    simp only [rotatedParameters, hsym]
    linear_combination a * he₀ - b * he₁ + lam * hab
  have hl : (rotatedParameters a b p).k₂ = 0 := by
    simp only [rotatedParameters, hsym]
    linear_combination b * he₀ + a * he₁
  have hh : (rotatedParameters a b p).h₁ = 0 := by
    simp only [rotatedParameters, hsym] at hl ⊢
    convert hl using 1; ring
  refine ⟨a, b, hab, ?_, hl, hh⟩
  rwa [hk]

/-- The second-sector vanishing conditions already established in the
first sector are preserved by an arbitrary visible rotation. -/
theorem rotatedParameters_sector_two_zeros (a b : ℝ) (p : Wong.AffineParameters)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) (hk₃ : p.k₃ = 0) (hh₃ : p.h₃ = 0) :
    (rotatedParameters a b p).b₁ = 0 ∧ (rotatedParameters a b p).b₂ = 0 ∧
    (rotatedParameters a b p).k₃ = 0 ∧ (rotatedParameters a b p).h₃ = 0 := by
  simp [rotatedParameters, hb₁, hb₂, hk₃, hh₃]

/-- Orthogonal diagonalization on the original filtering model preserves
all actual rank-two and function-element hypotheses and all known zero slopes. -/
theorem diagonal_sector_two_model {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) (hk₃ : p.k₃ = 0) (hh₃ : p.h₃ = 0)
    (hne : p.k₁ ≠ 0 ∨ p.k₂ ≠ 0 ∨ p.h₂ ≠ 0) :
    ∃ (e : State ≃L[ℝ] State) (q : Wong.AffineParameters),
      CoordinateOrthogonal e ∧
      (∀ i j x, (wong (coordinateDrift e f) i j).1 x = q.matrix x i j) ∧
      FiniteDimensional ℝ (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) ∧
      linearRank (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) = 2 ∧
      QuadraticFree (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) ∧
      multiplication (linearFunction (coordinateVector 0)) ∈
        estimationAlgebra (coordinateDrift e f) (coordinateObservations e h) ∧
      multiplication (linearFunction (coordinateVector 1)) ∈
        estimationAlgebra (coordinateDrift e f) (coordinateObservations e h) ∧
      q.b₁ = 0 ∧ q.b₂ = 0 ∧ q.k₃ = 0 ∧ q.h₃ = 0 ∧
      q.k₁ ≠ 0 ∧ q.k₂ = 0 ∧ q.h₁ = 0 := by
  obtain ⟨a, b, hab, hk, hl, hh⟩ := exists_diagonalizing_planeRotation p
    (bianchi_slopes f p hp) hne
  let e := planeRotation a b hab
  have he : CoordinateOrthogonal e := planeRotation_orthogonal a b hab
  obtain ⟨hb₁', hb₂', hk₃', hh₃'⟩ := rotatedParameters_sector_two_zeros a b p hb₁ hb₂ hk₃ hh₃
  refine ⟨e, rotatedParameters a b p, he, wong_planeRotation a b hab f p hp,
    finiteDimensional_coordinateEstimationAlgebra e he f h, ?_,
    quadraticFree_coordinateEstimationAlgebra e he f h hq,
    planeRotation_coordinate_mem a b hab f h h₀ h₁ 0 (Or.inl rfl),
    planeRotation_coordinate_mem a b hab f h h₀ h₁ 1 (Or.inr rfl),
    hb₁', hb₂', hk₃', hh₃', hk, hl, hh⟩
  rwa [linearRank_coordinateEstimationAlgebra e he]

end Wong.SmoothModel.VisibleHeads
