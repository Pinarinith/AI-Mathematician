import Wong.CoordinateGenerators
import Wong.VisibleHeadCalculus
import Wong.Visible

/-! Actual rotations in the visible coordinate plane and their affine Wong tensors. -/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads
open scoped Matrix

def planeRotationLinear (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : State ≃ₗ[ℝ] State where
  toFun x := ![a * x 0 + b * x 1, -b * x 0 + a * x 1, x 2]
  invFun x := ![a * x 0 - b * x 1, b * x 0 + a * x 1, x 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by funext i; fin_cases i <;> simp <;> ring
  left_inv x := by
    funext i
    fin_cases i <;> simp
    · nlinarith [congrArg (fun t : ℝ => t * x 0) hab]
    · nlinarith [congrArg (fun t : ℝ => t * x 1) hab]
  right_inv x := by
    funext i
    fin_cases i <;> simp
    · nlinarith [congrArg (fun t : ℝ => t * x 0) hab]
    · nlinarith [congrArg (fun t : ℝ => t * x 1) hab]

def planeRotation (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : State ≃L[ℝ] State :=
  (planeRotationLinear a b hab).toContinuousLinearEquiv

@[simp] theorem planeRotation_apply (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (x : State) :
    planeRotation a b hab x = ![a * x 0 + b * x 1, -b * x 0 + a * x 1, x 2] := rfl

theorem planeRotation_orthogonal (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    CoordinateOrthogonal (planeRotation a b hab) := by
  intro v w
  simp [dotProduct, Fin.sum_univ_three]
  nlinarith [congrArg (fun t : ℝ => t * (v 0 * w 0)) hab,
    congrArg (fun t : ℝ => t * (v 1 * w 1)) hab]

def rotatedParameters (a b : ℝ) (p : Wong.AffineParameters) : Wong.AffineParameters where
  b₀ := p.b₀
  b₁ := a * p.b₁ - b * p.b₂
  b₂ := b * p.b₁ + a * p.b₂
  k₀ := a * p.k₀ - b * p.h₀
  k₁ := a * (a * p.k₁ - b * p.k₂) - b * (a * p.h₁ - b * p.h₂)
  k₂ := a * (b * p.k₁ + a * p.k₂) - b * (b * p.h₁ + a * p.h₂)
  k₃ := a * p.k₃ - b * p.h₃
  h₀ := b * p.k₀ + a * p.h₀
  h₁ := b * (a * p.k₁ - b * p.k₂) + a * (a * p.h₁ - b * p.h₂)
  h₂ := b * (b * p.k₁ + a * p.k₂) + a * (b * p.h₁ + a * p.h₂)
  h₃ := b * p.k₃ + a * p.h₃

theorem wong_planeRotation (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    ∀ i j x, (wong (coordinateDrift (planeRotation a b hab) f) i j).1 x =
      (rotatedParameters a b p).matrix x i j := by
  intro i j x
  rw [wong_coordinateDrift]
  simp only [coordinatePullback_apply, wongBilinear, Fin.sum_univ_three,
    planeRotation_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hp, coordinateVector, rotatedParameters, Wong.AffineParameters.matrix,
      Wong.AffineParameters.w12, Wong.AffineParameters.w13, Wong.AffineParameters.w23]
  all_goals first | (solve | ring) | nlinarith [congrArg (fun t : ℝ => t *
    (p.b₁ * (a * x 0 + b * x 1) + p.b₂ * (-b * x 0 + a * x 1) + p.b₀)) hab]

theorem planeRotation_coordinate_mem {m : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (i : Fin 3) (hi : i = 0 ∨ i = 1) :
    multiplication (linearFunction (coordinateVector i)) ∈
      estimationAlgebra (coordinateDrift (planeRotation a b hab) f)
        (coordinateObservations (planeRotation a b hab) h) := by
  rw [← coordinateAlgebra_estimationAlgebra _ (planeRotation_orthogonal a b hab),
    linear_mem_coordinateAlgebra _ (planeRotation_orthogonal a b hab)]
  have hv₀ : planeRotation a b hab (coordinateVector 0) =
      a • coordinateVector 0 + (-b) • coordinateVector 1 := by
    funext j; fin_cases j <;> simp [coordinateVector]
  have hv₁ : planeRotation a b hab (coordinateVector 1) =
      b • coordinateVector 0 + a • coordinateVector 1 := by
    funext j; fin_cases j <;> simp [coordinateVector]
  rcases hi with rfl | rfl
  · rw [hv₀]
    exact (linearCoefficientSpace (estimationAlgebra f h)).add_mem
      ((linearCoefficientSpace (estimationAlgebra f h)).smul_mem a h₀)
      ((linearCoefficientSpace (estimationAlgebra f h)).smul_mem (-b) h₁)
  · rw [hv₁]
    exact (linearCoefficientSpace (estimationAlgebra f h)).add_mem
      ((linearCoefficientSpace (estimationAlgebra f h)).smul_mem b h₀)
      ((linearCoefficientSpace (estimationAlgebra f h)).smul_mem a h₁)

/-- A nonzero visible Wong slope admits a genuine orthogonal change of the
actual filtering model, with affine visible entry `ρ x₁ + b₀`, `ρ > 0`. -/
theorem exists_normalizing_planeRotation (p : Wong.AffineParameters)
    (hne : p.b₁ ≠ 0 ∨ p.b₂ ≠ 0) :
    ∃ (a b ρ : ℝ) (_hab : a ^ 2 + b ^ 2 = 1),
      0 < ρ ∧ (rotatedParameters a b p).b₁ = 0 ∧
        (rotatedParameters a b p).b₂ = ρ := by
  obtain ⟨ρ, hρ, hs⟩ := Wong.Visible.existsNormalization p.b₁ p.b₂ hne
  have hn : ρ ≠ 0 := ne_of_gt hρ
  have hab : (p.b₂ / ρ) ^ 2 + (p.b₁ / ρ) ^ 2 = 1 := by
    field_simp
    nlinarith [hs]
  refine ⟨p.b₂ / ρ, p.b₁ / ρ, ρ, hab, hρ, ?_, ?_⟩
  · simp only [rotatedParameters]
    ring
  · simp only [rotatedParameters]
    calc
      _ = (p.b₁ ^ 2 + p.b₂ ^ 2) / ρ := by ring
      _ = ρ := by rw [← hs]; field_simp



/-- Normalize a nonzero visible slope while retaining every actual-model
hypothesis needed by the visible elimination argument. -/
theorem normalized_visible_model {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hne : p.b₁ ≠ 0 ∨ p.b₂ ≠ 0) :
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
      q.b₁ = 0 ∧ 0 < q.b₂ := by
  obtain ⟨a, b, ρ, hab, hρ, hq₁, hq₂⟩ := exists_normalizing_planeRotation p hne
  let e := planeRotation a b hab
  have he : CoordinateOrthogonal e := planeRotation_orthogonal a b hab
  refine ⟨e, rotatedParameters a b p, he, wong_planeRotation a b hab f p hp,
    finiteDimensional_coordinateEstimationAlgebra e he f h, ?_,
    quadraticFree_coordinateEstimationAlgebra e he f h hq,
    planeRotation_coordinate_mem a b hab f h h₀ h₁ 0 (Or.inl rfl),
    planeRotation_coordinate_mem a b hab f h h₀ h₁ 1 (Or.inr rfl), hq₁, ?_⟩
  · rwa [linearRank_coordinateEstimationAlgebra e he]
  · rwa [hq₂]

end Wong.SmoothModel.VisibleHeads
