import Wong.SmoothBrackets
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Actual smooth gauge conjugation

Multiplication by `exp Λ` is an invertible linear map on globally smooth
functions. Its conjugation fixes every scalar multiplication operator,
sends `D f i` to `D (f + grad Λ) i`, and leaves the Wong matrix unchanged.

The conjugated filtering generator retains the original scalar potential.
No assertion identifies it with `L0` obtained by recomputing `eta` from the
new drift.
-/

noncomputable section
namespace Wong.SmoothModel

/-- The exponential of an actual smooth function. -/
def smoothExp (u : Smooth) : Smooth :=
  ⟨fun x => Real.exp (u.1 x), (smooth u).exp⟩

@[simp] theorem smoothExp_apply (u : Smooth) (x : State) :
    (smoothExp u).1 x = Real.exp (u.1 x) := rfl

/-- The chain rule for the gauge multiplier. -/
theorem partialDerivative_smoothExp (i : Fin 3) (u : Smooth) :
    partialDerivative i (smoothExp u) =
      smoothMul (smoothExp u) (partialDerivative i u) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun y => Real.exp (u.1 y)) x (coordinateVector i) = _
  rw [fderiv_exp (((smooth u).differentiable (by simp)).differentiableAt)]
  rfl

/-- Multiplication by `exp Λ`, with genuine inverse multiplication by `exp (-Λ)`. -/
def gaugeEquiv (Λ : Smooth) : Smooth ≃ₗ[ℝ] Smooth where
  __ := multiplication (smoothExp Λ)
  invFun := multiplication (smoothExp (-Λ))
  left_inv u := by
    apply Subtype.ext
    funext x
    change Real.exp (-Λ.1 x) * (Real.exp (Λ.1 x) * u.1 x) = u.1 x
    rw [← mul_assoc, ← Real.exp_add]
    simp
  right_inv u := by
    apply Subtype.ext
    funext x
    change Real.exp (Λ.1 x) * (Real.exp (-Λ.1 x) * u.1 x) = u.1 x
    rw [← mul_assoc, ← Real.exp_add]
    simp

@[simp] theorem gaugeEquiv_apply (Λ u : Smooth) (x : State) :
    (gaugeEquiv Λ u).1 x = Real.exp (Λ.1 x) * u.1 x := rfl

@[simp] theorem gaugeEquiv_symm_apply (Λ u : Smooth) (x : State) :
    ((gaugeEquiv Λ).symm u).1 x = Real.exp (-Λ.1 x) * u.1 x := rfl

/-- Conjugation of actual operators, as an associative algebra equivalence. -/
def gaugeConjugation (Λ : Smooth) : Operator ≃ₐ[ℝ] Operator :=
  (gaugeEquiv Λ).conjAlgEquiv ℝ

/-- The same actual conjugation preserves Lie brackets. -/
def gaugeLieEquiv (Λ : Smooth) : Operator ≃ₗ⁅ℝ⁆ Operator :=
  (gaugeConjugation Λ).toLieEquiv

@[simp] theorem gaugeConjugation_apply (Λ : Smooth) (A : Operator) (u : Smooth) :
    gaugeConjugation Λ A u = gaugeEquiv Λ (A ((gaugeEquiv Λ).symm u)) := rfl

@[simp] theorem gaugeLieEquiv_apply (Λ : Smooth) (A : Operator) :
    gaugeLieEquiv Λ A = gaugeConjugation Λ A := rfl

/-- Gauge conjugation fixes every multiplication operator. -/
@[simp] theorem gaugeConjugation_multiplication (Λ u : Smooth) :
    gaugeConjugation Λ (multiplication u) = multiplication u := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext x
  change Real.exp (Λ.1 x) * (u.1 x * (Real.exp (-Λ.1 x) * v.1 x)) = u.1 x * v.1 x
  calc
    _ = (Real.exp (Λ.1 x) * Real.exp (-Λ.1 x)) * (u.1 x * v.1 x) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

/-- The new covariant drift, with the sign fixed by `exp Λ · A · exp (-Λ)`. -/
def gaugeDrift (Λ : Smooth) (f : Fin 3 → Smooth) : Fin 3 → Smooth :=
  fun i => f i + partialDerivative i Λ

@[simp] theorem gaugeConjugation_partialDerivative (Λ : Smooth) (i : Fin 3) :
    gaugeConjugation Λ (partialDerivative i) =
      partialDerivative i - multiplication (partialDerivative i Λ) := by
  apply LinearMap.ext
  intro u
  change smoothMul (smoothExp Λ)
      (partialDerivative i (smoothMul (smoothExp (-Λ)) u)) = _
  rw [partialDerivative_smoothMul, partialDerivative_smoothExp, map_neg]
  apply Subtype.ext
  funext x
  change Real.exp (Λ.1 x) *
    ((Real.exp (-Λ.1 x) * (-(partialDerivative i Λ).1 x)) * u.1 x +
      Real.exp (-Λ.1 x) * (partialDerivative i u).1 x) =
    (partialDerivative i u).1 x - (partialDerivative i Λ).1 x * u.1 x
  have he : Real.exp (Λ.1 x) * Real.exp (-Λ.1 x) = 1 := by
    rw [← Real.exp_add]; simp
  calc
    _ = (Real.exp (Λ.1 x) * Real.exp (-Λ.1 x)) *
      ((partialDerivative i u).1 x - (partialDerivative i Λ).1 x * u.1 x) := by ring
    _ = _ := by rw [he, one_mul]

@[simp] theorem gaugeConjugation_D (Λ : Smooth) (f : Fin 3 → Smooth) (i : Fin 3) :
    gaugeConjugation Λ (D f i) = D (gaugeDrift Λ f) i := by
  simp only [D, map_sub, gaugeConjugation_partialDerivative,
    gaugeConjugation_multiplication, gaugeDrift, multiplication_add]
  abel

/-- Mixed partial symmetry proves gauge invariance of each actual Wong function. -/
@[simp] theorem wong_gaugeDrift (Λ : Smooth) (f : Fin 3 → Smooth) (i j : Fin 3) :
    wong (gaugeDrift Λ f) i j = wong f i j := by
  simp only [wong, gaugeDrift, map_add]
  rw [partialDerivative_commute_apply i j]
  abel

theorem WongConstant_gaugeDrift_iff (Λ : Smooth) (f : Fin 3 → Smooth) :
    WongConstant (gaugeDrift Λ f) ↔ WongConstant f := by
  simp only [WongConstant, wong_gaugeDrift]

/-- The exact conjugated generator: the potential is the original `eta f h`. -/
theorem gaugeConjugation_L0 {m : ℕ} (Λ : Smooth) (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) :
    gaugeConjugation Λ (L0 f h) =
      (1 / 2 : ℝ) • (∑ i, D (gaugeDrift Λ f) i * D (gaugeDrift Λ f) i) -
        (1 / 2 : ℝ) • multiplication (eta f h) := by
  simp only [L0, map_sub, map_smul, map_sum, map_mul,
    gaugeConjugation_D, gaugeConjugation_multiplication]

/-- The image of an arbitrary Lie subalgebra under the actual gauge equivalence. -/
abbrev gaugeAlgebra (Λ : Smooth) (E : LieSubalgebra ℝ Operator) :
    LieSubalgebra ℝ Operator := E.map (gaugeLieEquiv Λ).toLieHom

/-- The original and gauge-transformed algebras are linearly and Lie isomorphic. -/
def gaugeAlgebraEquiv (Λ : Smooth) (E : LieSubalgebra ℝ Operator) :
    E ≃ₗ⁅ℝ⁆ gaugeAlgebra Λ E :=
  (gaugeLieEquiv Λ).ofSubalgebras E (gaugeAlgebra Λ E) rfl

theorem gaugeAlgebra_finiteDimensional (Λ : Smooth) (E : LieSubalgebra ℝ Operator)
    [FiniteDimensional ℝ E] : FiniteDimensional ℝ (gaugeAlgebra Λ E) :=
  (gaugeAlgebraEquiv Λ E).toLinearEquiv.finiteDimensional

@[simp] theorem multiplication_mem_gaugeAlgebra (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (u : Smooth) :
    multiplication u ∈ gaugeAlgebra Λ E ↔ multiplication u ∈ E := by
  constructor
  · rintro ⟨A, hA, he⟩
    have he' : gaugeConjugation Λ A = gaugeConjugation Λ (multiplication u) := by
      simpa using he
    exact (gaugeConjugation Λ).injective he' ▸ hA
  · intro hu
    exact ⟨multiplication u, hu, gaugeConjugation_multiplication Λ u⟩

theorem linearCoefficientSpace_gaugeAlgebra (Λ : Smooth) (E : LieSubalgebra ℝ Operator) :
    linearCoefficientSpace (gaugeAlgebra Λ E) = linearCoefficientSpace E := by
  ext a
  exact multiplication_mem_gaugeAlgebra Λ E (linearFunction a)

@[simp] theorem linearRank_gaugeAlgebra (Λ : Smooth) (E : LieSubalgebra ℝ Operator) :
    linearRank (gaugeAlgebra Λ E) = linearRank E := by
  rw [linearRank, linearCoefficientSpace_gaugeAlgebra]
  rfl

/-- Every operator acting by a pointwise scalar function is fixed, without
choosing a smoothness witness for that scalar function. -/
theorem gaugeConjugation_of_scalar_action (Λ : Smooth) (A : Operator) (φ : State → ℝ)
    (hA : ∀ (u : Smooth) (x : State), (A u).1 x = φ x * u.1 x) :
    gaugeConjugation Λ A = A := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  simp only [gaugeConjugation_apply, gaugeEquiv_apply, hA, gaugeEquiv_symm_apply]
  calc
    _ = (Real.exp (Λ.1 x) * Real.exp (-Λ.1 x)) * (φ x * u.1 x) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

/-- Quadratic-freeness is preserved for arbitrary actual Lie subalgebras. -/
theorem quadraticFree_gaugeAlgebra_iff (Λ : Smooth) (E : LieSubalgebra ℝ Operator) :
    QuadraticFree (gaugeAlgebra Λ E) ↔ QuadraticFree E := by
  constructor
  · intro hq p hp ⟨A, hA, hact⟩
    apply hq p hp
    refine ⟨A, ?_, hact⟩
    exact ⟨A, hA, gaugeConjugation_of_scalar_action Λ A _ hact⟩
  · intro hq p hp ⟨A, ⟨B, hB, he⟩, hact⟩
    apply hq p hp
    refine ⟨A, ?_, hact⟩
    have hfix := gaugeConjugation_of_scalar_action Λ A _ hact
    have hBA : B = A := (gaugeConjugation Λ).injective (he.trans hfix.symm)
    exact hBA ▸ hB

end Wong.SmoothModel
