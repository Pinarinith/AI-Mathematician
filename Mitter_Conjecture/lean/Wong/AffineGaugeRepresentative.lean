import Wong.PublishedAffineStatement

/-!
# A polynomial representative of the actual affine Wong tensor

The Bianchi relation is derived from genuine mixed partial derivatives;
it is not included in the external affinity input. The explicit polynomial
drift is the triangular Poincaré representative used in the manuscript.
-/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

theorem affineWong_smooth_entries (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    wong f 0 1 = polynomialSmooth (affineScalarPolynomial p.b₀ ![p.b₁, p.b₂, 0]) ∧
    wong f 0 2 = polynomialSmooth (affineScalarPolynomial p.k₀ ![p.k₁, p.k₂, p.k₃]) ∧
    wong f 1 2 = polynomialSmooth (affineScalarPolynomial p.h₀ ![p.h₁, p.h₂, p.h₃]) := by
  constructor
  · apply Subtype.ext
    funext x
    rw [hform 0 1 x]
    simp [Wong.AffineParameters.matrix, Wong.AffineParameters.w12,
      polynomialSmooth, affineScalarPolynomial, Fin.sum_univ_three]
    ring
  constructor
  · apply Subtype.ext
    funext x
    rw [hform 0 2 x]
    simp [Wong.AffineParameters.matrix, Wong.AffineParameters.w13,
      polynomialSmooth, affineScalarPolynomial, Fin.sum_univ_three]
    ring
  · apply Subtype.ext
    funext x
    rw [hform 1 2 x]
    simp [Wong.AffineParameters.matrix, Wong.AffineParameters.w23,
      polynomialSmooth, affineScalarPolynomial, Fin.sum_univ_three]
    ring

theorem affineWong_bianchi_parameters (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j) : p.h₁ = p.k₂ := by
  obtain ⟨hw, hu, hv⟩ := affineWong_smooth_entries f p hform
  have he := wong_bianchi f 0 1 2
  rw [hw, hu, hv] at he
  simp only [partialDerivative_polynomialSmooth, pderiv_affineScalarPolynomial,
    Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero,
    polynomialSmooth_C] at he
  have hr := congrArg (fun u : Smooth => u.1 (0 : State)) he
  simp [smoothOne] at hr
  linarith

def triangularDriftPolynomials (p : Wong.AffineParameters) : Fin 3 → RealPoly :=
  ![0,
    C (p.b₁ / 2) * X 0 ^ 2 + C p.b₂ * X 0 * X 1 + C p.b₀ * X 0,
    C (p.k₁ / 2) * X 0 ^ 2 + C p.k₂ * X 0 * X 1 +
      C p.k₃ * X 0 * X 2 + C p.k₀ * X 0 +
      C (p.h₂ / 2) * X 1 ^ 2 + C p.h₃ * X 1 * X 2 + C p.h₀ * X 1]

def triangularDrift (p : Wong.AffineParameters) : Fin 3 → Smooth :=
  fun i => polynomialSmooth (triangularDriftPolynomials p i)

theorem triangularDrift_wong_visible (p : Wong.AffineParameters) (x : State) :
    (wong (triangularDrift p) 0 1).1 x = p.w12 x := by
  simp only [wong, triangularDrift]
  rw [partialDerivative_polynomialSmooth, partialDerivative_polynomialSmooth]
  simp [triangularDriftPolynomials,
    polynomialSmooth, Wong.AffineParameters.w12]
  ring

theorem triangularDrift_wong_first_hidden (p : Wong.AffineParameters) (x : State) :
    (wong (triangularDrift p) 0 2).1 x = p.w13 x := by
  simp only [wong, triangularDrift]
  rw [partialDerivative_polynomialSmooth, partialDerivative_polynomialSmooth]
  simp [triangularDriftPolynomials,
    polynomialSmooth, Wong.AffineParameters.w13]
  ring

theorem triangularDrift_wong_second_hidden (p : Wong.AffineParameters)
    (hb : p.h₁ = p.k₂) (x : State) :
    (wong (triangularDrift p) 1 2).1 x = p.w23 x := by
  simp only [wong, triangularDrift]
  rw [partialDerivative_polynomialSmooth, partialDerivative_polynomialSmooth]
  simp [triangularDriftPolynomials,
    polynomialSmooth, Wong.AffineParameters.w23, hb]
  ring

theorem triangularDrift_wong_eq (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    ∀ i j, wong f i j = wong (triangularDrift p) i j := by
  have hb := affineWong_bianchi_parameters f p hform
  have h₀₁ : wong f 0 1 = wong (triangularDrift p) 0 1 := by
    apply Subtype.ext
    funext x
    rw [triangularDrift_wong_visible, hform]
    rfl
  have h₀₂ : wong f 0 2 = wong (triangularDrift p) 0 2 := by
    apply Subtype.ext
    funext x
    rw [triangularDrift_wong_first_hidden, hform]
    rfl
  have h₁₂ : wong f 1 2 = wong (triangularDrift p) 1 2 := by
    apply Subtype.ext
    funext x
    rw [triangularDrift_wong_second_hidden p hb, hform]
    rfl
  intro i j
  fin_cases i <;> fin_cases j
  · simp
  · exact h₀₁
  · exact h₀₂
  · change wong f 1 0 = wong (triangularDrift p) 1 0
    exact (wong_skew f 0 1).trans ((congrArg Neg.neg h₀₁).trans
      (wong_skew (triangularDrift p) 0 1).symm)
  · simp
  · exact h₁₂
  · change wong f 2 0 = wong (triangularDrift p) 2 0
    exact (wong_skew f 0 2).trans ((congrArg Neg.neg h₀₂).trans
      (wong_skew (triangularDrift p) 0 2).symm)
  · change wong f 2 1 = wong (triangularDrift p) 2 1
    exact (wong_skew f 1 2).trans ((congrArg Neg.neg h₁₂).trans
      (wong_skew (triangularDrift p) 1 2).symm)
  · simp

end Wong.SmoothModel
