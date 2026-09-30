import Wong.PolynomialSmooth
import Wong.PolynomialAffinity
import Wong.SmoothGeometry
import Wong.RankStructure
import Mathlib.Tactic.FinCases

/-!
# Exact statement of the user-authorized published affinity input

Reference: Ji Shi and Stephen S.-T. Yau, SIAM J. Control Optim. 55(6)
(2017), 4227–4246, DOI 10.1137/16M1065471, Theorems 3.4 and 3.10.

This module defines, but does not assume, the external proposition. It also
proves the equivalence between its polynomial conclusion and the actual
affine matrix parametrization. No Bianchi or zero-slope conclusion is part
of the published input. The original globally smooth estimation algebra,
its homogeneous linear rank, and its original generator are retained.
-/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

/-- Exact affine conclusion, with the visible entry independent of x₂. -/
def AffineWong (f : Fin 3 → Smooth) : Prop :=
  ∃ p : Wong.AffineParameters, ∀ i j x, (wong f i j).1 x = p.matrix x i j

/-- The two published conclusions in polynomial language. The derivative
condition expresses precisely that the visible entry does not depend on
the hidden coordinate. Its equivalence to the affine parametrization is
proved below, rather than silently asserted. -/
def PublishedPolynomialWong (f : Fin 3 → Smooth) : Prop :=
  ∃ p₀₁ p₀₂ p₁₂ : RealPoly,
    p₀₁.totalDegree ≤ 1 ∧ p₀₂.totalDegree ≤ 1 ∧ p₁₂.totalDegree ≤ 1 ∧
    pderiv 2 p₀₁ = 0 ∧
    polynomialSmooth p₀₁ = wong f 0 1 ∧
    polynomialSmooth p₀₂ = wong f 0 2 ∧
    polynomialSmooth p₁₂ = wong f 1 2

/-- Positive observation dimension matches the literal filtering model in
the source. The zero-observation rank-two branch must be closed separately.
There is deliberately no quadratic-freeness assumption. -/
def ShiYauAffineStructure : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h →
    multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h →
    PublishedPolynomialWong f

/-- A genuine polynomial representing a specified affine smooth function. -/
def affineScalarPolynomial (c : ℝ) (a : State) : RealPoly :=
  C c + ∑ i : Fin 3, C (a i) * X i

theorem affineScalarPolynomial_degree_le_one (c : ℝ) (a : State) :
    (affineScalarPolynomial c a).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simp)

theorem polynomialSmooth_affineScalarPolynomial (c : ℝ) (a : State) :
    polynomialSmooth (affineScalarPolynomial c a) = c • smoothOne + linearFunction a := by
  apply Subtype.ext
  funext x
  simp [affineScalarPolynomial, polynomialSmooth, smoothOne, linearFunction]

theorem pderiv_affineScalarPolynomial (c : ℝ) (a : State) (j : Fin 3) :
    pderiv j (affineScalarPolynomial c a) = C (a j) := by
  simp [affineScalarPolynomial, Pi.single_apply, mul_ite]

theorem polynomialSmooth_affine_of_degree_le_one (p : RealPoly)
    (hp : p.totalDegree ≤ 1) :
    polynomialSmooth p = p.coeff 0 • smoothOne +
      linearFunction (fun i => p.coeff (Finsupp.single i 1)) := by
  apply Subtype.ext
  funext x
  simpa [smoothOne, linearFunction] using
    Wong.PolynomialAffinity.eval_eq_affine p hp x

theorem affineWong_iff_publishedPolynomialWong (f : Fin 3 → Smooth) :
    AffineWong f ↔ PublishedPolynomialWong f := by
  constructor
  · rintro ⟨p, hp⟩
    let a₀₁ : State := ![p.b₁, p.b₂, 0]
    let a₀₂ : State := ![p.k₁, p.k₂, p.k₃]
    let a₁₂ : State := ![p.h₁, p.h₂, p.h₃]
    refine ⟨affineScalarPolynomial p.b₀ a₀₁,
      affineScalarPolynomial p.k₀ a₀₂,
      affineScalarPolynomial p.h₀ a₁₂,
      affineScalarPolynomial_degree_le_one _ _,
      affineScalarPolynomial_degree_le_one _ _,
      affineScalarPolynomial_degree_le_one _ _, ?_, ?_, ?_, ?_⟩
    · rw [pderiv_affineScalarPolynomial]
      simp [a₀₁]
    · apply Subtype.ext
      funext x
      rw [hp 0 1 x]
      simp [polynomialSmooth, affineScalarPolynomial, a₀₁,
        Wong.AffineParameters.matrix, Wong.AffineParameters.w12, Fin.sum_univ_three]
      ring
    · apply Subtype.ext
      funext x
      rw [hp 0 2 x]
      simp [polynomialSmooth, affineScalarPolynomial, a₀₂,
        Wong.AffineParameters.matrix, Wong.AffineParameters.w13, Fin.sum_univ_three]
      ring
    · apply Subtype.ext
      funext x
      rw [hp 1 2 x]
      simp [polynomialSmooth, affineScalarPolynomial, a₁₂,
        Wong.AffineParameters.matrix, Wong.AffineParameters.w23, Fin.sum_univ_three]
      ring
  · rintro ⟨p₀₁, p₀₂, p₁₂, hd₀₁, hd₀₂, hd₁₂, hhidden, he₀₁, he₀₂, he₁₂⟩
    let a₀₁ : State := fun i => p₀₁.coeff (Finsupp.single i 1)
    have ha₀₁ : a₀₁ 2 = 0 := by
      have he := congrArg (partialDerivative 2)
        (polynomialSmooth_affine_of_degree_le_one p₀₁ hd₀₁)
      rw [partialDerivative_polynomialSmooth, hhidden, polynomialSmooth_zero,
        map_add, partialDerivative_const, partialDerivative_linearFunction,
        zero_add] at he
      have hv := congrArg (fun u : Smooth => u.1 (0 : State)) he
      simpa [a₀₁, smoothOne] using hv.symm
    let p : Wong.AffineParameters :=
      ⟨p₀₁.coeff 0, a₀₁ 0, a₀₁ 1,
        p₀₂.coeff 0, p₀₂.coeff (Finsupp.single 0 1),
        p₀₂.coeff (Finsupp.single 1 1), p₀₂.coeff (Finsupp.single 2 1),
        p₁₂.coeff 0, p₁₂.coeff (Finsupp.single 0 1),
        p₁₂.coeff (Finsupp.single 1 1), p₁₂.coeff (Finsupp.single 2 1)⟩
    have h₀₁ (x : State) : (wong f 0 1).1 x = p.w12 x := by
      rw [← he₀₁]
      have he := Wong.PolynomialAffinity.eval_eq_affine p₀₁ hd₀₁ x
      simpa [p, a₀₁, Wong.AffineParameters.w12, Fin.sum_univ_three, ha₀₁,
        add_comm, add_left_comm] using he
    have h₀₂ (x : State) : (wong f 0 2).1 x = p.w13 x := by
      rw [← he₀₂]
      have he := Wong.PolynomialAffinity.eval_eq_affine p₀₂ hd₀₂ x
      simpa [p, Wong.AffineParameters.w13, Fin.sum_univ_three, add_comm, add_left_comm] using he
    have h₁₂ (x : State) : (wong f 1 2).1 x = p.w23 x := by
      rw [← he₁₂]
      have he := Wong.PolynomialAffinity.eval_eq_affine p₁₂ hd₁₂ x
      simpa [p, Wong.AffineParameters.w23, Fin.sum_univ_three, add_comm, add_left_comm] using he
    refine ⟨p, ?_⟩
    intro i j x
    fin_cases i <;> fin_cases j
    · simp [Wong.AffineParameters.matrix]
    · simpa [Wong.AffineParameters.matrix] using h₀₁ x
    · simpa [Wong.AffineParameters.matrix] using h₀₂ x
    · change (wong f 1 0).1 x = -p.w12 x
      have he := congrArg (fun u : Smooth => u.1 x) (wong_skew f 0 1)
      exact he.trans (congrArg Neg.neg (h₀₁ x))
    · simp [Wong.AffineParameters.matrix]
    · simpa [Wong.AffineParameters.matrix] using h₁₂ x
    · change (wong f 2 0).1 x = -p.w13 x
      have he := congrArg (fun u : Smooth => u.1 x) (wong_skew f 0 2)
      exact he.trans (congrArg Neg.neg (h₀₂ x))
    · change (wong f 2 1).1 x = -p.w23 x
      have he := congrArg (fun u : Smooth => u.1 x) (wong_skew f 1 2)
      exact he.trans (congrArg Neg.neg (h₁₂ x))
    · simp [Wong.AffineParameters.matrix]

end Wong.SmoothModel
