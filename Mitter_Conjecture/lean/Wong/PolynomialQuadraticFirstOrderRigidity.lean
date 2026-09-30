import Wong.FunctionQuadraticRankConstraints
import Wong.QuadraticHiddenRigidity
import Wong.QuadraticVisibleRigidity
import Wong.SymmetricMatrixEigenvector

/-!
# Genuine quadratic first-order coefficients are affine

This integrates the real spectral obstruction and the visible-axis order ladder.
All hypotheses concern the actual finite-dimensional smooth estimation algebra,
an actual first-order member, and its polynomial principal coefficients.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Wong.SmoothModel
open MvPolynomial

/-- Constant polynomial first derivatives force degree at most one. -/
theorem polynomial_degree_le_one_of_constant_pderivs (p : RealPoly) (c : Fin 3 → ℝ)
    (hc : ∀ i, pderiv i p = C (c i)) : p.totalDegree ≤ 1 := by
  have hg : Wong.PolynomialGradient.gradientSquare p = C (∑ i : Fin 3, (c i)^2) := by
    simp only [Wong.PolynomialGradient.gradientSquare, hc, ← map_pow, ← map_sum]
  by_contra hn
  have hd : 0 < p.totalDegree := by omega
  have he := Wong.PolynomialGradient.gradientSquare_totalDegree p hd
  rw [hg, totalDegree_C] at he
  omega

/-- Affine polynomials have zero actual smooth Hessian. -/
theorem polynomialSmooth_hessian_zero_of_degree_le_one (p : RealPoly)
    (hp : p.totalDegree ≤ 1) (i j : Fin 3) :
    partialDerivative i (partialDerivative j (polynomialSmooth p)) = 0 := by
  obtain ⟨c, a, he⟩ := polynomialSmooth_exists_affine_of_degree_le_one p hp
  rw [he, map_add, partialDerivative_const, partialDerivative_linearFunction, zero_add,
    partialDerivative_const]

/-- Finite dimensionality rules out every quadratic hidden coefficient once the
visible principal coefficients are affine and independent of the hidden variable.
No Wong-affinity theorem or quadratic-freeness assumption is used. -/
theorem actual_polynomial_quadratic_firstOrder_hidden_degree_le_one {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD₀ : D f 0 ∈ estimationAlgebra f h) (hD₁ : D f 1 ∈ estimationAlgebra f h)
    (p : NormalForm) (hp : NormalDegreeLE 1 p)
    (hpE : normalAction p ∈ estimationAlgebra f h)
    (P : Fin 3 → RealPoly)
    (hpa : normalSymbol 1 p = principalVectorSymbol (fun i => polynomialSmooth (P i)))
    (hvisible : ∀ i : Fin 3, i ≠ 2 → (P i).totalDegree ≤ 1)
    (hquadratic : (P 2).totalDegree ≤ 2)
    (h₀ : partialDerivative 2 (polynomialSmooth (P 0)) = 0)
    (h₁ : partialDerivative 2 (polynomialSmooth (P 1)) = 0) :
    (P 2).totalDegree ≤ 1 := by
  classical
  have hlinzero : linearFunction (0 : State) = 0 := by
    apply Subtype.ext
    funext x
    simp [linearFunction]
  have hfirst (j : Fin 3) : ∃ c : ℝ, ∃ b : State,
      partialDerivative j (polynomialSmooth (P 2)) = c • smoothOne + linearFunction b := by
    rw [partialDerivative_polynomialSmooth]
    apply polynomialSmooth_exists_affine_of_degree_le_one
    have hd := Wong.PolynomialGradient.partial_totalDegree_le (P 2) j
    omega
  choose c b hb using hfirst
  let Q : Matrix (Fin 3) (Fin 3) ℝ := fun i j => b j i
  have hH (i j k : Fin 3) :
      partialDerivative i (partialDerivative j (polynomialSmooth (P k))) =
        if k = 2 then Q i j • smoothOne else 0 := by
    by_cases hk : k = 2
    · subst k
      rw [ite_eq_left rfl, hb j, map_add, partialDerivative_const,
        partialDerivative_linearFunction, zero_add]
    · rw [ite_eq_right hk]
      exact polynomialSmooth_hessian_zero_of_degree_le_one (P k) (hvisible k hk) i j
  have hQ : Q.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have hij := partialDerivative_commute_apply j i (polynomialSmooth (P 2))
    rw [hH, hH, ite_eq_left rfl, ite_eq_left rfl] at hij
    have he := congrArg (fun u : Smooth => u.1 (0 : State)) hij
    simpa [smoothOne] using he
  have hcolumn : Q.mulVec (Pi.single (2 : Fin 3) 1) = 0 := by
    by_contra hn
    obtain ⟨lam, v, hlam, hv₂, hv⟩ :=
      Wong.symmetric_three_hidden_column_eigenvector Q hQ hn
    exact hlam (actual_quadratic_hidden_eigenvalue_zero f h p hp hpE
      (fun i => polynomialSmooth (P i)) hpa Q hH v lam hv hv₂)
  have hb₂ (i : Fin 3) : b 2 i = 0 := by
    have hi := congrFun hcolumn i
    change (∑ j : Fin 3, b j i * (coordinateVector 2) j) = 0 at hi
    simpa [Fin.sum_univ_three, coordinateVector, Pi.single_apply] using hi
  have hbhidden (i : Fin 3) : b i 2 = 0 := by
    have hi := Matrix.IsSymm.ext_iff.mp hQ i 2
    change b i 2 = b 2 i at hi
    exact hi.trans (hb₂ i)
  have hcross : b 1 0 = b 0 1 := Matrix.IsSymm.ext_iff.mp hQ 1 0
  have hbzero₂ : b 2 = 0 := funext hb₂
  have hbshape₀ : b 0 = ![b 0 0, b 0 1, 0] := by
    funext i
    fin_cases i <;> simp [hbhidden]
  have hbshape₁ : b 1 = ![b 0 1, b 1 1, 0] := by
    funext i
    fin_cases i <;> simp [hbhidden, hcross]
  have hg₂ : partialDerivative 2 (polynomialSmooth (P 2)) = c 2 • smoothOne := by
    rw [hb 2, hbzero₂]
    simp only [hlinzero, add_zero]
  have hg₀ : partialDerivative 0 (polynomialSmooth (P 2)) =
      hiddenAxisAffineCoefficient (c 0) (b 0 0) (b 0 1) := by
    rw [hb 0, hbshape₀]
    rfl
  have hg₁ : partialDerivative 1 (polynomialSmooth (P 2)) =
      hiddenAxisAffineCoefficient (c 1) (b 0 1) (b 1 1) := by
    rw [hb 1, hbshape₁]
    rfl
  obtain ⟨hk, hd, hq⟩ := actual_quadratic_visible_hessian_zero f h hD₀ hD₁ p hp hpE
    (fun i => polynomialSmooth (P i)) hpa (c 2) (c 0) (c 1)
    (b 0 0) (b 0 1) (b 1 1) h₀ h₁ hg₂ hg₀ hg₁
  have hbzero₀ : b 0 = 0 := by
    rw [hbshape₀, hk, hd]
    funext i
    fin_cases i <;> rfl
  have hbzero₁ : b 1 = 0 := by
    rw [hbshape₁, hd, hq]
    funext i
    fin_cases i <;> rfl
  have hbzero (i : Fin 3) : b i = 0 := by
    fin_cases i
    · exact hbzero₀
    · exact hbzero₁
    · exact hbzero₂
  apply polynomial_degree_le_one_of_constant_pderivs (P 2) c
  intro i
  apply polynomialSmooth_injective
  rw [← partialDerivative_polynomialSmooth, hb i, hbzero i, polynomialSmooth_C]
  simp only [hlinzero, add_zero]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.polynomial_degree_le_one_of_constant_pderivs
#print axioms Wong.SmoothModel.polynomialSmooth_hessian_zero_of_degree_le_one
#print axioms Wong.SmoothModel.actual_polynomial_quadratic_firstOrder_hidden_degree_le_one
