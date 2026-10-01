import Wong.RootAnalyticBridges
import Wong.PublishedAffineStatement

/-! Global smooth regularity from actual derivative equations. All degree
bounds refer to the faithful polynomial evaluation embedding. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

theorem smooth_eq_constant_of_partials_zero (u : Smooth)
    (hu : ∀ i : Fin 3, partialDerivative i u = 0) :
    u = u.1 0 • smoothOne := by
  obtain ⟨c, hc⟩ := (smooth_constant_iff_partials_zero u).mpr hu
  apply Subtype.ext
  funext x
  simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, smoothOne, mul_one]
    using (hc x).trans (hc 0).symm

theorem smooth_affine_of_constant_partials (u : Smooth) (a : State)
    (hu : ∀ i : Fin 3, partialDerivative i u = a i • smoothOne) :
    u = u.1 0 • smoothOne + linearFunction a := by
  let w := u - linearFunction a
  have hw : ∀ i : Fin 3, partialDerivative i w = 0 := by
    intro i
    simp only [w, map_sub, hu, partialDerivative_linearFunction, sub_self]
  have he := smooth_eq_constant_of_partials_zero w hw
  have hw0 : w.1 0 = u.1 0 := by simp [w, linearFunction]
  rw [hw0] at he
  exact sub_eq_iff_eq_add.mp he

theorem polynomial_degree_le_succ_of_pderiv_bounds (p : RealPoly) (d : ℕ)
    (hp : ∀ i : Fin 3, (pderiv i p).totalDegree ≤ d) :
    p.totalDegree ≤ d + 1 := by
  have hg : (Wong.PolynomialGradient.gradientSquare p).totalDegree ≤ 2*d := by
    apply totalDegree_finsetSum_le
    intro i _hi
    exact (totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (hp i))
  by_cases hz : p.totalDegree = 0
  · omega
  · rw [Wong.PolynomialGradient.gradientSquare_totalDegree p (by omega)] at hg
    omega

theorem smooth_polynomial_of_polynomial_gradient_bounds (u : Smooth) (d : ℕ)
    (hu : ∀ i : Fin 3, ∃ p : RealPoly,
      p.totalDegree ≤ d ∧ polynomialSmooth p = partialDerivative i u) :
    ∃ p : RealPoly, p.totalDegree ≤ d+1 ∧ polynomialSmooth p = u := by
  obtain ⟨p, he⟩ := polynomial_of_polynomial_gradient u (by
    intro i
    obtain ⟨q, _hq, heq⟩ := hu i
    exact ⟨q, heq.symm⟩)
  refine ⟨p, polynomial_degree_le_succ_of_pderiv_bounds p d ?_, he.symm⟩
  intro i
  obtain ⟨q, hq, heq⟩ := hu i
  have hpoly : pderiv i p = q := by
    apply polynomialSmooth_injective
    rw [← partialDerivative_polynomialSmooth, ← he, ← heq]
  rwa [hpoly]

theorem smooth_quadratic_of_third_partials_zero (u : Smooth)
    (hu : ∀ i j k : Fin 3,
      partialDerivative i (partialDerivative j (partialDerivative k u)) = 0) :
    ∃ p : RealPoly, p.totalDegree ≤ 2 ∧ polynomialSmooth p = u := by
  apply smooth_polynomial_of_polynomial_gradient_bounds u 1
  intro i
  let a : State := fun j => (partialDerivative j (partialDerivative i u)).1 0
  have ha (j : Fin 3) : partialDerivative j (partialDerivative i u) = a j • smoothOne :=
    smooth_eq_constant_of_partials_zero _ (fun k => hu k j i)
  have he := smooth_affine_of_constant_partials (partialDerivative i u) a ha
  exact ⟨affineScalarPolynomial ((partialDerivative i u).1 0) a,
    affineScalarPolynomial_degree_le_one _ _,
    (polynomialSmooth_affineScalarPolynomial _ _).trans he.symm⟩

theorem smooth_polynomial_third_partials_zero (p : RealPoly)
    (hp : p.totalDegree ≤ 2) (i j k : Fin 3) :
    partialDerivative i (partialDerivative j (partialDerivative k (polynomialSmooth p))) = 0 := by
  have hk := Wong.PolynomialGradient.partial_totalDegree_le p k
  have hj := Wong.PolynomialGradient.partial_totalDegree_le (pderiv k p) j
  have hz : (pderiv j (pderiv k p)).totalDegree = 0 := by omega
  have he := totalDegree_eq_zero_iff_eq_C.mp hz
  simp only [partialDerivative_polynomialSmooth]
  rw [he, pderiv_C, polynomialSmooth_zero]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.smooth_quadratic_of_third_partials_zero
#print axioms Wong.SmoothModel.smooth_polynomial_of_polynomial_gradient_bounds
