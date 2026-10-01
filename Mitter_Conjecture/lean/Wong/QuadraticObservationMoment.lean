import Wong.PolynomialRayLift
import Wong.PolynomialTopRemainder

/-! The fourth coefficient of the quadratic-observation test moment is the
negative sum of squared highest homogeneous values, times the actual mass.
This file is purely algebraic: no Riccati bound or estimation-algebra conclusion
is assumed or encoded in the definitions. -/
noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

def quadraticObservationMoment {m : ℕ} (F : RealPoly →ₗ[ℝ] ℝ)
    (v : State) (Q : RealPoly) (P : Fin m → RealPoly) : Polynomial ℝ :=
  rayMoment F v Q - ∑ j : Fin m, rayMoment F v ((P j)^2)

theorem quadraticObservationMoment_degree {m : ℕ} (F : RealPoly →ₗ[ℝ] ℝ)
    (v : State) (Q : RealPoly) (P : Fin m → RealPoly)
    (hQ : Q.totalDegree ≤ 2) (hP : ∀j, (P j).totalDegree ≤ 2) :
    (quadraticObservationMoment F v Q P).natDegree ≤ 4 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (rayMoment_degree F v Q).trans (hQ.trans (by decide))
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    change (polynomialMoment F (rayLift v ((P j)^2))).natDegree ≤ 4
    apply (polynomialMoment_degree F _).trans
    rw [map_pow]
    exact Polynomial.natDegree_pow_le.trans
      (Nat.mul_le_mul_left 2 ((rayLift_natDegree_le v (P j)).trans (hP j)))

theorem quadraticObservationMoment_coeff_four {m : ℕ} (F : RealPoly →ₗ[ℝ] ℝ)
    (v : State) (Q : RealPoly) (P : Fin m → RealPoly)
    (hQ : Q.totalDegree ≤ 2) (hP : ∀j, (P j).totalDegree ≤ 2) :
    (quadraticObservationMoment F v Q P).coeff 4 =
      -(∑j : Fin m, (eval v (homogeneousComponent 2 (P j)))^2) * F 1 := by
  have hzero : (rayMoment F v Q).coeff 4 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((rayMoment_degree F v Q).trans_lt (hQ.trans_lt (by decide)))
  have hsquare (j : Fin m) : (rayMoment F v ((P j)^2)).coeff 4 =
      (eval v (homogeneousComponent 2 (P j)))^2 * F 1 := by
    simpa using rayMoment_square_coeff F v (P j) 2 (hP j)
  rw [quadraticObservationMoment, Polynomial.coeff_sub,
    Polynomial.finsetSum_coeff, hzero, zero_sub]
  simp only [hsquare]
  rw [← Finset.sum_mul, neg_mul]

/-- Nonnegative fourth coefficients in every real direction force every
quadratic highest observation component to vanish.  The only condition on the
linear functional is its strictly positive value on the constant polynomial. -/
theorem quadratic_observations_affine_of_ray_coeff_nonnegative {m : ℕ}
    (F : RealPoly →ₗ[ℝ] ℝ) (Q : RealPoly) (P : Fin m → RealPoly)
    (hQ : Q.totalDegree ≤ 2) (hP : ∀j, (P j).totalDegree ≤ 2)
    (hmass : 0 < F 1)
    (hnonneg : ∀v : State, 0 ≤ (quadraticObservationMoment F v Q P).coeff 4) :
    ∀j, (P j).totalDegree ≤ 1 := by
  have hsumzero (v : State) :
      (∑j : Fin m, (eval v (homogeneousComponent 2 (P j)))^2) = 0 := by
    have hh := hnonneg v
    rw [quadraticObservationMoment_coeff_four F v Q P hQ hP] at hh
    have hs : 0 ≤ ∑j : Fin m, (eval v (homogeneousComponent 2 (P j)))^2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    apply le_antisymm _ hs
    apply le_of_not_gt
    intro hpos
    have hp := mul_pos hpos hmass
    nlinarith
  have htop (j : Fin m) : homogeneousComponent 2 (P j) = 0 := by
    apply MvPolynomial.funext
    intro v
    have hh := Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) =>
        sq_nonneg (eval v (homogeneousComponent 2 (P k)))) (Finset.mem_univ j)
    rw [hsumzero v] at hh
    simp only [map_zero]
    nlinarith [sq_nonneg (eval v (homogeneousComponent 2 (P j)))]
  intro j
  have hd := polynomial_sub_top_component_degree_le (P j) 2 (by decide) (hP j)
  simpa only [htop j, sub_zero, Nat.reduceSub] using hd

end Wong.SmoothModel

#print axioms Wong.SmoothModel.quadratic_observations_affine_of_ray_coeff_nonnegative
