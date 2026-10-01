import Wong.HiddenAxisLadder

/-!
# Genuine order-growth ladders along any momentum axis

The retained momentum axis is arbitrary. All three first momentum jets of
K are supplied, so a transverse transport in coordinate 2 is allowed even
when the retained momentum is visible. The ordinary differential-order
filtration and actual Lie membership are the proved smooth-operator ones.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Wong.SmoothModel
open MvPolynomial

def projectMomentumAxis (axis : Fin 3) : SmoothSymbol →ₐ[Smooth] SmoothSymbol :=
  aeval fun i : Fin 3 => if i = axis then X axis else 0

@[simp] theorem projectMomentumAxis_C (axis : Fin 3) (u : Smooth) :
    projectMomentumAxis axis (C u) = C u := by simp [projectMomentumAxis]

@[simp] theorem projectMomentumAxis_X (axis i : Fin 3) :
    projectMomentumAxis axis (X i) = if i = axis then X axis else 0 := by
  simp [projectMomentumAxis]

theorem projectMomentumAxis_coefficientDerivative (axis : Fin 3)
    (p : SmoothSymbol) (i : Fin 3) :
    projectMomentumAxis axis (symbolCoefficientDerivative i p) =
      symbolCoefficientDerivative i (projectMomentumAxis axis p) := by
  induction p using MvPolynomial.induction_on with
  | C u => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = axis
    · simp [map_mul, symbolCoefficientDerivative_mul, hp, hj]
    · simp [map_mul, symbolCoefficientDerivative_mul, hp, hj]

theorem coefficientDerivative_momentumAxisMonomial
    (axis i : Fin 3) (u : Smooth) (l : ℕ) :
    symbolCoefficientDerivative i (C u * X axis ^ l) =
      C (partialDerivative i u) * X axis ^ l := by
  rw [C_mul_X_pow_eq_monomial, symbolCoefficientDerivative_monomial,
    ← C_mul_X_pow_eq_monomial]

/-- Every same-order remainder is accounted for through the complete first
momentum jet. No quotient is applied to actual operators. -/
theorem projectMomentumAxis_poisson (axis : Fin 3) (k q : SmoothSymbol)
    (n l : ℕ) (c : ℝ) (v : Fin 3 → Smooth) (u : Smooth)
    (hk : projectMomentumAxis axis k = C (c • smoothOne) * X axis ^ (n+1))
    (hkj : ∀ i : Fin 3, projectMomentumAxis axis (pderiv i k) = C (v i) * X axis ^ n)
    (hq : projectMomentumAxis axis q = C u * X axis ^ l) :
    projectMomentumAxis axis (symbolPoisson k q) =
      C (∑ i : Fin 3, v i * partialDerivative i u) * X axis ^ (n+l) := by
  have hDk (i : Fin 3) : projectMomentumAxis axis (symbolCoefficientDerivative i k) = 0 := by
    rw [projectMomentumAxis_coefficientDerivative, hk,
      coefficientDerivative_momentumAxisMonomial, partialDerivative_const, map_zero, zero_mul]
  have hDq (i : Fin 3) : projectMomentumAxis axis (symbolCoefficientDerivative i q) =
      C (partialDerivative i u) * X axis ^ l := by
    rw [projectMomentumAxis_coefficientDerivative, hq, coefficientDerivative_momentumAxisMonomial]
  simp only [symbolPoisson, symbolFirstCorrection, map_sub, map_mul,
    Fin.sum_univ_three, hDk, hDq, hkj, mul_zero,
    add_zero, sub_zero, map_add, map_mul, pow_add]
  ring

theorem momentumAxis_principal_bracket (axis : Fin 3) (K Q : NormalForm) (n l : ℕ)
    (hK : NormalDegreeLE (n+1) K) (hQ : NormalDegreeLE (l+1) Q)
    (c : ℝ) (v : Fin 3 → Smooth) (u : Smooth)
    (hk : projectMomentumAxis axis (normalSymbol (n+1) K) =
      C (c • smoothOne) * X axis ^ (n+1))
    (hkj : ∀ i : Fin 3, projectMomentumAxis axis (pderiv i (normalSymbol (n+1) K)) =
      C (v i) * X axis ^ n)
    (hq : projectMomentumAxis axis (normalSymbol (l+1) Q) = C u * X axis ^ (l+1)) :
    projectMomentumAxis axis (normalSymbol (n+l+1) (normalBracket K Q)) =
      C (∑ i : Fin 3, v i * partialDerivative i u) * X axis ^ (n+l+1) := by
  rw [normalSymbol_bracket K Q n l hK hQ]
  simpa only [Nat.add_assoc] using
    projectMomentumAxis_poisson axis _ _ n (l+1) c v u hk hkj hq

theorem momentumAxisWords_projected (axis : Fin 3) (K Q : NormalForm) (n l : ℕ)
    (hK : NormalDegreeLE (n+1) K) (hQ : NormalDegreeLE (l+1) Q)
    (c lam : ℝ) (v : Fin 3 → Smooth) (u : Smooth)
    (hk : projectMomentumAxis axis (normalSymbol (n+1) K) =
      C (c • smoothOne) * X axis ^ (n+1))
    (hkj : ∀ i : Fin 3, projectMomentumAxis axis (pderiv i (normalSymbol (n+1) K)) =
      C (v i) * X axis ^ n)
    (hq : projectMomentumAxis axis (normalSymbol (l+1) Q) = C u * X axis ^ (l+1))
    (heigen : (∑ i : Fin 3, v i * partialDerivative i u) = lam • u)
    (r : ℕ) :
    projectMomentumAxis axis (normalSymbol (l+r*n+1) (hiddenAxisWords K Q r)) =
      C ((lam^r) • u) * X axis ^ (l+r*n+1) := by
  induction r with
  | zero => simpa only [hiddenAxisWords, Nat.zero_mul, Nat.add_zero, pow_zero, one_smul] using hq
  | succ r ih =>
    have hcoef : (∑ i : Fin 3, v i * partialDerivative i ((lam^r) • u)) =
        (lam^(r+1)) • u := by
      simp only [map_smul, mul_smul_comm, ← Finset.smul_sum, heigen, smul_smul, pow_succ]
    have hh := momentumAxis_principal_bracket axis K (hiddenAxisWords K Q r) n (l+r*n)
      hK (hiddenAxisWords_order K Q n l hK hQ r) c v ((lam^r) • u) hk hkj ih
    rw [hcoef] at hh
    have hi : n+(l+r*n)+1=l+(r+1)*n+1 := by
      simp only [Nat.add_mul, one_mul]
      omega
    simpa only [hiddenAxisWords, hi] using hh

theorem momentumAxisMonomial_ne_zero (axis : Fin 3) (u : Smooth) (l : ℕ) (hu : u ≠ 0) :
    (C u * X axis ^ l : SmoothSymbol) ≠ 0 := by
  intro hz
  have hc := congrArg (fun p : SmoothSymbol => p.coeff (Finsupp.single axis l)) hz
  apply hu
  simpa [C_mul_X_pow_eq_monomial] using hc

/-- The nonzero transported coefficient yields actual unbounded differential
order in the same finite-dimensional Lie algebra. -/
theorem actual_momentumAxis_eigen_ladder_obstruction
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (axis : Fin 3) (K Q : NormalForm) (n l : ℕ) (hn : 0 < n)
    (hKE : normalAction K ∈ E) (hQE : normalAction Q ∈ E)
    (hK : NormalDegreeLE (n+1) K) (hQ : NormalDegreeLE (l+1) Q)
    (c lam : ℝ) (hlam : lam ≠ 0) (v : Fin 3 → Smooth) (u : Smooth) (hu0 : u ≠ 0)
    (hk : projectMomentumAxis axis (normalSymbol (n+1) K) =
      C (c • smoothOne) * X axis ^ (n+1))
    (hkj : ∀ i : Fin 3, projectMomentumAxis axis (pderiv i (normalSymbol (n+1) K)) =
      C (v i) * X axis ^ n)
    (hq : projectMomentumAxis axis (normalSymbol (l+1) Q) = C u * X axis ^ (l+1))
    (heigen : (∑ i : Fin 3, v i * partialDerivative i u) = lam • u) : False := by
  obtain ⟨N, hN⟩ := actual_uniform_normal_weight_bound E.toSubmodule (fun α => α.degree)
  have hbound : NormalDegreeLE N (hiddenAxisWords K Q N) :=
    hN _ (hiddenAxisWords_mem E K Q hKE hQE N)
  have hNn : N ≤ N*n := Nat.le_mul_of_pos_right N hn
  have hz := normalSymbol_eq_zero_above_order (hiddenAxisWords K Q N) N (l+N*n+1)
    hbound (by omega)
  have hh := momentumAxisWords_projected axis K Q n l hK hQ c lam v u hk hkj hq heigen N
  rw [hz, map_zero] at hh
  exact momentumAxisMonomial_ne_zero axis ((lam^N) • u) _
    (smul_ne_zero (pow_ne_zero N hlam) hu0) hh.symm

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_momentumAxis_eigen_ladder_obstruction
