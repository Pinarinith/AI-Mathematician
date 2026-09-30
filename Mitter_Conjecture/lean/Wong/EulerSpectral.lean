import Wong.EulerFalling
import Wong.EulerGeneralFinite

/-!
# Actual finite integer-weight decomposition and Lie-word projection

A squarefree integer-root annihilator produces a genuine finite
Euler eigenspace decomposition. The visible multiplier perturbation is
nilpotent on each finite-order component. CRT then projects each component
by a polynomial in the actual adjoint of the element belonging to the algebra.
-/
noncomputable section
namespace Wong.EulerSpectral
open Polynomial
open Wong.SmoothModel
set_option maxHeartbeats 1000000

theorem integer_linear_coprime (i j : ℤ) (hij : i ≠ j) :
    IsCoprime (X - C (i : ℝ)) (X - C (j : ℝ)) := by
  apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
  apply isUnit_iff_ne_zero.mpr
  apply sub_ne_zero.mpr
  exact_mod_cast hij

theorem integer_product_dvd (s : Finset ℤ) (p : Polynomial ℝ)
    (hp : ∀ w ∈ s, p.eval (w : ℝ) = 0) : integerWeightPolynomial s ∣ p := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact integer_linear_coprime i j hij
  · intro w hw
    exact Polynomial.dvd_iff_isRoot.mpr (hp w hw)

/-- A squarefree annihilator at distinct integer weights gives actual
polynomials in D whose values sum to v and are true eigenvectors. -/
theorem integer_spectral_decomposition {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Module.End ℝ V) (s : Finset ℤ) (v : V)
    (hv : (aeval D (integerWeightPolynomial s)) v = 0) :
    ∃ p : ℤ → Polynomial ℝ,
      (∑ w ∈ s, (aeval D (p w)) v) = v ∧
      ∀ w ∈ s, D ((aeval D (p w)) v) = (w : ℝ) • (aeval D (p w)) v := by
  classical
  have hproj (i : ℤ) : ∃ p : Polynomial ℝ, ∀ j ∈ s,
      X - C (j : ℝ) ∣ p - if j = i then 1 else 0 := by
    apply Wong.EulerAlgebra.exists_coprime_projection s i (fun j => X - C (j : ℝ))
    intro j hj hji
    exact integer_linear_coprime i j hji.symm
  choose p hp using hproj
  have heval (i j : ℤ) (hj : j ∈ s) : (p i).eval (j : ℝ) = if j = i then 1 else 0 := by
    have hi := Polynomial.dvd_iff_isRoot.mp (hp i j hj)
    apply sub_eq_zero.mp
    by_cases hji : j = i <;> simpa [Polynomial.IsRoot, hji] using hi
  have hsumdiv : integerWeightPolynomial s ∣ (∑ i ∈ s, p i) - 1 := by
    apply integer_product_dvd
    intro j hj
    simp only [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_one]
    simp_rw [heval _ j hj]
    simp [hj]
  refine ⟨p, ?_, ?_⟩
  · have he := Wong.EulerAlgebra.aeval_apply_eq_of_dvd_sub D
      (∑ i ∈ s, p i) 1 (integerWeightPolynomial s) v hv hsumdiv
    simpa only [map_sum, LinearMap.sum_apply, map_one, Module.End.one_apply] using he
  · intro i hi
    have hdiv : integerWeightPolynomial s ∣ (X - C (i : ℝ)) * p i := by
      apply integer_product_dvd
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · simp [heval i j hj, hji]
    have he := Wong.EulerAlgebra.aeval_apply_eq_of_dvd_sub D
      ((X - C (i : ℝ)) * p i) 0 (integerWeightPolynomial s) v hv
      (by simpa only [sub_zero] using hdiv)
    have hz : D ((aeval D (p i)) v) - (i : ℝ) • (aeval D (p i)) v = 0 := by
      simpa only [map_mul, Module.End.mul_apply, map_sub, LinearMap.sub_apply,
        Polynomial.aeval_X, Polynomial.aeval_C, Module.algebraMap_end_apply,
        map_zero, LinearMap.zero_apply] using he
    exact sub_eq_zero.mp hz

end Wong.EulerSpectral

namespace Wong.SmoothModel
open Polynomial
set_option maxHeartbeats 1000000

theorem hiddenEuler_mem_finiteOrderAlgebra : hiddenEuler ∈ finiteOrderAlgebra := by
  refine ⟨1, ?_⟩
  exact mul_mem_orderSpace (multiplication_mem_orderSpace_zero _) (partialDerivative_mem_orderSpace_one 2)

theorem hiddenEuler_polynomial_mem_finiteOrderAlgebra (Q : Polynomial ℝ) (P : Operator)
    (hP : P ∈ finiteOrderAlgebra) :
    (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) P ∈ finiteOrderAlgebra := by
  exact Wong.EulerAlgebra.aeval_mem_of_invariant finiteOrderAlgebra.toSubmodule
    (LieAlgebra.ad ℝ Operator hiddenEuler)
    (fun A hA => finiteOrderAlgebra.lie_mem hiddenEuler_mem_finiteOrderAlgebra hA) Q P hP

/-- Any actual finite decomposition into Euler eigenoperators of finite
differential order is recovered by polynomials of ad J. Individual
components need not be assumed to belong to the Lie algebra. -/
theorem actual_euler_weight_projection (E : LieSubalgebra ℝ Operator)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (s : Finset ℤ) (v : ℤ → Operator)
    (heigen : ∀ w ∈ s, ⁅hiddenEuler, v w⁆ = (w : ℝ) • v w)
    (hfinite : ∀ w ∈ s, v w ∈ finiteOrderAlgebra)
    (hmem : (∑ w ∈ s, v w) ∈ E)
    (i : ℤ) (hi : i ∈ s) :
    ∃ Q : Polynomial ℝ,
      (aeval (LieAlgebra.ad ℝ Operator (hiddenEuler + multiplication B)) Q)
        (∑ w ∈ s, v w) = v i ∧ v i ∈ E := by
  classical
  let D := LieAlgebra.ad ℝ Operator hiddenEuler
  let N := commuteWithMultiplier B
  let T := LieAlgebra.ad ℝ Operator (hiddenEuler + multiplication B)
  have hDN : Commute D N := by
    dsimp [D, N]
    rw [right_multiplier_eq_neg_ad]
    exact (LieAlgebra.commute_ad_of_commute (hiddenEuler_commute_multiplier B hB)).neg_right
  have hT : T = D - N := by
    apply LinearMap.ext
    intro P
    change ⁅hiddenEuler + multiplication B, P⁆ = ⁅hiddenEuler, P⁆ - ⁅P, multiplication B⁆
    rw [add_lie, ← lie_skew P (multiplication B)]
    abel
  let k : ℤ → ℕ := fun w => if hw : w ∈ s then Classical.choose (hfinite w hw) else 0
  have hk (w : ℤ) (hw : w ∈ s) : v w ∈ orderSpace (k w) := by
    simpa only [k, dite_eq_left hw] using Classical.choose_spec (hfinite w hw)
  let r := s.sup k + 1
  have hnil (w : ℤ) (hw : w ∈ s) : (N ^ r) (v w) = 0 := by
    have ho : v w ∈ orderSpace (s.sup k) := orderSpace_monotone (Finset.le_sup hw) (hk w hw)
    simpa only [N, r, Module.End.pow_apply] using iterate_commuteWithMultiplier_eq_zero ho B
  have hann (w : ℤ) (hw : w ∈ s) :
      ((T - algebraMap ℝ (Module.End ℝ Operator) (w : ℝ)) ^ r) (v w) = 0 := by
    let A := D - algebraMap ℝ (Module.End ℝ Operator) (w : ℝ)
    have hA : A (v w) = 0 := by
      simpa only [A, D, LieAlgebra.ad_apply, LinearMap.sub_apply,
        Module.algebraMap_end_apply, sub_eq_zero] using heigen w hw
    have hAN : Commute A (-N) := (hDN.sub_left (Algebra.commutes _ _)).neg_right
    have heq : T - algebraMap ℝ (Module.End ℝ Operator) (w : ℝ) = A + -N := by
      rw [hT]
      dsimp [A]
      abel
    rw [heq, Wong.EulerAlgebra.add_pow_apply_eq_of_annihilate A (-N) hAN (v w) hA]
    rw [neg_pow, Module.End.mul_apply, hnil w hw, map_zero]
  obtain ⟨Q, hQ⟩ := Wong.EulerAlgebra.generalized_weight_projection s i hi
    (fun w : ℤ => (w : ℝ)) (fun _ _ _ _ he => Int.cast_injective he) r T v hann
  refine ⟨Q, hQ, ?_⟩
  rw [← hQ]
  exact Wong.EulerAlgebra.aeval_mem_of_invariant (E).toSubmodule T
    (fun A hA => (E).lie_mem hJ hA) Q _ hmem

/-- The full actual finite Euler decomposition: every estimation-algebra
element splits into finitely many true integer Euler eigenoperators; each
component is an actual polynomial in ad J applied to the original element
and therefore belongs to the same estimation algebra. -/
theorem finiteOrderLieAlgebra_finite_euler_decomposition
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (hnormal : E ≤ normalFormOperators)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (P : Operator) (hP : P ∈ E) :
    ∃ s : Finset ℤ, ∃ v : ℤ → Operator,
      (∑ w ∈ s, v w) = P ∧
      ∀ w ∈ s, ⁅hiddenEuler, v w⁆ = (w : ℝ) • v w ∧
        ∃ Q : Polynomial ℝ,
          (aeval (LieAlgebra.ad ℝ Operator (hiddenEuler + multiplication B)) Q) P = v w ∧
          v w ∈ E := by
  obtain ⟨p, hp⟩ := hnormal hP
  obtain ⟨n, hn⟩ := finiteOrderLieAlgebra_uniform_hidden_nilpotence E hfinite B hB hJ
  have hnp : ∀ α, (partialDerivative 2 ^ n) (p α) = 0 := hn p (by simpa only [hp] using hP)
  obtain ⟨s, hs⟩ := normalEuler_integer_annihilator p n hnp
  rw [hp] at hs
  obtain ⟨q, hsum, heigen⟩ := Wong.EulerSpectral.integer_spectral_decomposition
    (LieAlgebra.ad ℝ Operator hiddenEuler) s P hs
  let v : ℤ → Operator := fun w => (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) (q w)) P
  have hvfinite (w : ℤ) (_hw : w ∈ s) : v w ∈ finiteOrderAlgebra :=
    hiddenEuler_polynomial_mem_finiteOrderAlgebra (q w) P (hfinite hP)
  have hvmem : (∑ w ∈ s, v w) ∈ E := by simpa only [v, hsum] using hP
  refine ⟨s, v, hsum, ?_⟩
  intro w hw
  refine ⟨heigen w hw, ?_⟩
  obtain ⟨Q, hQ, hQE⟩ := actual_euler_weight_projection E B hB hJ s v
    heigen hvfinite hvmem w hw
  exact ⟨Q, by simpa only [v, hsum] using hQ, hQE⟩

/-- Specialization to the original estimation algebra, with all normal-form
and finite-order premises discharged from its actual defining generators. -/
theorem estimationAlgebra_finite_euler_decomposition {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ estimationAlgebra f h)
    (P : Operator) (hP : P ∈ estimationAlgebra f h) :
    ∃ s : Finset ℤ, ∃ v : ℤ → Operator,
      (∑ w ∈ s, v w) = P ∧
      ∀ w ∈ s, ⁅hiddenEuler, v w⁆ = (w : ℝ) • v w ∧
        ∃ Q : Polynomial ℝ,
          (aeval (LieAlgebra.ad ℝ Operator (hiddenEuler + multiplication B)) Q) P = v w ∧
          v w ∈ estimationAlgebra f h :=
  finiteOrderLieAlgebra_finite_euler_decomposition (estimationAlgebra f h)
    (estimationAlgebra_le_finiteOrder f h) (estimationAlgebra_le_normalFormOperators f h)
    B hB hJ P hP

end Wong.SmoothModel
