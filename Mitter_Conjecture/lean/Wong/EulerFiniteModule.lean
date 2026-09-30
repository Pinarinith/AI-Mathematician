import Wong.NormalFormAlgebra
import Wong.EulerAlgebra
import Wong.EulerSmooth
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Lie.AdjointAction.Basic

/-!
# Actual finite modules for a hidden Euler adjoint

A multiplier commutator need not preserve the original estimation algebra.
We enlarge a finite-dimensional invariant space by finitely many images of
that nilpotent commutator; the pure Euler adjoint then preserves the enlarged
finite-dimensional space. Cayley--Hamilton applies there without an extra
invariance assumption on the multiplier part.
-/

noncomputable section
namespace Wong.EulerFiniteModule

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem aeval_restrict_apply (D : Module.End ℝ V) (U : Submodule ℝ V)
    (hD : ∀ u ∈ U, D u ∈ U) (p : Polynomial ℝ) (u : U) :
    ((Polynomial.aeval (D.restrict hD) p) u : V) = (Polynomial.aeval D p) (u : V) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul]
    rw [Module.End.pow_restrict n hD, LinearMap.coe_restrict_apply]

theorem invariant_common_annihilator (D : Module.End ℝ V) (U : Submodule ℝ V)
    [FiniteDimensional ℝ U] (hD : ∀ u ∈ U, D u ∈ U) :
    ∃ Q : Polynomial ℝ, Q ≠ 0 ∧ ∀ u ∈ U, (Polynomial.aeval D Q) u = 0 := by
  let d : Module.End ℝ U := D.restrict hD
  refine ⟨d.charpoly, (LinearMap.charpoly_monic d).ne_zero, ?_⟩
  intro u hu
  have h := congrArg (fun A : Module.End ℝ U => (A ⟨u, hu⟩ : V))
    (LinearMap.aeval_self_charpoly d)
  simpa only [d, aeval_restrict_apply, LinearMap.zero_apply, Submodule.coe_zero] using h

/-- A commuting perturbation nilpotent on U gives a genuine finite-dimensional
invariant extension for T+N. No assumption that N preserves U is made. -/
theorem common_annihilator_of_commuting_nilpotent
    (T N : Module.End ℝ V) (hTN : Commute T N) (U : Submodule ℝ V)
    [FiniteDimensional ℝ U] (hT : ∀ u ∈ U, T u ∈ U)
    (r : ℕ) (hr : 0 < r) (hN : ∀ u ∈ U, (N ^ r) u = 0) :
    ∃ Q : Polynomial ℝ, Q ≠ 0 ∧ ∀ u ∈ U, (Polynomial.aeval (T + N) Q) u = 0 := by
  let W : Submodule ℝ V := ⨆ j : Fin r, U.map (N ^ j.val)
  have hU : U ≤ W := by
    intro u hu
    apply le_iSup (fun j : Fin r => U.map (N ^ j.val)) ⟨0, hr⟩
    exact ⟨u, hu, by simp⟩
  have hTW : W ≤ W.comap T := by
    apply iSup_le
    intro j
    rintro _ ⟨u, hu, rfl⟩
    change T ((N ^ j.val) u) ∈ W
    rw [← Module.End.mul_apply, (hTN.pow_right j.val).eq, Module.End.mul_apply]
    apply le_iSup (fun j : Fin r => U.map (N ^ j.val)) j
    exact ⟨T u, hT u hu, rfl⟩
  have hNW : W ≤ W.comap N := by
    apply iSup_le
    intro j
    rintro _ ⟨u, hu, rfl⟩
    change N ((N ^ j.val) u) ∈ W
    rw [← Module.End.mul_apply, ← pow_succ']
    by_cases hj : j.val + 1 < r
    · apply le_iSup (fun j : Fin r => U.map (N ^ j.val)) ⟨j.val + 1, hj⟩
      exact ⟨u, hu, rfl⟩
    · have heq : j.val + 1 = r := by omega
      rw [heq, hN u hu]
      exact W.zero_mem
  have hsum : ∀ u ∈ W, (T + N) u ∈ W := by
    intro u hu
    exact W.add_mem (hTW hu) (hNW hu)
  let : FiniteDimensional ℝ W := by dsimp [W]; infer_instance
  obtain ⟨Q, hQ, hQU⟩ := invariant_common_annihilator (T + N) W hsum
  exact ⟨Q, hQ, fun u hu => hQU u (hU hu)⟩

end Wong.EulerFiniteModule

namespace Wong.SmoothModel

/-- The genuine hidden Euler vector field x3 ∂3. -/
def hiddenEuler : Operator := multiplication (linearFunction (coordinateVector 2)) * partialDerivative 2

theorem hiddenEuler_commute_multiplier (B : Smooth) (hB : partialDerivative 2 B = 0) :
    Commute hiddenEuler (multiplication B) := by
  apply sub_eq_zero.mp
  change ⁅hiddenEuler, multiplication B⁆ = 0
  rw [hiddenEuler, operator_lie_mul_left, lie_partial_multiplication, hB,
    multiplication_zero, mul_zero, lie_multiplication_multiplication, zero_mul, add_zero]

theorem right_multiplier_eq_neg_ad (B : Smooth) :
    commuteWithMultiplier B = -LieAlgebra.ad ℝ Operator (multiplication B) := by
  apply LinearMap.ext
  intro P
  simp only [commuteWithMultiplier_apply, LinearMap.neg_apply, LieAlgebra.ad_apply]
  exact (lie_skew P (multiplication B)).symm

/-- Finite dimensionality and a real hidden-Euler-plus-visible-potential element
produce an actual polynomial annihilator for the pure Euler adjoint. -/
theorem hiddenEuler_ad_common_annihilator {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ estimationAlgebra f h) :
    ∃ Q : Polynomial ℝ, Q ≠ 0 ∧ ∀ P ∈ estimationAlgebra f h,
      (Polynomial.aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) P = 0 := by
  let T := LieAlgebra.ad ℝ Operator (hiddenEuler + multiplication B)
  let N := commuteWithMultiplier B
  have hTN : Commute T N := by
    dsimp [T, N]
    rw [right_multiplier_eq_neg_ad]
    exact (LieAlgebra.commute_ad_of_commute
      ((hiddenEuler_commute_multiplier B hB).add_left (Commute.refl _))).neg_right
  have hT : ∀ P ∈ (estimationAlgebra f h).toSubmodule, T P ∈ (estimationAlgebra f h).toSubmodule := by
    intro P hP
    exact (estimationAlgebra f h).lie_mem hJ hP
  obtain ⟨n, hn⟩ := estimationAlgebra_uniform_order_bound f h
  have hN : ∀ P ∈ (estimationAlgebra f h).toSubmodule, (N ^ (n + 1)) P = 0 := by
    intro P hP
    simpa only [N, Module.End.pow_apply] using iterate_commuteWithMultiplier_eq_zero (hn hP) B
  have heq : T + N = LieAlgebra.ad ℝ Operator hiddenEuler := by
    apply LinearMap.ext
    intro P
    change ⁅hiddenEuler + multiplication B, P⁆ + ⁅P, multiplication B⁆ = ⁅hiddenEuler, P⁆
    rw [add_lie, ← lie_skew P (multiplication B)]
    abel
  obtain ⟨Q, hQ, hQP⟩ := Wong.EulerFiniteModule.common_annihilator_of_commuting_nilpotent
    T N hTN (estimationAlgebra f h).toSubmodule hT (n + 1) (Nat.succ_pos n) hN
  exact ⟨Q, hQ, fun P hP => by simpa only [heq] using hQP P hP⟩

end Wong.SmoothModel
