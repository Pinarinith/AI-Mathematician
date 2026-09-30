import Wong.SharpDifferentialOrder
import Mathlib.Tactic.Linarith

/-!
# The pure-direction obstruction on actual smooth operators

The proof uses iterated genuine multiplier commutators. Thus it does not
assume a principal-symbol map or an unproved Poisson quotient identity.
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace Wong.SmoothModel
open Wong.AdjointIteration

/-- The exact second-degree Leibniz formula when the second argument has
vanishing third multiplier commutator. -/
theorem multiplier_power_lie_quadratic (u : Smooth) (P C : Operator)
    (hC : (commuteWithMultiplier u ^ 3) C = 0) (n : ℕ) :
    (commuteWithMultiplier u ^ (n + 2)) ⁅P, C⁆ =
      ⁅(commuteWithMultiplier u ^ (n + 2)) P, C⁆ +
      (n + 2 : ℝ) • ⁅(commuteWithMultiplier u ^ (n + 1)) P,
        commuteWithMultiplier u C⁆ +
      (((n + 2 : ℝ) * (n + 1 : ℝ)) / 2) •
        ⁅(commuteWithMultiplier u ^ n) P, (commuteWithMultiplier u ^ 2) C⁆ := by
  let δ := commuteWithMultiplier u
  change (δ ^ (n + 2)) ⁅P, C⁆ =
    ⁅(δ ^ (n + 2)) P, C⁆ + (n + 2 : ℝ) • ⁅(δ ^ (n + 1)) P, δ C⁆ +
      (((n + 2 : ℝ) * (n + 1 : ℝ)) / 2) • ⁅(δ ^ n) P, (δ ^ 2) C⁆
  have hd (A B : Operator) : δ ⁅A, B⁆ = ⁅A, δ B⁆ + ⁅δ A, B⁆ :=
    commuteWithMultiplier_lie u A B
  have hc : δ ((δ ^ 2) C) = 0 := hC
  have htwo (Q : Operator) : δ (δ Q) = (δ ^ 2) Q := rfl
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add, pow_zero, Module.End.one_apply]
    rw [show (δ ^ 2) ⁅P, C⁆ = δ (δ ⁅P, C⁆) from rfl,
      hd P C, map_add, hd P (δ C), hd (δ P) C]
    rw [htwo C, htwo P]
    norm_num
    module
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, end_pow_succ_apply, ih]
    simp only [map_add, map_smul, hd, hc, lie_zero, zero_add, htwo C]
    simp only [← end_pow_succ_apply, Nat.cast_add, Nat.cast_one]
    module

/-- Lie words used to force arbitrarily high order from a nonzero pure slope. -/
def pureHeadWords (L C : Operator) : ℕ → Operator
  | 0 => ⁅L, C⁆
  | n + 1 => ⁅pureHeadWords L C n, C⁆

def pureHeadFactor (a : ℝ) : ℕ → ℝ
  | 0 => 6 * a
  | n + 1 => (n + 4 : ℝ) * (n + 3 : ℝ) * a * pureHeadFactor a n

theorem pureHeadFactor_ne_zero (a : ℝ) (ha : a ≠ 0) (n : ℕ) :
    pureHeadFactor a n ≠ 0 := by
  induction n with
  | zero => exact mul_ne_zero (by norm_num) ha
  | succ n ih =>
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) ha) ih

theorem pureHeadWords_mem_orderSpace (L C : Operator)
    (hL : L ∈ orderSpace 2) (hC : C ∈ orderSpace 2) (n : ℕ) :
    pureHeadWords L C n ∈ orderSpace (n + 3) := by
  induction n with
  | zero => exact lie_mem_orderSpace_sharp hL hC
  | succ n ih =>
    simpa only [pureHeadWords, show n + 3 + 2 - 1 = n + 1 + 3 by omega] using
      lie_mem_orderSpace_sharp ih hC

/-- The factorial coefficient is extracted directly from the Lie words. -/
theorem pureHeadWords_extraction (u : Smooth) (L C : Operator) (a c : ℝ)
    (hL : L ∈ orderSpace 2) (hC : C ∈ orderSpace 2)
    (hLL : (commuteWithMultiplier u ^ 2) L = 1)
    (hCC : (commuteWithMultiplier u ^ 2) C =
      (2 * a) • multiplication u + c • (1 : Operator)) (n : ℕ) :
    (commuteWithMultiplier u ^ (n + 3)) (pureHeadWords L C n) =
      pureHeadFactor a n • (1 : Operator) := by
  let δ := commuteWithMultiplier u
  have hzC : (δ ^ 3) C = 0 := by
    simpa only [Module.End.pow_apply] using iterate_commuteWithMultiplier_eq_zero hC u
  have hzL : (δ ^ 3) L = 0 := by
    simpa only [Module.End.pow_apply] using iterate_commuteWithMultiplier_eq_zero hL u
  have hbr (P : Operator) : ⁅P, (δ ^ 2) C⁆ = (2 * a) • δ P := by
    rw [hCC, lie_add, lie_smul, lie_scalar_identity, add_zero]
    rfl
  have hone (P : Operator) : ⁅(1 : Operator), P⁆ = 0 := by
    simpa only [one_smul] using scalar_identity_lie (1 : ℝ) P
  induction n with
  | zero =>
    change (δ ^ 3) ⁅L, C⁆ = (6 * a) • (1 : Operator)
    rw [show 3 = 1 + 2 from rfl,
      multiplier_power_lie_quadratic u L C hzC 1, hzL, hLL]
    simp only [zero_lie, zero_add, hone, smul_zero]
    rw [hbr]
    change _ • ((2 * a) • ((δ ^ 2) L)) = _
    rw [hLL]
    norm_num
    module
  | succ n ih =>
    have hord := pureHeadWords_mem_orderSpace L C hL hC n
    have hzP : (δ ^ (n + 4)) (pureHeadWords L C n) = 0 := by
      simpa only [Module.End.pow_apply, Nat.add_assoc] using
        iterate_commuteWithMultiplier_eq_zero hord u
    change (δ ^ (n + 1 + 3)) ⁅pureHeadWords L C n, C⁆ = _
    rw [show n + 1 + 3 = (n + 2) + 2 by omega,
      multiplier_power_lie_quadratic u _ C hzC (n + 2)]
    rw [show n + 2 + 2 = n + 4 by omega, hzP,
      show n + 2 + 1 = n + 3 by omega, ih]
    simp only [zero_lie, zero_add, scalar_identity_lie, smul_zero, zero_add]
    rw [hbr, ← end_pow_succ_apply,
      show n + 2 + 1 = n + 3 by omega, ih]
    simp only [pureHeadFactor, smul_smul, Nat.cast_add, Nat.cast_ofNat]
    congr 1
    ring

/-- In a finite-dimensional algebra of actual finite-order operators, a
second-order pure coefficient cannot have a nonzero slope in that direction. -/
theorem pure_head_slope_zero {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] (i : Fin 3)
    (C : Operator) (hCE : C ∈ estimationAlgebra f h) (hC : C ∈ orderSpace 2)
    (a c : ℝ)
    (hCC : (commuteWithMultiplier (linearFunction (coordinateVector i)) ^ 2) C =
      (2 * a) • multiplication (linearFunction (coordinateVector i)) +
        c • (1 : Operator)) : a = 0 := by
  by_contra ha
  let u := linearFunction (coordinateVector i)
  let δ := commuteWithMultiplier u
  have hLL : (δ ^ 2) (L0 f h) = 1 := by
    change ⁅⁅L0 f h, multiplication u⁆, multiplication u⁆ = 1
    rw [lie_L0_linearFunction, lie_directionD_linearFunction]
    simp [coordinateVector, Pi.single_apply]
  obtain ⟨N, hN⟩ := estimationAlgebra_uniform_order_bound f h
  have hPE (n : ℕ) : pureHeadWords (L0 f h) C n ∈ estimationAlgebra f h := by
    induction n with
    | zero =>
      exact (estimationAlgebra f h).lie_mem
        (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hCE
    | succ n ih => exact (estimationAlgebra f h).lie_mem ih hCE
  have hPN : pureHeadWords (L0 f h) C N ∈ orderSpace (N + 2) :=
    orderSpace_monotone (by omega) (hN (hPE N))
  have hz : (δ ^ (N + 3)) (pureHeadWords (L0 f h) C N) = 0 := by
    simpa only [Module.End.pow_apply, Nat.add_assoc] using
      iterate_commuteWithMultiplier_eq_zero hPN u
  have hex := pureHeadWords_extraction u (L0 f h) C a c
    (L0_mem_orderSpace_two f h) hC hLL hCC N
  rw [hz] at hex
  have heval := congrArg (fun A : Operator => (A smoothOne).1 (0 : State)) hex
  have hc0 : pureHeadFactor a N = 0 := by simpa [smoothOne] using heval.symm
  exact pureHeadFactor_ne_zero a ha N hc0

end Wong.SmoothModel
