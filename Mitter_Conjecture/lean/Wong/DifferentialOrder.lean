import Wong.SmoothBrackets
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Genuine finite differential order of the smooth estimation algebra

The filtration is defined on the actual endomorphisms of globally smooth
functions, using successive commutators with all smooth multiplication
operators. Closure and order bounds are proved, rather than included as
fields of an assumed interface.
-/

noncomputable section
namespace Wong.SmoothModel

/-- Commutation on the right with multiplication by a smooth function. -/
def commuteWithMultiplier (u : Smooth) : Operator →ₗ[ℝ] Operator :=
  LinearMap.mulRight ℝ (multiplication u) - LinearMap.mulLeft ℝ (multiplication u)

@[simp] theorem commuteWithMultiplier_apply (u : Smooth) (A : Operator) :
    commuteWithMultiplier u A = ⁅A, multiplication u⁆ := rfl

/-- Grothendieck order at most `n`. The order-zero operators commute with
    every smooth multiplier; each further commutator lowers the index. -/
def orderSpace : ℕ → Submodule ℝ Operator
  | 0 => ⨅ u : Smooth, (commuteWithMultiplier u).ker
  | n + 1 => ⨅ u : Smooth, (orderSpace n).comap (commuteWithMultiplier u)

@[simp] theorem mem_orderSpace_zero {A : Operator} :
    A ∈ orderSpace 0 ↔ ∀ u : Smooth, commuteWithMultiplier u A = 0 := by
  simp only [orderSpace, Submodule.mem_iInf, LinearMap.mem_ker]

@[simp] theorem mem_orderSpace_succ {n : ℕ} {A : Operator} :
    A ∈ orderSpace (n + 1) ↔ ∀ u : Smooth, commuteWithMultiplier u A ∈ orderSpace n := by
  simp only [orderSpace, Submodule.mem_iInf, Submodule.mem_comap]

/-- `n + 1` repetitions of any one multiplier commutator annihilate an
    operator of order at most `n`. -/
theorem iterate_commuteWithMultiplier_eq_zero {n : ℕ} {A : Operator}
    (hA : A ∈ orderSpace n) (u : Smooth) :
    (commuteWithMultiplier u)^[n + 1] A = 0 := by
  induction n generalizing A with
  | zero => simpa using mem_orderSpace_zero.mp hA u
  | succ n ih =>
    simpa only [Function.iterate_succ_apply] using
      ih (mem_orderSpace_succ.mp hA u)

/-- The filtration is increasing. -/
theorem orderSpace_le_succ (n : ℕ) : orderSpace n ≤ orderSpace (n + 1) := by
  induction n with
  | zero =>
    intro A hA
    rw [mem_orderSpace_succ]
    intro u
    rw [mem_orderSpace_zero.mp hA u]
    exact (orderSpace 0).zero_mem
  | succ n ih =>
    intro A hA
    rw [mem_orderSpace_succ] at hA ⊢
    intro u
    exact ih (hA u)

theorem orderSpace_monotone : Monotone orderSpace :=
  monotone_nat_of_le_succ orderSpace_le_succ

/-- The commutator product rule for actual operator composition. -/
theorem commuteWithMultiplier_mul (u : Smooth) (A B : Operator) :
    commuteWithMultiplier u (A * B) =
      A * commuteWithMultiplier u B + commuteWithMultiplier u A * B := by
  simpa only [commuteWithMultiplier_apply] using
    operator_lie_mul_left A B (multiplication u)

/-- Composition adds differential-order bounds. -/
theorem mul_mem_orderSpace {m n : ℕ} {A B : Operator}
    (hA : A ∈ orderSpace m) (hB : B ∈ orderSpace n) :
    A * B ∈ orderSpace (m + n) := by
  induction m generalizing n A B with
  | zero =>
    induction n generalizing B with
    | zero =>
      apply mem_orderSpace_zero.mpr
      intro u
      rw [commuteWithMultiplier_mul, mem_orderSpace_zero.mp hA u,
        mem_orderSpace_zero.mp hB u, mul_zero, zero_mul, add_zero]
    | succ n ih =>
      apply mem_orderSpace_succ.mpr
      intro u
      rw [commuteWithMultiplier_mul, mem_orderSpace_zero.mp hA u, zero_mul, add_zero]
      exact ih (mem_orderSpace_succ.mp hB u)
  | succ m ihM =>
    induction n generalizing B with
    | zero =>
      apply mem_orderSpace_succ.mpr
      intro u
      rw [commuteWithMultiplier_mul, mem_orderSpace_zero.mp hB u, mul_zero, zero_add]
      exact ihM (mem_orderSpace_succ.mp hA u) hB
    | succ n ihN =>
      apply mem_orderSpace_succ.mpr
      intro u
      rw [commuteWithMultiplier_mul]
      apply (orderSpace (m + 1 + n)).add_mem
      · exact ihN (mem_orderSpace_succ.mp hB u)
      · simpa only [Nat.add_assoc, Nat.add_comm 1 n] using
          ihM (mem_orderSpace_succ.mp hA u) hB

/-- A sufficient (not claimed sharp) commutator bound. -/
theorem lie_mem_orderSpace {m n : ℕ} {A B : Operator}
    (hA : A ∈ orderSpace m) (hB : B ∈ orderSpace n) :
    ⁅A, B⁆ ∈ orderSpace (m + n) := by
  change A * B - B * A ∈ orderSpace (m + n)
  apply (orderSpace (m + n)).sub_mem (mul_mem_orderSpace hA hB)
  simpa only [Nat.add_comm] using mul_mem_orderSpace hB hA

/-- Every multiplication operator has order at most zero. -/
theorem multiplication_mem_orderSpace_zero (u : Smooth) : multiplication u ∈ orderSpace 0 := by
  apply mem_orderSpace_zero.mpr
  intro v
  simpa only [commuteWithMultiplier_apply] using lie_multiplication_multiplication u v

/-- Every genuine coordinate partial derivative has order at most one. -/
theorem partialDerivative_mem_orderSpace_one (i : Fin 3) :
    partialDerivative i ∈ orderSpace 1 := by
  apply mem_orderSpace_succ.mpr
  intro u
  rw [commuteWithMultiplier_apply, lie_partial_multiplication]
  exact multiplication_mem_orderSpace_zero _

/-- The covariant first-order operators also have order at most one. -/
theorem D_mem_orderSpace_one (f : Fin 3 → Smooth) (i : Fin 3) : D f i ∈ orderSpace 1 := by
  apply (orderSpace 1).sub_mem (partialDerivative_mem_orderSpace_one i)
  exact orderSpace_le_succ 0 (multiplication_mem_orderSpace_zero (f i))

/-- The filtering generator has order at most two. -/
theorem L0_mem_orderSpace_two {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    L0 f h ∈ orderSpace 2 := by
  apply (orderSpace 2).sub_mem
  · apply (orderSpace 2).smul_mem
    apply (orderSpace 2).sum_mem
    intro i _
    exact mul_mem_orderSpace (D_mem_orderSpace_one f i) (D_mem_orderSpace_one f i)
  · apply (orderSpace 2).smul_mem
    exact orderSpace_monotone (by decide : 0 ≤ 2) (multiplication_mem_orderSpace_zero _)

/-- All finite-order operators form an actual Lie subalgebra. -/
def finiteOrderAlgebra : LieSubalgebra ℝ Operator where
  carrier := {A | ∃ n, A ∈ orderSpace n}
  zero_mem' := ⟨0, (orderSpace 0).zero_mem⟩
  add_mem' := by
    rintro A B ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨max m n, (orderSpace (max m n)).add_mem
      (orderSpace_monotone (le_max_left m n) hm)
      (orderSpace_monotone (le_max_right m n) hn)⟩
  smul_mem' := by
    rintro c A ⟨n, hn⟩
    exact ⟨n, (orderSpace n).smul_mem c hn⟩
  lie_mem' := by
    rintro A B ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, lie_mem_orderSpace hm hn⟩

/-- Finite differential order holds for every element of the actual
    estimation algebra, without assuming finite dimensionality. -/
theorem estimationAlgebra_le_finiteOrder {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    estimationAlgebra f h ≤ finiteOrderAlgebra := by
  apply LieSubalgebra.lieSpan_le.mpr
  intro A hA
  rcases hA with hA | hA
  · rcases hA with rfl
    exact ⟨2, L0_mem_orderSpace_two f h⟩
  · obtain ⟨j, rfl⟩ := hA
    exact ⟨0, multiplication_mem_orderSpace_zero (h j)⟩

/-- A finite-dimensional subspace consisting of finite-order operators has
    one common order bound, by taking the maximum over finite generators. -/
theorem finiteDimensional_uniform_order_bound (V : Submodule ℝ Operator)
    [FiniteDimensional ℝ V]
    (hfinite : ∀ A ∈ V, ∃ n, A ∈ orderSpace n) :
    ∃ N, V ≤ orderSpace N := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℝ) (M := V)
  choose n hn using fun v : V => hfinite v.1 v.property
  let N := s.sup n
  refine ⟨N, ?_⟩
  have hspan : Submodule.span ℝ (s : Set V) ≤ (orderSpace N).comap V.subtype := by
    apply Submodule.span_le.mpr
    intro v hv
    exact orderSpace_monotone (Finset.le_sup hv) (hn v)
  rw [hs] at hspan
  intro A hA
  exact hspan (show (⟨A, hA⟩ : V) ∈ (⊤ : Submodule ℝ V) from Submodule.mem_top)

/-- The uniform differential-order bound for the original finite-dimensional
    estimation algebra. All finite-order premises have been discharged. -/
theorem estimationAlgebra_uniform_order_bound {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    ∃ N, (estimationAlgebra f h).toSubmodule ≤ orderSpace N := by
  apply finiteDimensional_uniform_order_bound
  intro A hA
  exact estimationAlgebra_le_finiteOrder f h hA

end Wong.SmoothModel
