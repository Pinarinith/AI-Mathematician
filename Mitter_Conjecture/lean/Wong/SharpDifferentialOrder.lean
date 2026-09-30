import Wong.DirectionalExtraction

/-!
# Sharp order bounds on the real smooth operator model

Order zero is proved to consist exactly of multiplication operators, and
Jacobi then gives the sharp commutator bound. No representation theorem for
higher-order operators is assumed.
-/

noncomputable section
namespace Wong.SmoothModel

/-- An operator commuting with all smooth multipliers is multiplication by
    its value on the constant-one test function. -/
theorem orderSpace_zero_representation {A : Operator} (hA : A ∈ orderSpace 0) :
    A = multiplication (A smoothOne) := by
  apply LinearMap.ext
  intro u
  have hcomm := mem_orderSpace_zero.mp hA u
  change A * multiplication u - multiplication u * A = 0 at hcomm
  have hprod := sub_eq_zero.mp hcomm
  have hpoint := congrArg (fun B : Operator => B smoothOne) hprod
  change A (multiplication u smoothOne) = multiplication u (A smoothOne) at hpoint
  rw [multiplication_apply, smoothMul_one] at hpoint
  exact hpoint.trans (smoothMul_comm u (A smoothOne))

/-- The recursive order-zero definition has precisely its intended meaning. -/
theorem mem_orderSpace_zero_iff {A : Operator} :
    A ∈ orderSpace 0 ↔ ∃ u : Smooth, A = multiplication u := by
  constructor
  · intro hA
    exact ⟨A smoothOne, orderSpace_zero_representation hA⟩
  · rintro ⟨u, rfl⟩
    exact multiplication_mem_orderSpace_zero u

/-- The sharp commutator bound for actual endomorphisms of smooth functions.
    The natural-number subtraction also covers two order-zero operators. -/
theorem lie_mem_orderSpace_sharp {m n : ℕ} {A B : Operator}
    (hA : A ∈ orderSpace m) (hB : B ∈ orderSpace n) :
    ⁅A, B⁆ ∈ orderSpace (m + n - 1) := by
  induction m generalizing n A B with
  | zero =>
    obtain ⟨u, rfl⟩ := mem_orderSpace_zero_iff.mp hA
    rw [← lie_skew]
    change -commuteWithMultiplier u B ∈ orderSpace (0 + n - 1)
    cases n with
    | zero =>
      rw [mem_orderSpace_zero.mp hB u, neg_zero]
      exact (orderSpace 0).zero_mem
    | succ n =>
      simpa only [Nat.zero_add, Nat.add_sub_cancel] using
        (orderSpace n).neg_mem (mem_orderSpace_succ.mp hB u)
  | succ m ihM =>
    induction n generalizing B with
    | zero =>
      obtain ⟨u, rfl⟩ := mem_orderSpace_zero_iff.mp hB
      exact mem_orderSpace_succ.mp hA u
    | succ n ihN =>
      have hindex : m + 1 + (n + 1) - 1 = (m + n) + 1 := by omega
      rw [hindex, mem_orderSpace_succ]
      intro u
      rw [commuteWithMultiplier_lie]
      apply (orderSpace (m + n)).add_mem
      · have h := ihN (mem_orderSpace_succ.mp hB u)
        simpa only [show m + 1 + n - 1 = m + n by omega] using h
      · have h := ihM (mem_orderSpace_succ.mp hA u) hB
        simpa only [show m + (n + 1) - 1 = m + n by omega] using h

/-- Bracketing with the filtering generator raises order by at most one. -/
theorem lie_L0_mem_orderSpace {m n : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    {A : Operator} (hA : A ∈ orderSpace n) :
    ⁅L0 f h, A⁆ ∈ orderSpace (n + 1) := by
  have hbound := lie_mem_orderSpace_sharp (L0_mem_orderSpace_two f h) hA
  simpa only [show 2 + n - 1 = n + 1 by omega] using hbound

/-- The iterated generator bracket of a function multiplier has order at
    most the number of brackets, in addition to the finite-dimensional bound. -/
theorem ad_L0_pow_multiplication_mem_orderSpace {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (u : Smooth) (n : ℕ) :
    ((LieAlgebra.ad ℝ Operator (L0 f h)) ^ n) (multiplication u) ∈ orderSpace n := by
  induction n with
  | zero => exact multiplication_mem_orderSpace_zero u
  | succ n ih =>
    rw [Wong.AdjointIteration.end_pow_succ_apply, LieAlgebra.ad_apply]
    exact lie_L0_mem_orderSpace f h ih

end Wong.SmoothModel
