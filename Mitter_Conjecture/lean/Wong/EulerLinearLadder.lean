import Wong.EulerHeadExtraction
import Wong.NormalSymbolsOrderBridge

/-!
# A genuine order-doubling Lie ladder

The ladder is formulated for actual smooth operators. Its hypotheses are
explicit first commutator identities, which the canonical visible-linear
Euler generator discharges in the companion calculation file.
-/
noncomputable section
namespace Wong.SmoothModel
set_option maxHeartbeats 1200000

theorem actual_lie_zero_of_commute (A B : Operator) (h : Commute A B) : ⁅A, B⁆ = 0 := by
  rw [operator_lie_def, h.eq, sub_self]

theorem actual_commute_scalar_identity (A : Operator) (c : ℝ) : Commute A (c • 1) := by
  apply sub_eq_zero.mp
  exact lie_scalar_identity A c

/-- The coefficient multiplying a derivative may be an operator, provided
it commutes with that derivative; this gives the exact power formula. -/
theorem lie_power_commuting_coefficient (L D R : Operator) (hRD : Commute R D)
    (hLD : ⁅L, D⁆ = R * D) (n : ℕ) :
    ⁅L, D ^ n⁆ = (n : ℝ) • (R * D ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_smul, one_smul] using lie_scalar_identity L 1
  | succ n ih =>
    rw [pow_succ', euler_lie_mul, hLD, ih, mul_smul_comm]
    have hmove : D * (R * D ^ n) = R * (D * D ^ n) := by
      rw [← mul_assoc, hRD.symm.eq, mul_assoc]
    rw [hmove, mul_assoc]
    simp only [Nat.cast_add, Nat.cast_one]
    module

/-- Exact algebraic commutator behind the doubling step, on actual operators. -/
theorem actual_double_lie_product (L G A B R : Operator) (μ : ℝ)
    (hLA : ⁅L, A⁆ = R * A) (hLG : ⁅L, G⁆ = B)
    (hGA : Commute G A) (hAB : Commute A B)
    (hGR : Commute G R) (hAR : Commute A R)
    (hGB : ⁅G, B⁆ = -μ • 1) :
    ⁅G * A, ⁅L, G * A⁆⁆ = -μ • (A * A) := by
  have hAZ : ⁅A, B * A⁆ = 0 :=
    actual_lie_zero_of_commute A (B * A) (hAB.mul_right (Commute.refl A))
  have hGZ : ⁅G, A⁆ = 0 := actual_lie_zero_of_commute G A hGA
  have hterm : ⁅G * A, G * (R * A)⁆ = 0 := by
    apply actual_lie_zero_of_commute
    exact ((Commute.refl G).mul_left hGA.symm).mul_right
      ((hGR.mul_left hAR).mul_right (hGA.mul_left (Commute.refl A)))
  rw [euler_lie_mul L G A, hLG, hLA, lie_add, hterm, add_zero,
    operator_lie_mul_left G A (B * A), hAZ, mul_zero, zero_add,
    euler_lie_mul G B A, hGB, hGZ, mul_zero, add_zero]
  simp only [smul_mul_assoc, one_mul]

/-- Genuine pure powers have unbounded actual differential order. -/
theorem partialDerivative_pow_not_mem_lower_order (n k : ℕ) (hkn : k < n) :
    partialDerivative 2 ^ n ∉ orderSpace k := by
  intro hp
  have hact : normalAction (normalHiddenHead n 1) ∈ orderSpace k := by
    simpa only [normalAction_hiddenHead, one_smul] using hp
  have hdeg := normalDegreeLE_of_action_order (normalHiddenHead n 1) k hact
  have hz := hdeg (Finsupp.single 2 n) (by simpa only [Finsupp.degree_single] using hkn)
  have hone : (smoothOne : Smooth) = 0 := by
    simpa only [normalHiddenHead, Finsupp.single_eq_same, one_smul] using hz
  have he := congrArg (fun u : Smooth => u.1 (0 : State)) hone
  norm_num [smoothOne] at he

/-- First commutators of the canonical visible-linear Euler block force an
actual unbounded-order ladder unless its visible slope norm μ vanishes. -/
theorem actual_linear_euler_ladder_obstruction
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (L G B : Operator) (c μ : ℝ)
    (hLE : L ∈ E) (hPE : partialDerivative 2 ^ 2 ∈ E)
    (hLD : ⁅L, partialDerivative 2⁆ = (G + c • 1) * partialDerivative 2)
    (hLG : ⁅L, G⁆ = B) (hGD : Commute G (partialDerivative 2))
    (hBD : Commute B (partialDerivative 2)) (hGB : ⁅G, B⁆ = -μ • 1) : μ = 0 := by
  by_contra hμ
  let D := partialDerivative 2
  let R₀ := G + c • (1 : Operator)
  have hR₀D : Commute R₀ D := hGD.add_left (actual_commute_scalar_identity D c).symm
  have hR₀G : Commute G R₀ := (Commute.refl G).add_right (actual_commute_scalar_identity G c)
  have hpow (m : ℕ) : ⁅L, D ^ m⁆ = (m : ℝ) • (R₀ * D ^ m) :=
    lie_power_commuting_coefficient L D R₀ hR₀D hLD m
  have hstep (m : ℕ) (hm : 0 < m) (hmE : D ^ m ∈ E) : D ^ (2 * m) ∈ E := by
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hm
    have hiso : ⁅L, D ^ m⁆ - ((m : ℝ) * c) • D ^ m = (m : ℝ) • (G * D ^ m) := by
      rw [hpow]
      dsimp [R₀]
      simp only [add_mul, smul_mul_assoc, one_mul, smul_add, smul_smul]
      module
    have hX : G * D ^ m ∈ E := by
      have he := E.sub_mem (E.lie_mem hLE hmE) (E.smul_mem ((m : ℝ) * c) hmE)
      rw [hiso] at he
      have hs := E.smul_mem (m : ℝ)⁻¹ he
      simpa only [smul_smul, inv_mul_cancel₀ hmreal, one_smul] using hs
    have hLA : ⁅L, D ^ m⁆ = ((m : ℝ) • R₀) * D ^ m := by
      rw [hpow, smul_mul_assoc]
    have hd := actual_double_lie_product L G (D ^ m) B ((m : ℝ) • R₀) μ
      hLA hLG (hGD.pow_right m) (hBD.pow_right m).symm
      (hR₀G.smul_right (m : ℝ)) ((hR₀D.pow_right m).symm.smul_right (m : ℝ)) hGB
    have hdouble : ⁅G * D ^ m, ⁅L, G * D ^ m⁆⁆ = -μ • D ^ (2 * m) := by
      simpa only [← pow_add, two_mul] using hd
    have he := E.lie_mem hX (E.lie_mem hLE hX)
    rw [hdouble] at he
    have hs := E.smul_mem (-μ)⁻¹ he
    simpa only [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hμ), one_smul] using hs
  have hseq (n : ℕ) : D ^ (2 ^ (n + 1)) ∈ E := by
    induction n with
    | zero => simpa only [zero_add, pow_one] using hPE
    | succ n ih =>
      simpa only [pow_succ' 2 (n + 1)] using hstep (2 ^ (n + 1)) (by positivity) ih
  obtain ⟨N, hN⟩ := finiteDimensional_uniform_order_bound E.toSubmodule (fun P hP => hfinite hP)
  exact partialDerivative_pow_not_mem_lower_order (2 ^ (N + 1)) N
    (lt_trans (Nat.lt_succ_self N) (Nat.lt_two_pow_self)) (hN (hseq N))

end Wong.SmoothModel
