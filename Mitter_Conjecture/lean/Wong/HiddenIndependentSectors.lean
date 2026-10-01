import Wong.SectorTwoConclusion
import Wong.SectorIHiddenBridge
import Wong.QuadraticVisibleRigidity
import Wong.FirstOrderNormalBridge


/-! Source segment: HiddenIndependentSectorCalculus.lean -/

/-! Weak function-space versions of the real second-sector argument.
The hypothesis says every actual multiplication element is independent of
hidden coordinate 2. No affine or quadratic-free function-space assumption
is made. Existing differential identities and weighted Lie obstructions are
reused unchanged; all affected membership-to-derivative steps are re-proved.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel

/-- Every actual function element is independent of the hidden coordinate. -/
def HiddenIndependentFunctionSpace (E : LieSubalgebra ℝ Operator) : Prop :=
  ∀ u : Smooth, multiplication u ∈ E → partialDerivative 2 u = 0

theorem hiddenIndependentFunctionSpace_gauge (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E) :
    HiddenIndependentFunctionSpace (gaugeAlgebra Λ E) := by
  intro u hu
  exact hE u ((multiplication_mem_gaugeAlgebra Λ E u).mp hu)

theorem hiddenIndependentFunctionSpace_affine (e : State ≃L[ℝ] State) (b : State)
    (he : e (coordinateVector 2) = coordinateVector 2)
    (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E) :
    HiddenIndependentFunctionSpace (affineAlgebra e b E) := by
  intro u hu
  let v := (affinePullback e b).symm u
  have hv := hE v ((multiplication_mem_affineAlgebra_iff e b E u).mp hu)
  have hd := directionalDerivative_affinePullback e b (coordinateVector 2) v
  rw [he, coordinate_directionalDerivative,
    hv, map_zero] at hd
  simpa only [v, LinearEquiv.apply_symm_apply] using hd

theorem hiddenIndependentFunctionSpace_coordinate (e : State ≃L[ℝ] State)
    (he : e (coordinateVector 2) = coordinateVector 2)
    (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E) :
    HiddenIndependentFunctionSpace (coordinateAlgebra e E) := by
  intro u hu
  let v := (coordinatePullback e).symm u
  have hvE : multiplication v ∈ E := by
    apply (multiplication_pullback_mem_coordinateAlgebra e E v).mp
    simpa only [v, LinearEquiv.apply_symm_apply] using hu
  have hd := directionalDerivative_coordinatePullback e (coordinateVector 2) v
  rw [he, coordinate_directionalDerivative,
    hE v hvE, map_zero] at hd
  simpa only [v, LinearEquiv.apply_symm_apply] using hd

theorem hiddenIndependentFunctionSpace_hiddenFrame (α β δ : ℝ) (Λ : Smooth)
    (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E) :
    HiddenIndependentFunctionSpace (hiddenFrameAlgebra α β δ Λ E) := by
  apply hiddenIndependentFunctionSpace_gauge
  apply hiddenIndependentFunctionSpace_affine _ _ ?_ E hE
  funext i
  fin_cases i <;> simp [hiddenShear, hiddenShearLinear, coordinateVector]

end Wong.SmoothModel

namespace Wong.SmoothModel.SectorTwo.HiddenIndependent

theorem adapted_hidden_partial_zero (E : LieSubalgebra ℝ Operator)
    (hE : HiddenIndependentFunctionSpace E) (a : Smooth) (ha : multiplication a ∈ E) :
    partialDerivative 2 a = 0 := hE a ha

theorem adapted_visible_constant (E : LieSubalgebra ℝ Operator)
    (hE : HiddenIndependentFunctionSpace E) (a : Smooth) (ha : multiplication a ∈ E)
    (h₀ : partialDerivative 0 a = 0) (h₁ : partialDerivative 1 a = 0) :
    ∃ c : ℝ, a = c • smoothOne := by
  have hall : ∀ i, partialDerivative i a = 0 := by
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact hE a ha
  obtain ⟨c, hc⟩ := (smooth_constant_iff_partials_zero a).mpr hall
  refine ⟨c, ?_⟩
  apply Subtype.ext
  funext z
  simpa [smoothOne] using hc z



theorem hessian_mixed_zero (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E)
    (b k h c : ℝ) (V : Smooth)
    (hL : filteringOperator (drift b k h c) V ∈ E)
    (h₀ : D (drift b k h c) 0 ∈ E) (h₁ : D (drift b k h c) 1 ∈ E) :
    partialDerivative 1 (partialDerivative 0 (W V)) = 0 := by
  have hM : multiplication (s01 k h c V) ∈ E := by
    rw [← D1_H0 b k h c V]
    exact E.lie_mem h₁ (H_mem E b k h c V hL 0 h₀)
  have hz := adapted_hidden_partial_zero E hE _ hM
  rw [hidden_s01] at hz
  exact half_smul_eq_zero _ hz


theorem hessian_diagonal_relation (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E)
    (b k h c : ℝ) (V : Smooth)
    (hL : filteringOperator (drift b k h c) V ∈ E)
    (h₀ : D (drift b k h c) 0 ∈ E) (h₁ : D (drift b k h c) 1 ∈ E) :
    h • partialDerivative 0 (partialDerivative 0 (W V)) -
      k • partialDerivative 1 (partialDerivative 1 (W V)) = 0 := by
  have he : h • ⁅D (drift b k h c) 0, H b k h c V 0⁆ -
      k • ⁅D (drift b k h c) 1, H b k h c V 1⁆ =
        multiplication (h • s00 b k V - k • s11 b h c V) := by
    rw [D0_H0, D1_H1]
    simp only [smul_add, smul_smul, multiplication_sub, multiplication_smul]
    module
  have hM : multiplication (h • s00 b k V - k • s11 b h c V) ∈ E := by
    rw [← he]
    exact E.sub_mem (E.smul_mem h (E.lie_mem h₀ (H_mem E b k h c V hL 0 h₀)))
      (E.smul_mem k (E.lie_mem h₁ (H_mem E b k h c V hL 1 h₁)))
  have hz := adapted_hidden_partial_zero E hE _ hM
  simp only [map_sub, map_smul, hidden_s00, hidden_s11] at hz
  apply half_smul_eq_zero
  convert hz using 1 <;> module


theorem third_first_visible_zero (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E)
    (b k h c : ℝ) (V : Smooth)
    (hL : filteringOperator (drift b k h c) V ∈ E)
    (h₀ : D (drift b k h c) 0 ∈ E) :
    partialDerivative 0 (partialDerivative 0 (partialDerivative 0 (W V))) = 0 := by
  have hM : multiplication ((-k) • u k + partialDerivative 0 (s00 b k V)) ∈ E := by
    rw [← D0_D0_H0 b k h c V]
    exact E.lie_mem h₀ (E.lie_mem h₀ (H_mem E b k h c V hL 0 h₀))
  have hz := adapted_hidden_partial_zero E hE _ hM
  simp only [map_add, map_smul, partial_u, show (2 : Fin 3) ≠ 0 by decide,
    ite_false, zero_smul, smul_zero, zero_add] at hz
  rw [partialDerivative_commute_apply 2 0, hidden_s00, map_smul] at hz
  exact half_smul_eq_zero _ hz


theorem q_visible_partials_zero (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E)
    (b k h c : ℝ) (V : Smooth)
    (hL : filteringOperator (drift b k h c) V ∈ E)
    (h₀ : D (drift b k h c) 0 ∈ E) (h₁ : D (drift b k h c) 1 ∈ E) :
    partialDerivative 0 (q k V) = 0 ∧ partialDerivative 1 (q k V) = 0 := by
  have h000 := third_first_visible_zero E hE b k h c V hL h₀
  have h10 := hessian_mixed_zero E hE b k h c V hL h₀ h₁
  constructor
  · simp only [q, map_smul, h000, smul_zero]
  · simp only [q, map_smul]
    rw [partialDerivative_commute_apply 1 0, h10, map_zero, smul_zero, smul_zero]


theorem B_visible_partials (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E)
    (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0)
    (hL : filteringOperator (drift b k h c) V ∈ E)
    (h₀ : D (drift b k h c) 0 ∈ E) (h₁ : D (drift b k h c) 1 ∈ E) :
    partialDerivative 0 (B0 k V) = 0 ∧ partialDerivative 1 (B0 k V) = 0 ∧
    partialDerivative 0 (B1 k h c V) = 0 ∧ partialDerivative 1 (B1 k h c V) = 0 := by
  obtain ⟨hq₀, hq₁⟩ := q_visible_partials_zero E hE b k h c V hL h₀ h₁
  have h10 := hessian_mixed_zero E hE b k h c V hL h₀ h₁
  have hd := hessian_diagonal_relation E hE b k h c V hL h₀ h₁
  have hqk : k • q k V = (1 / 2 : ℝ) • partialDerivative 0 (partialDerivative 0 (W V)) := by
    simp [q, smul_smul, hk]
  have hqh : h • q k V = (1 / 2 : ℝ) • partialDerivative 1 (partialDerivative 1 (W V)) := by
    have he := congrArg (fun z : Smooth => ((1 / 2 : ℝ) * k⁻¹) • z) hd
    simp only [smul_sub, smul_smul, smul_zero] at he
    have hmul : (1 / 2 : ℝ) * k⁻¹ * k = 1 / 2 := by field_simp
    rw [hmul] at he
    apply sub_eq_zero.mp
    convert he using 1 <;> simp only [q, smul_smul] <;> congr 1 <;> ring
  have hone : (smoothOne : Smooth) = 1 := smoothOne_eq_one
  constructor
  · simp [B0, partial_mul, hq₀, hone, smul_mul_assoc, hqk]
  constructor
  · simp [B0, partial_mul, hq₁, h10]
  constructor
  · simp [B1, partial_mul, hq₀, partialDerivative_commute_apply 0 1 (W V), h10]
  · simp [B1, partial_mul, hq₁, hone, smul_mul_assoc, hqh]


theorem B_constants (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E)
    (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0)
    (hL : filteringOperator (drift b k h c) V ∈ E)
    (h₀ : D (drift b k h c) 0 ∈ E) (h₁ : D (drift b k h c) 1 ∈ E) :
    ∃ a₀ a₁ : ℝ, B0 k V = a₀ • smoothOne ∧ B1 k h c V = a₁ • smoothOne := by
  have hT := T_mem E b k h c V hL h₀
  have hm₀ : multiplication (B0 k V) ∈ E := by
    rw [← T_H0 b k h c V hk]
    exact E.lie_mem hT (E.sub_mem (H_mem E b k h c V hL 0 h₀) (E.smul_mem b h₁))
  have hm₁ : multiplication (B1 k h c V) ∈ E := by
    rw [← T_H1 b k h c V hk]
    exact E.lie_mem hT (E.add_mem (H_mem E b k h c V hL 1 h₁) (E.smul_mem b h₀))
  obtain ⟨h00, h10, h01, h11⟩ := B_visible_partials E hE b k h c V hk hL h₀ h₁
  obtain ⟨a₀, ha₀⟩ := adapted_visible_constant E hE _ hm₀ h00 h10
  obtain ⟨a₁, ha₁⟩ := adapted_visible_constant E hE _ hm₁ h01 h11
  exact ⟨a₀, a₁, ha₀, ha₁⟩


theorem potential_profile (E : LieSubalgebra ℝ Operator) (hE : HiddenIndependentFunctionSpace E)
    (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0)
    (hL : filteringOperator (drift b k h c) V ∈ E)
    (h₀ : D (drift b k h c) 0 ∈ E) (h₁ : D (drift b k h c) 1 ∈ E) :
    ∃ (ε e V₀ : Smooth) (a₀ a₁ : ℝ),
      partialDerivative 0 ε = 0 ∧ partialDerivative 1 ε = 0 ∧
      partialDerivative 0 e = 0 ∧ partialDerivative 1 e = 0 ∧
      partialDerivative 2 V₀ = 0 ∧ partialDerivative 2 ε = q k V ∧
      V = V₀ + (2 : ℝ) • (ε * F k h c) + e +
        x 2 * (a₀ • x 0 + a₁ • x 1) := by
  obtain ⟨a₀, a₁, ha₀, ha₁⟩ := B_constants E hE b k h c V hk hL h₀ h₁
  obtain ⟨hq₀, hq₁⟩ := q_visible_partials_zero E hE b k h c V hL h₀ h₁
  let r : Smooth := W V - (2 : ℝ) • (q k V * F k h c) -
    (2 * a₀) • x 0 - (2 * a₁) • x 1
  have hr₀ : partialDerivative 0 r = 0 := by
    have he : partialDerivative 0 r = (2 : ℝ) • (B0 k V - a₀ • smoothOne) := by
      simp only [r, map_sub, map_smul, partial_mul, hq₀, partial_F, partial_x,
        Matrix.cons_val_zero, zero_mul, zero_add, ite_true,
        show (0 : Fin 3) ≠ 1 by decide, ite_false, zero_smul, one_smul,
        smul_zero, sub_zero, B0, mul_comm (q k V) (u k)]
      module
    rw [he, ha₀, sub_self, smul_zero]
  have hr₁ : partialDerivative 1 r = 0 := by
    have he : partialDerivative 1 r = (2 : ℝ) • (B1 k h c V - a₁ • smoothOne) := by
      simp only [r, map_sub, map_smul, partial_mul, hq₁, partial_F, partial_x,
        Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_add, ite_true,
        show (1 : Fin 3) ≠ 0 by decide, ite_false, zero_smul, one_smul,
        smul_zero, sub_zero, B1, mul_comm (q k V) (v h c)]
      module
    rw [he, ha₁, sub_self, smul_zero]
  let ε := hiddenPrimitive (q k V)
  let e := hiddenPrimitive r
  obtain ⟨he₀, he₁⟩ := hiddenPrimitive_visible_partials (q k V) hq₀ hq₁
  obtain ⟨hrp₀, hrp₁⟩ := hiddenPrimitive_visible_partials r hr₀ hr₁
  have he₂ : partialDerivative 2 ε = q k V := partialDerivative_hiddenPrimitive _
  have hrp₂ : partialDerivative 2 e = r := partialDerivative_hiddenPrimitive _
  let V₀ := V - (2 : ℝ) • (ε * F k h c) - e -
    x 2 * ((2 * a₀) • x 0 + (2 * a₁) • x 1)
  have hV₀ : partialDerivative 2 V₀ = 0 := by
    simp only [V₀, map_sub, map_smul, map_add, partial_mul, he₂, hrp₂,
      partial_F, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, mul_zero, add_zero, partial_x,
      ite_true, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, ite_false, zero_smul, one_smul,
      smul_zero, zero_add, smoothOne_eq_one, one_mul, W, r]
    module
  refine ⟨ε, e, V₀, 2 * a₀, 2 * a₁, he₀, he₁, hrp₀, hrp₁, hV₀, he₂, ?_⟩
  dsimp [V₀]
  abel


theorem normalized_tail_nilpotent (E : LieSubalgebra ℝ Operator)
    (hE : HiddenIndependentFunctionSpace E) (b : ℝ) (F ε r U₀ U₁ g₀ : Smooth)
    (hF : partialDerivative 2 F = 0) (hU₀ : partialDerivative 2 U₀ = 0)
    (hU₁ : partialDerivative 2 U₁ = 0) (hg : partialDerivative 2 g₀ = 0)
    (hε₀ : partialDerivative 0 ε = 0) (hε₁ : partialDerivative 1 ε = 0)
    (hL : normalizedGenerator b F ε r U₀ U₁ ∈ E)
    (hT : hiddenTransport g₀ ∈ E) (m : ℕ) (hm : 2 ≤ m)
    (hε : (partialDerivative 2 ^ (m + 1)) ε = 0) :
    (partialDerivative 2 ^ (m + 1)) r = 0 := by
  have htop (i : Fin 3) : partialDerivative i ((partialDerivative 2 ^ m) ε) = 0 := by
    fin_cases i
    · change partialDerivative 0 ((partialDerivative 2 ^ m) ε) = 0
      rw [partial_hidden_power_commute, hε₀, map_zero]
    · change partialDerivative 1 ((partialDerivative 2 ^ m) ε) = 0
      rw [partial_hidden_power_commute, hε₁, map_zero]
    · change partialDerivative 2 ((partialDerivative 2 ^ m) ε) = 0
      simpa only [pow_succ', Module.End.mul_apply] using hε
  obtain ⟨c, hc⟩ := (smooth_constant_iff_partials_zero _).mpr htop
  have hec : (partialDerivative 2 ^ m) ε = c • smoothOne := by
    apply Subtype.ext
    funext z
    simpa [smoothOne] using hc z
  let A := if m = 2 then gradientNorm g₀ else 0
  have hA : partialDerivative 2 A = 0 := by
    dsimp only [A]
    split_ifs
    · exact gradientNorm_hidden_zero g₀ hg
    · exact map_zero _
  have he : (hiddenAd g₀ ^ m) (normalizedGenerator b F ε r U₀ U₁) +
      c • hiddenTransport g₀ =
      multiplication (c • g₀ + A - (1 / 2 : ℝ) • (partialDerivative 2 ^ m) r) := by
    rw [normalizedGenerator_ad_power b F ε r U₀ U₁ g₀ hF hU₀ hU₁ hg m hm,
      hec, hε]
    simp only [hiddenTransport, zero_add, multiplication_sub, multiplication_add,
      multiplication_smul, multiplication_smoothOne, smul_mul_assoc, one_mul,
      smul_add]
    change multiplication A - c • partialDerivative 2 -
      (1 / 2 : ℝ) • multiplication ((partialDerivative 2 ^ m) r) +
      (c • partialDerivative 2 + c • multiplication g₀) = _
    module
  have hM : multiplication (c • g₀ + A - (1 / 2 : ℝ) • (partialDerivative 2 ^ m) r) ∈ E := by
    rw [← he]
    exact E.add_mem (hiddenAd_pow_mem E g₀ hT _ hL m) (E.smul_mem c hT)
  have hz := adapted_hidden_partial_zero E hE _ hM
  simp only [map_sub, map_add, map_smul, hg, hA, smul_zero, zero_add, zero_sub] at hz
  have hh := half_smul_eq_zero _ (neg_eq_zero.mp hz)
  simpa only [pow_succ', Module.End.mul_apply] using hh


theorem actual_scalarTail_nilpotent (E : LieSubalgebra ℝ Operator)
    (hE : HiddenIndependentFunctionSpace E) (b k h c a₀ a₁ : ℝ) (V ε e V₀ : Smooth)
    (hk : k ≠ 0) (hL : filteringOperator (drift b k h c) V ∈ E)
    (h₀ : D (drift b k h c) 0 ∈ E)
    (hε₀ : partialDerivative 0 ε = 0) (hε₁ : partialDerivative 1 ε = 0)
    (he₀ : partialDerivative 0 e = 0) (he₁ : partialDerivative 1 e = 0)
    (hV₀ : partialDerivative 2 V₀ = 0) (hε₂ : partialDerivative 2 ε = q k V)
    (hV : V = V₀ + (2 : ℝ) • (ε * F k h c) + e +
      x 2 * (a₀ • x 0 + a₁ • x 1))
    (m : ℕ) (hm : 2 ≤ m) (hε : (partialDerivative 2 ^ (m + 1)) ε = 0) :
    (partialDerivative 2 ^ (m + 1)) (scalarTail ε e) = 0 := by
  let E' := gaugeAlgebra (hiddenPrimitive ε) E
  have hE' : HiddenIndependentFunctionSpace E' := hiddenIndependentFunctionSpace_gauge _ E hE
  have hL' : normalizedGenerator b (F k h c) ε (scalarTail ε e)
      (visiblePotential b k h c V₀) (visibleLinearPotential a₀ a₁) ∈ E' := by
    rw [normalizedGenerator_eq_filtering b k h c a₀ a₁ ε e V₀ V hV,
      ← hidden_gauge_drift b k h c ε hε₀ hε₁]
    exact filteringOperator_mem_gaugeAlgebra _ E _ V hL
  have hT' : hiddenTransport (g b k h c V - ε) ∈ E' := by
    exact ⟨T b k h c V, T_mem E b k h c V hL h₀,
      hidden_gauge_transport b k h c V ε hk⟩
  have hg₀ : partialDerivative 2 (g b k h c V - ε) = 0 := by
    rw [map_sub, partial_g, hε₂, sub_self]
  obtain ⟨hU₀, hU₁, _, _⟩ := normalized_profiles_hidden_zero b k h c a₀ a₁ ε e V₀
    hV₀ hε₀ hε₁ he₀ he₁
  exact normalized_tail_nilpotent E' hE' b (F k h c) ε (scalarTail ε e)
    (visiblePotential b k h c V₀) (visibleLinearPotential a₀ a₁)
    (g b k h c V - ε) (by simp) hU₀ hU₁ hg₀ hε₀ hε₁ hL' hT' m hm hε


theorem polynomial_profile {m : ℕ} (f : Fin 3 → Smooth) (obs : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f obs)]
    (Λ : Smooth) (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0)
    (hΛ : gaugeDrift Λ f = drift b k h c)
    (hE : HiddenIndependentFunctionSpace (gaugeAlgebra Λ (estimationAlgebra f obs)))
    (hL : filteringOperator (drift b k h c) V ∈ gaugeAlgebra Λ (estimationAlgebra f obs))
    (h₀ : D (drift b k h c) 0 ∈ gaugeAlgebra Λ (estimationAlgebra f obs))
    (h₁ : D (drift b k h c) 1 ∈ gaugeAlgebra Λ (estimationAlgebra f obs)) :
    ∃ (ε e V₀ : Smooth) (a₀ a₁ : ℝ) (p : RealPoly),
      partialDerivative 0 ε = 0 ∧ partialDerivative 1 ε = 0 ∧
      partialDerivative 0 e = 0 ∧ partialDerivative 1 e = 0 ∧
      partialDerivative 2 V₀ = 0 ∧ partialDerivative 2 ε = q k V ∧
      ε = polynomialSmooth p ∧
      V = V₀ + (2 : ℝ) • (ε * F k h c) + e +
        x 2 * (a₀ • x 0 + a₁ • x 1) := by
  obtain ⟨ε, e, V₀, a₀, a₁, hε₀, hε₁, he₀, he₁, hV₀, hε₂, hV⟩ :=
    potential_profile _ hE b k h c V hk hL h₀ h₁
  obtain ⟨pg, hpg⟩ := polynomial_of_polynomial_gradient (g b k h c V)
    (scalar_gradient_polynomial f obs Λ b k h c V hk hΛ hL h₀)
  have hq : q k V = polynomialSmooth (MvPolynomial.pderiv 2 pg) := by
    rw [← partial_g b k h c V, hpg, partialDerivative_polynomialSmooth]
  have hgrad : ∀ i : Fin 3, ∃ p : RealPoly, partialDerivative i ε = polynomialSmooth p := by
    intro i
    fin_cases i
    · exact ⟨0, hε₀.trans polynomialSmooth_zero.symm⟩
    · exact ⟨0, hε₁.trans polynomialSmooth_zero.symm⟩
    · exact ⟨MvPolynomial.pderiv 2 pg, hε₂.trans hq⟩
  obtain ⟨p, hp⟩ := polynomial_of_polynomial_gradient ε hgrad
  exact ⟨ε, e, V₀, a₀, a₁, p, hε₀, hε₁, he₀, he₁, hV₀, hε₂, hp, hV⟩


theorem actual_canonical_obstruction {n : ℕ} (f : Fin 3 → Smooth) (obs : Fin n → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f obs)]
    (Λ : Smooth) (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0)
    (hΛ : gaugeDrift Λ f = drift b k h c)
    (hE : HiddenIndependentFunctionSpace (gaugeAlgebra Λ (estimationAlgebra f obs)))
    (hL : filteringOperator (drift b k h c) V ∈ gaugeAlgebra Λ (estimationAlgebra f obs))
    (h₀ : D (drift b k h c) 0 ∈ gaugeAlgebra Λ (estimationAlgebra f obs))
    (h₁ : D (drift b k h c) 1 ∈ gaugeAlgebra Λ (estimationAlgebra f obs)) : False := by
  obtain ⟨ε, e, V₀, a₀, a₁, p, hε₀, hε₁, he₀, he₁, hV₀, hε₂, hp, hV⟩ :=
    polynomial_profile f obs Λ b k h c V hk hΛ hE hL h₀ h₁
  obtain ⟨P, hP⟩ := exists_univariate_profile ε p hp hε₀ hε₁
  let d := P.natDegree
  let m := max 2 d
  have heps : HiddenDegreeLE (m : ℤ) ε :=
    (univariate_profile_degree P ε hP).mono (by dsimp [m, d]; omega)
  have hepsnil : (partialDerivative 2 ^ (m + 1)) ε = 0 :=
    (hiddenDegreeLE_nat_iff m ε).mp heps
  have hrnil := actual_scalarTail_nilpotent _ hE b k h c a₀ a₁ V ε e V₀ hk hL h₀
    hε₀ hε₁ he₀ he₁ hV₀ hε₂ hV m (by dsimp [m]; omega) hepsnil
  have hr : HiddenDegreeLE (m : ℤ) (scalarTail ε e) :=
    (hiddenDegreeLE_nat_iff m _).mpr hrnil
  let E := gaugeAlgebra (hiddenPrimitive ε) (gaugeAlgebra Λ (estimationAlgebra f obs))
  let _ : FiniteDimensional ℝ (gaugeAlgebra Λ (estimationAlgebra f obs)) :=
    gaugeAlgebra_finiteDimensional Λ _
  let _ : FiniteDimensional ℝ E := gaugeAlgebra_finiteDimensional _ _
  let U₀ := visiblePotential b k h c V₀
  let U₁ := visibleLinearPotential a₀ a₁
  have hnorm : normalizedGenerator b (F k h c) ε (scalarTail ε e) U₀ U₁ ∈ E := by
    rw [normalizedGenerator_eq_filtering b k h c a₀ a₁ ε e V₀ V hV,
      ← hidden_gauge_drift b k h c ε hε₀ hε₁]
    exact filteringOperator_mem_gaugeAlgebra _ _ _ V hL
  have hw : canonicalWeightedOperator (b • x 0) (F k h c) ε
      (U₀ + x 2 * U₁) (scalarTail ε e) ∈ E := by
    rw [canonicalWeightedOperator_normalized]
    exact hnorm
  have hx : partialDerivative 0 ∈ E := by
    have hh := D_mem_gaugeAlgebra (hiddenPrimitive ε) _ (drift b k h c) 0 h₀
    rw [hidden_gauge_drift b k h c ε hε₀ hε₁] at hh
    have hd : D (shiftedDrift b k h c ε) 0 = partialDerivative 0 := by
      simp [D, shiftedDrift]
    rw [hd] at hh
    exact hh
  obtain ⟨hU₀, hU₁, hr₀, hr₁⟩ := normalized_profiles_hidden_zero b k h c a₀ a₁ ε e V₀
    hV₀ hε₀ hε₁ he₀ he₁
  have hg : HiddenDegreeLE 0 (b • x 0) :=
    HiddenDegreeLE.of_hiddenDerivative_eq_zero _ (by simp)
  have hF : HiddenDegreeLE 0 (F k h c) :=
    HiddenDegreeLE.of_hiddenDerivative_eq_zero _ (by simp)
  have hVP : HiddenDegreeLE 1 (U₀ + x 2 * U₁) := by
    apply ((HiddenDegreeLE.of_hiddenDerivative_eq_zero U₀ hU₀).mono (by norm_num)).add
    have ht : HiddenDegreeLE 1 (x 2) := by simpa using hiddenCoordinate_power_degree 1
    simpa using ht.mul (HiddenDegreeLE.of_hiddenDerivative_eq_zero U₁ hU₁)
  have hεvis : ∀ i : Fin 3, i ≠ 2 → partialDerivative i ε = 0 := by
    intro i hi
    fin_cases i
    · change partialDerivative 0 ε = 0
      exact hε₀
    · change partialDerivative 1 ε = 0
      exact hε₁
    · exact (hi rfl).elim
  have hrvis : ∀ i : Fin 3, i ≠ 2 → partialDerivative i (scalarTail ε e) = 0 := by
    intro i hi
    fin_cases i
    · change partialDerivative 0 (scalarTail ε e) = 0
      exact hr₀
    · change partialDerivative 1 (scalarTail ε e) = 0
      exact hr₁
    · exact (hi rfl).elim
  have hF0 : partialDerivative 0 (F k h c) = k • linearFunction (coordinateVector 0) := by
    simp [u, x]
  by_cases hd : d ≤ 2
  · have hm : m = 2 := max_eq_left hd
    obtain ⟨a, ha⟩ := univariate_profile_low_remainder P ε hP hd
    exact sectorTwo_quadratic_actual_obstruction E (b • x 0) (F k h c) ε
      (U₀ + x 2 * U₁) (scalarTail ε e) a k hk hw hx hg hF
      (by simpa [hm] using heps) hεvis hVP (by simpa [hm] using hr) hrvis hF0
      (by simp) (by simpa only [quadraticHiddenProfile, x] using ha)
  · have hd' : 3 ≤ d := by omega
    have hm : m = d := max_eq_right (by omega)
    exact sectorTwo_high_actual_obstruction E (b • x 0) (F k h c) ε
      (U₀ + x 2 * U₁) (scalarTail ε e) P.leadingCoeff k d
      (univariate_profile_nonzero_leading P hd') hk hd' hw hx hg hF
      (by simpa [hm] using heps) hεvis hVP (by simpa [hm] using hr) hrvis hF0
      (by simpa only [powerHiddenProfile, x] using univariate_profile_leading_remainder P ε hP)


end Wong.SmoothModel.SectorTwo.HiddenIndependent

#print axioms Wong.SmoothModel.SectorTwo.HiddenIndependent.actual_canonical_obstruction
#print axioms Wong.SmoothModel.hiddenIndependentFunctionSpace_hiddenFrame


/-! Source segment: HiddenIndependentSectorOne.lean -/

/-! The actual hidden Euler route under the weaker, explicit hypothesis that
all function elements have zero hidden derivative. The canonical gauge and
finite-dimensional Lie words are genuine constructions. No QFree or external
Wong structure theorem is called. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel.HiddenIndependent
open scoped ContDiff


theorem normalized_visible_gauge_hidden_profile
    (E : LieSubalgebra ℝ Operator) (f : Fin 3 → Smooth) (α β δ : ℝ) (Λ B : Smooth)
    (hfun : HiddenIndependentFunctionSpace (hiddenFrameAlgebra α β δ Λ E))
    (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ hiddenFrameAlgebra α β δ Λ E)
    (hD₀ : D f 0 ∈ E) (hD₁ : D f 1 ∈ E)
    (hf₀ : partialDerivative 2 (f 0) = 0) (hf₁ : partialDerivative 2 (f 1) = 0) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧
      ∀ x : State, (partialDerivative 2 Λ).1 x =
        ρ (x 2 - α * x 0 - β * x 1 - δ) := by
  obtain ⟨he₀, he₁⟩ := hiddenShear_symm_visible_vectors α β
  have hz (i : Fin 3) (hi : i ≠ 2) (a : ℝ)
      (he : (hiddenShear α β).symm (coordinateVector i) =
        coordinateVector i + a • coordinateVector 2)
      (hD : D f i ∈ E) (hf : partialDerivative 2 (f i) = 0) :
      directionalDerivative (coordinateVector i + a • coordinateVector 2)
        (partialDerivative 2 Λ) = 0 := by
    have hmem := hiddenFrame_image_mem α β δ Λ E (D f i) hD
    rw [hiddenFrame_D, he, directionalDerivative_add, directionalDerivative_smul,
      coordinate_directionalDerivative, coordinate_directionalDerivative] at hmem
    have hu := firstOrder_hidden_independent_of_function_space _ hfun B
      (-(hiddenAffinePullback α β δ (f i) +
        (partialDerivative i + a • partialDerivative 2) Λ)) hB hJ i hi a hmem
    have hp : partialDerivative 2 (hiddenAffinePullback α β δ (f i)) = 0 := by
      rw [hidden_partial_pullback, hf, map_zero]
    have hc : partialDerivative 2 ((partialDerivative i + a • partialDerivative 2) Λ) =
        directionalDerivative (coordinateVector i + a • coordinateVector 2)
          (partialDerivative 2 Λ) := by
      have ho : partialDerivative i + a • partialDerivative 2 =
          directionalDerivative (coordinateVector i + a • coordinateVector 2) := by
        rw [directionalDerivative_add, directionalDerivative_smul,
          coordinate_directionalDerivative, coordinate_directionalDerivative]
      rw [ho, partialDerivative_directionalDerivative_commute]
    simpa only [map_neg, map_add, hp, zero_add, hc, neg_eq_zero] using hu
  apply exists_slanted_hidden_profile _ α β δ
  · exact hz 0 (by decide) α he₀ hD₀ hf₀
  · exact hz 1 (by decide) β he₁ hD₁ hf₁


theorem normalized_frameDrift_visible_independent
    (E : LieSubalgebra ℝ Operator) (f : Fin 3 → Smooth)
    (α β δ : ℝ) (Λ B : Smooth)
    (hfun : HiddenIndependentFunctionSpace (hiddenFrameAlgebra α β δ Λ E))
    (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ hiddenFrameAlgebra α β δ Λ E)
    (hD₀ : D f 0 ∈ E) (hD₁ : D f 1 ∈ E) :
    partialDerivative 2 (frameDrift f α β δ Λ 0) = 0 ∧
    partialDerivative 2 (frameDrift f α β δ Λ 1) = 0 := by
  obtain ⟨he₀, he₁⟩ := hiddenShear_symm_visible_vectors α β
  have hz (i : Fin 3) (hi : i ≠ 2) (a : ℝ)
      (he : (hiddenShear α β).symm (coordinateVector i) =
        coordinateVector i + a • coordinateVector 2)
      (hD : D f i ∈ E) :
      partialDerivative 2 (hiddenAffinePullback α β δ (f i) +
        (partialDerivative i + a • partialDerivative 2) Λ) = 0 := by
    have hmem := hiddenFrame_image_mem α β δ Λ E (D f i) hD
    rw [hiddenFrame_D, he, directionalDerivative_add, directionalDerivative_smul,
      coordinate_directionalDerivative, coordinate_directionalDerivative] at hmem
    have hu := firstOrder_hidden_independent_of_function_space _ hfun B
      (-(hiddenAffinePullback α β δ (f i) +
        (partialDerivative i + a • partialDerivative 2) Λ)) hB hJ i hi a hmem
    simpa only [map_neg, neg_eq_zero] using hu
  constructor
  · simpa only [frameDrift, frameVectors, Matrix.cons_val_zero,
      directionalDerivative_add, directionalDerivative_smul,
      coordinate_directionalDerivative, LinearMap.add_apply,
      LinearMap.smul_apply] using hz 0 (by decide) α he₀ hD₀
  · simpa only [frameDrift, frameVectors, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.vecHead, Matrix.vecTail,
      directionalDerivative_add, directionalDerivative_smul,
      coordinate_directionalDerivative, LinearMap.add_apply,
      LinearMap.smul_apply] using hz 1 (by decide) β he₁ hD₁


theorem actual_normalizing_gauge_hidden_polynomial
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra)
    (f : Fin 3 → Smooth) (V : Smooth) (α β δ : ℝ) (Λ B : Smooth)
    (hfun : HiddenIndependentFunctionSpace (hiddenFrameAlgebra α β δ Λ E))
    (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ hiddenFrameAlgebra α β δ Λ E)
    (hL : filteringOperator f V ∈ E) (hD₀ : D f 0 ∈ E) (hD₁ : D f 1 ∈ E)
    (hf₀ : partialDerivative 2 (f 0) = 0) (hf₁ : partialDerivative 2 (f 1) = 0)
    (hf₂ : (partialDerivative 2 ^ 2) (f 2) = 0) :
    ∃ p : Polynomial ℝ, ∀ x : State,
      (partialDerivative 2 Λ).1 x = p.eval (x 2 - α*x 0 - β*x 1 - δ) := by
  let F := hiddenFrameAlgebra α β δ Λ E
  let : FiniteDimensional ℝ F := hiddenFrameAlgebra_finiteDimensional α β δ Λ E
  have hFfinite : F ≤ finiteOrderAlgebra :=
    hiddenFrameAlgebra_le_finiteOrder α β δ Λ E hfinite
  obtain ⟨N, hN⟩ := finiteOrderLieAlgebra_uniform_hidden_nilpotence F hFfinite B hB hJ
  let g := frameDrift f α β δ Λ
  let W := hiddenAffinePullback α β δ V
  have hp : normalAction (frameDiffusionNormal α β g W) ∈ F := by
    rw [normalAction_frameDiffusionNormal]
    rw [← actual_transported_filteringOperator]
    exact hiddenFrame_image_mem α β δ Λ E _ hL
  have hc := hN (frameDiffusionNormal α β g W) hp (Finsupp.single 2 1)
  rw [frameDiffusionNormal_hidden_first] at hc
  have hcM : (partialDerivative 2 ^ (N+2)) (-(α • g 0 + β • g 1 + g 2)) = 0 := by
    rw [Nat.add_comm N 2, pow_add, Module.End.mul_apply, hc, map_zero]
  obtain ⟨hg₀, hg₁⟩ := normalized_frameDrift_visible_independent E f α β δ Λ B
    hfun hB hJ hD₀ hD₁
  have hz₀ := hidden_power_zero_of_first (g 0) hg₀ (N+1)
  have hz₁ := hidden_power_zero_of_first (g 1) hg₁ (N+1)
  have hfP : (partialDerivative 2 ^ 2) (hiddenAffinePullback α β δ (f 2)) = 0 := by
    simp only [pow_two, Module.End.mul_apply, hidden_partial_pullback]
    have he : partialDerivative 2 (partialDerivative 2 (f 2)) = 0 := by
      simpa only [pow_two, Module.End.mul_apply] using hf₂
    rw [he, map_zero]
  have hzP := hidden_power_zero_of_second _ hfP N
  have he₂ : g 2 = hiddenAffinePullback α β δ (f 2) + partialDerivative 2 Λ := by
    simp [g, frameDrift, frameVectors, coordinate_directionalDerivative]
  rw [he₂] at hcM
  have hw : (partialDerivative 2 ^ (N+2)) (partialDerivative 2 Λ) = 0 := by
    simpa only [map_neg, map_add, map_smul, hz₀, hz₁, hzP,
      smul_zero, zero_add, neg_eq_zero] using hcM
  obtain ⟨ρ, _hρ, hu⟩ := normalized_visible_gauge_hidden_profile E f α β δ Λ B
    hfun hB hJ hD₀ hD₁ hf₀ hf₁
  exact polynomial_slanted_profile_of_representation_nilpotent
    (partialDerivative 2 Λ) α β δ ρ hu (N+1) hw


structure CanonicalGaugeData {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) where
  Λ : Smooth
  drift_eq : gaugeDrift Λ f = triangularDrift p
  finiteDimensional : FiniteDimensional ℝ (gaugeAlgebra Λ (estimationAlgebra f h))
  finiteOrder : gaugeAlgebra Λ (estimationAlgebra f h) ≤ finiteOrderAlgebra
  normalForm : gaugeAlgebra Λ (estimationAlgebra f h) ≤ normalFormOperators
  functionSpace : HiddenIndependentFunctionSpace (gaugeAlgebra Λ (estimationAlgebra f h))
  filtering_mem : filteringOperator (triangularDrift p) (eta f h) ∈
    gaugeAlgebra Λ (estimationAlgebra f h)
  D_zero_mem : D (triangularDrift p) 0 ∈ gaugeAlgebra Λ (estimationAlgebra f h)
  D_one_mem : D (triangularDrift p) 1 ∈ gaugeAlgebra Λ (estimationAlgebra f h)
  wong_eq : ∀ i j x, (wong (triangularDrift p) i j).1 x = p.matrix x i j


theorem exists_canonicalGaugeData {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hfun : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    Nonempty (CanonicalGaugeData f h p) := by
  obtain ⟨Λ, hΛ⟩ := exists_triangular_gauge f p hform
  have hL : filteringOperator f (eta f h) ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  refine ⟨{
    Λ := Λ
    drift_eq := hΛ
    finiteDimensional := gaugeAlgebra_finiteDimensional Λ _
    finiteOrder := gaugeAlgebra_le_finiteOrder Λ _ (estimationAlgebra_le_finiteOrder f h)
    normalForm := gaugeAlgebra_le_normalFormOperators Λ _
      (estimationAlgebra_le_normalFormOperators f h)
    functionSpace := hiddenIndependentFunctionSpace_gauge Λ _ hfun
    filtering_mem := by
      simpa only [hΛ] using filteringOperator_mem_gaugeAlgebra Λ _ f (eta f h) hL
    D_zero_mem := by
      simpa only [hΛ] using D_mem_gaugeAlgebra Λ _ f 0 (D_mem_of_coordinate_mem f h 0 hx₀)
    D_one_mem := by
      simpa only [hΛ] using D_mem_gaugeAlgebra Λ _ f 1 (D_mem_of_coordinate_mem f h 1 hx₁)
    wong_eq := by
      intro i j x
      rw [← hΛ, wong_gaugeDrift]
      exact hform i j x
  }⟩


theorem affine_hidden_slopes_zero {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hfun : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) : p.k₃ = 0 ∧ p.h₃ = 0 := by
  by_contra hzero
  have hne : p.k₃ ≠ 0 ∨ p.h₃ ≠ 0 := by tauto
  have hμ := ne_of_gt (hiddenSlopeNorm_pos p hne)
  obtain ⟨G⟩ := exists_canonicalGaugeData f h hfun hx₀ hx₁ p hform
  let E := gaugeAlgebra G.Λ (estimationAlgebra f h)
  let : FiniteDimensional ℝ E := G.finiteDimensional
  let α := hiddenSlopeAlpha p
  let β := hiddenSlopeBeta p
  let δ := hiddenSlopeDelta p
  obtain ⟨Λ,B,hB,hJ⟩ := exists_normalized_hiddenEuler E (triangularDrift p) (eta f h)
    p G.wong_eq hμ hb₁ hb₂ G.filtering_mem G.D_zero_mem G.D_one_mem
  let F := hiddenFrameAlgebra α β δ Λ E
  let : FiniteDimensional ℝ F := hiddenFrameAlgebra_finiteDimensional α β δ Λ E
  have hfinite : F ≤ finiteOrderAlgebra :=
    hiddenFrameAlgebra_le_finiteOrder α β δ Λ E G.finiteOrder
  have hnormal : F ≤ normalFormOperators :=
    hiddenFrameAlgebra_le_normalFormOperators α β δ Λ E G.normalForm
  have hfun : HiddenIndependentFunctionSpace F :=
    hiddenIndependentFunctionSpace_hiddenFrame α β δ Λ E G.functionSpace
  have hheat : partialDerivative 2 ^ 2 ∈ F :=
    actual_hiddenFrame_pure_second_mem E G.finiteOrder G.normalForm
      (triangularDrift p) (eta f h) α β δ Λ B G.filtering_mem hB hJ
  let g := frameDrift (triangularDrift p) α β δ Λ
  let V := hiddenAffinePullback α β δ (eta f h)
  have hL : directionalDiffusion α β g V ∈ F := by
    rw [← actual_transported_filteringOperator]
    exact hiddenFrame_image_mem α β δ Λ E _ G.filtering_mem
  obtain ⟨hg₀,hg₁⟩ := normalized_frameDrift_visible_independent E (triangularDrift p)
    α β δ Λ B hfun hB hJ G.D_zero_mem G.D_one_mem
  obtain ⟨q,hqeval⟩ := actual_normalizing_gauge_hidden_polynomial E G.finiteOrder
    (triangularDrift p) (eta f h) α β δ Λ B hfun hB hJ
    G.filtering_mem G.D_zero_mem G.D_one_mem
    (triangularDrift_hidden_visible_partial_zero p 0 (by decide))
    (triangularDrift_hidden_visible_partial_zero p 1 (by decide))
    (triangularDrift_hidden_second_partial_zero p)
  by_cases hd : q.natDegree ≤ 1
  · obtain ⟨c,v,hv,he⟩ := normalized_low_hidden_first_coefficient p α β δ Λ q
      hqeval hd hg₀ hg₁
    have hz := actual_low_frameDiffusion_hidden_slopes_zero F hfinite hnormal B hB hJ
      α β p.k₃ p.h₃ c g V v hg₀ hg₁ hv he hL hheat
    exact hzero hz
  · let d := q.natDegree-2
    have hdegree : q.natDegree = d+2 := by dsimp [d]; omega
    have hres := normalized_high_hidden_first_nilpotent p α β δ Λ q d hdegree
      hqeval hg₀ hg₁
    have hz := actual_high_frameDiffusion_obstruction F hfinite hnormal B hB hJ
      α β q.leadingCoeff d g V hg₀ hg₁ hres hL hheat
    have hqne : q ≠ 0 := by
      intro he
      simp [he] at hd
    exact (Polynomial.leadingCoeff_ne_zero.mpr hqne) hz


end Wong.SmoothModel.HiddenIndependent

#print axioms Wong.SmoothModel.HiddenIndependent.affine_hidden_slopes_zero


/-! Source segment: HiddenIndependentConclusion.lean -/

/-! Actual constancy for affine Wong data whose visible entry is constant,
assuming only that every genuine function element is hidden-independent.
In particular, the exact C2 whole-function classification supplies this
hypothesis; existence of a single quadratic element alone is not substituted
for that classification. No dimension-two classification is invoked. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel.HiddenIndependent
open VisibleHeads _root_.Wong.SmoothModel.SectorTwo

theorem coordinate_model_hiddenIndependent {m : ℕ}
    (e : State ≃L[ℝ] State) (he : CoordinateOrthogonal e)
    (he₂ : e (coordinateVector 2) = coordinateVector 2)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hfun : HiddenIndependentFunctionSpace (estimationAlgebra f h)) :
    HiddenIndependentFunctionSpace
      (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) := by
  rw [← coordinateAlgebra_estimationAlgebra e he]
  exact hiddenIndependentFunctionSpace_coordinate e he₂ _ hfun

theorem translation_model_hiddenIndependent {m : ℕ}
    (z : State) (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hfun : HiddenIndependentFunctionSpace (estimationAlgebra f h)) :
    HiddenIndependentFunctionSpace
      (estimationAlgebra (translationDrift z f) (translationObservations z h)) := by
  rw [← translationAlgebra_estimationAlgebra]
  exact hiddenIndependentFunctionSpace_affine _ z rfl _ hfun


theorem diagonal_sector_two_model {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hfun : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) (hk₃ : p.k₃ = 0) (hh₃ : p.h₃ = 0)
    (hne : p.k₁ ≠ 0 ∨ p.k₂ ≠ 0 ∨ p.h₂ ≠ 0) :
    ∃ (e : State ≃L[ℝ] State) (q : Wong.AffineParameters),
      CoordinateOrthogonal e ∧
      (∀ i j x, (wong (coordinateDrift e f) i j).1 x = q.matrix x i j) ∧
      FiniteDimensional ℝ (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) ∧
      linearRank (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) = 2 ∧
      HiddenIndependentFunctionSpace (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) ∧
      multiplication (linearFunction (coordinateVector 0)) ∈
        estimationAlgebra (coordinateDrift e f) (coordinateObservations e h) ∧
      multiplication (linearFunction (coordinateVector 1)) ∈
        estimationAlgebra (coordinateDrift e f) (coordinateObservations e h) ∧
      q.b₁ = 0 ∧ q.b₂ = 0 ∧ q.k₃ = 0 ∧ q.h₃ = 0 ∧
      q.k₁ ≠ 0 ∧ q.k₂ = 0 ∧ q.h₁ = 0 := by
  obtain ⟨a, b, hab, hk, hl, hh⟩ := exists_diagonalizing_planeRotation p
    (bianchi_slopes f p hp) hne
  let e := planeRotation a b hab
  have he : CoordinateOrthogonal e := planeRotation_orthogonal a b hab
  have he₂ : e (coordinateVector 2) = coordinateVector 2 := by
    funext i
    fin_cases i <;> simp [e, planeRotation_apply, coordinateVector]
  obtain ⟨hb₁', hb₂', hk₃', hh₃'⟩ := rotatedParameters_sector_two_zeros a b p hb₁ hb₂ hk₃ hh₃
  refine ⟨e, rotatedParameters a b p, he, wong_planeRotation a b hab f p hp,
    finiteDimensional_coordinateEstimationAlgebra e he f h, ?_,
    coordinate_model_hiddenIndependent e he he₂ f h hfun,
    planeRotation_coordinate_mem a b hab f h h₀ h₁ 0 (Or.inl rfl),
    planeRotation_coordinate_mem a b hab f h h₀ h₁ 1 (Or.inr rfl),
    hb₁', hb₂', hk₃', hh₃', hk, hl, hh⟩
  rwa [linearRank_coordinateEstimationAlgebra e he]


theorem translated_sector_two_model {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hfun : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hk : p.k₁ ≠ 0) :
    let z := firstHiddenConstantShift p
    let q := translatedParameters z p
    (∀ i j x, (wong (translationDrift z f) i j).1 x = q.matrix x i j) ∧
      FiniteDimensional ℝ (estimationAlgebra (translationDrift z f) (translationObservations z h)) ∧
      linearRank (estimationAlgebra (translationDrift z f) (translationObservations z h)) = 2 ∧
      HiddenIndependentFunctionSpace (estimationAlgebra (translationDrift z f) (translationObservations z h)) ∧
      multiplication (linearFunction (coordinateVector 0)) ∈
        estimationAlgebra (translationDrift z f) (translationObservations z h) ∧
      multiplication (linearFunction (coordinateVector 1)) ∈
        estimationAlgebra (translationDrift z f) (translationObservations z h) ∧
      q.k₀ = 0 ∧ q.k₁ ≠ 0 := by
  dsimp only
  exact ⟨wong_translation_parameters _ f p hp,
    finiteDimensional_translationEstimationAlgebra _ f h,
    linearRank_translationEstimationAlgebra _ f h hrank,
    translation_model_hiddenIndependent _ f h hfun,
    coordinate_mem_translationEstimationAlgebra _ f h hrank 0 h₀,
    coordinate_mem_translationEstimationAlgebra _ f h hrank 1 h₁,
    translated_firstHidden_constant_zero p hk, hk⟩


theorem nonzero_visible_matrix_impossible {n : ℕ} (f : Fin 3 → Smooth) (obs : Fin n → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f obs)]
    (hrank : linearRank (estimationAlgebra f obs) = 2)
    (hq : HiddenIndependentFunctionSpace (estimationAlgebra f obs))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f obs)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f obs)
    (p : Wong.AffineParameters) (hp : ∀ i j z, (wong f i j).1 z = p.matrix z i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) (hk₃ : p.k₃ = 0) (hh₃ : p.h₃ = 0)
    (hne : p.k₁ ≠ 0 ∨ p.k₂ ≠ 0 ∨ p.h₂ ≠ 0) : False := by
  obtain ⟨e, q, he, hqform, hfdq, hrq, hqq, hxq₀, hxq₁,
      hbq₁, hbq₂, hkq₃, hhq₃, hkq, hkq₂, _hhq₁⟩ :=
    diagonal_sector_two_model f obs hrank hq hx₀ hx₁ p hp hb₁ hb₂ hk₃ hh₃ hne
  let f₁ := coordinateDrift e f
  let obs₁ := coordinateObservations e obs
  let _ : FiniteDimensional ℝ (estimationAlgebra f₁ obs₁) := hfdq
  let z := VisibleHeads.firstHiddenConstantShift q
  let q' := VisibleHeads.translatedParameters z q
  let f₂ := translationDrift z f₁
  let obs₂ := translationObservations z obs₁
  obtain ⟨hqform', hfd', hr', hqq', hx'₀, hx'₁, hk'₀, hk'⟩ :=
    translated_sector_two_model f₁ obs₁ hrq hqq hxq₀ hxq₁ q hqform hkq
  let _ : FiniteDimensional ℝ (estimationAlgebra f₂ obs₂) := hfd'
  have htri : triangularDrift q' = drift q'.b₀ q'.k₁ q'.h₂ q'.h₀ :=
    triangularDrift_sector_two q' hbq₁ hbq₂ hkq₂ hkq₃ hhq₃ hk'₀
  obtain ⟨cg⟩ := exists_canonicalGaugeData f₂ obs₂ hqq' hx'₀ hx'₁ q' hqform'
  apply SectorTwo.HiddenIndependent.actual_canonical_obstruction f₂ obs₂ cg.Λ q'.b₀ q'.k₁ q'.h₂ q'.h₀
    (eta f₂ obs₂) hk' (cg.drift_eq.trans htri) cg.functionSpace
  · simpa only [htri] using cg.filtering_mem
  · simpa only [htri] using cg.D_zero_mem
  · simpa only [htri] using cg.D_one_mem


theorem remaining_visible_affine_slopes {n : ℕ} (f : Fin 3 → Smooth) (obs : Fin n → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f obs)]
    (hrank : linearRank (estimationAlgebra f obs) = 2)
    (hq : HiddenIndependentFunctionSpace (estimationAlgebra f obs))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f obs)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f obs)
    (p : Wong.AffineParameters) (hp : ∀ i j z, (wong f i j).1 z = p.matrix z i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) (hk₃ : p.k₃ = 0) (hh₃ : p.h₃ = 0) :
    p.k₁ = 0 ∧ p.k₂ = 0 ∧ p.h₂ = 0 := by
  by_contra! hn
  have hne : p.k₁ ≠ 0 ∨ p.k₂ ≠ 0 ∨ p.h₂ ≠ 0 := by tauto
  exact nonzero_visible_matrix_impossible f obs hrank hq hx₀ hx₁ p hp hb₁ hb₂ hk₃ hh₃ hne


theorem affine_wongConstant_of_hiddenIndependent {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hfun : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j z, (wong f i j).1 z = p.matrix z i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) : WongConstant f := by
  obtain ⟨hk₃, hh₃⟩ := affine_hidden_slopes_zero f h hfun hx₀ hx₁ p hp hb₁ hb₂
  obtain ⟨hk₁, hk₂, hh₂⟩ := remaining_visible_affine_slopes f h hrank hfun hx₀ hx₁
    p hp hb₁ hb₂ hk₃ hh₃
  exact wongConstant_of_independent_affine_slopes_zero f p hp hb₁ hb₂ hk₁ hk₂ hk₃ hh₂ hh₃

/-- The complete C2 function-space classification, including the actual
quadratic member. This is explicitly stronger than mere membership of x₀². -/
def C2FunctionSpace (E : LieSubalgebra ℝ Operator) : Prop :=
  multiplication (smoothMul (linearFunction (coordinateVector 0))
    (linearFunction (coordinateVector 0))) ∈ E ∧
  ∀ u : Smooth, multiplication u ∈ E → ∃ c a b q : ℝ,
    u = c • smoothOne + a • linearFunction (coordinateVector 0) +
      b • linearFunction (coordinateVector 1) +
      q • smoothMul (linearFunction (coordinateVector 0)) (linearFunction (coordinateVector 0))

theorem c2_hiddenIndependent (E : LieSubalgebra ℝ Operator) (hC2 : C2FunctionSpace E) :
    HiddenIndependentFunctionSpace E := by
  intro u hu
  obtain ⟨c, a, b, q, rfl⟩ := hC2.2 u hu
  simp only [map_add, map_smul, partialDerivative_smoothMul,
    partialDerivative_linearFunction, SectorTwo.partial_one]
  simp [coordinateVector, smoothMul_eq_mul]

theorem c2_wongConstant_of_affine_visible_constant {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hC2 : C2FunctionSpace (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j z, (wong f i j).1 z = p.matrix z i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) : WongConstant f :=
  affine_wongConstant_of_hiddenIndependent f h hrank (c2_hiddenIndependent _ hC2)
    hx₀ hx₁ p hp hb₁ hb₂

end Wong.SmoothModel.HiddenIndependent

#print axioms Wong.SmoothModel.HiddenIndependent.affine_wongConstant_of_hiddenIndependent
#print axioms Wong.SmoothModel.HiddenIndependent.c2_wongConstant_of_affine_visible_constant


/-! Source segment: QuadraticShearRigidity.lean -/

/-! A genuine quadratic shear obstruction using only one admitted covariant
derivative. The missing transverse Lie word is literally zero; no membership
of the second visible covariant derivative is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Wong.SmoothModel
open MvPolynomial

theorem actual_quadratic_hidden_shear_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD₀ : D f 0 ∈ estimationAlgebra f h)
    (p : NormalForm) (hp : NormalDegreeLE 1 p)
    (hpE : normalAction p ∈ estimationAlgebra f h)
    (a : Fin 3 → Smooth) (hpa : normalSymbol 1 p = axisVectorSymbol a)
    (c e k : ℝ)
    (ha₀ : partialDerivative 2 (a 0) = 0)
    (ha₁ : partialDerivative 2 (a 1) = 0)
    (hg₂ : partialDerivative 2 (a 2) = c • smoothOne)
    (hg₀ : partialDerivative 0 (a 2) = hiddenAxisAffineCoefficient e k 0)
    (hg₁ : partialDerivative 1 (a 2) = 0) : k = 0 := by
  let K := normalBracket (normalL0 f h) p
  let A := normalBracket (normalD f 0) p
  have hl : NormalDegreeLE 2 (normalL0 f h) :=
    normalDegreeLE_of_action_order _ _ (by
      rw [normalAction_normalL0]; exact L0_mem_orderSpace_two f h)
  have hd : NormalDegreeLE 1 (normalD f 0) :=
    normalDegreeLE_of_action_order _ _ (by
      rw [normalAction_normalD]; exact D_mem_orderSpace_one f 0)
  have hK : NormalDegreeLE 2 K := by
    apply normalDegreeLE_of_action_order
    rw [normalAction_bracket, normalAction_normalL0]
    exact lie_mem_orderSpace_sharp (L0_mem_orderSpace_two f h)
      (action_order_of_normalDegreeLE p 1 hp)
  have hA : NormalDegreeLE 1 A := by
    apply normalDegreeLE_of_action_order
    rw [normalAction_bracket, normalAction_normalD]
    exact lie_mem_orderSpace_sharp (D_mem_orderSpace_one f 0)
      (action_order_of_normalDegreeLE p 1 hp)
  have hKE : normalAction K ∈ estimationAlgebra f h := by
    rw [normalAction_bracket, normalAction_normalL0]
    exact (estimationAlgebra f h).lie_mem
      (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hpE
  have hAE : normalAction A ∈ estimationAlgebra f h := by
    rw [normalAction_bracket, normalAction_normalD]
    exact (estimationAlgebra f h).lie_mem hD₀ hpE
  have hKs : normalSymbol 2 K = symbolPoisson axisEuclideanKinetic (axisVectorSymbol a) := by
    rw [show 2=1+0+1 from rfl, normalSymbol_bracket _ _ 1 0 hl hp,
      normalSymbol_normalL0, hpa]
    rfl
  have hAs : normalSymbol 1 A = axisVectorSymbol (fun j => partialDerivative 0 (a j)) := by
    rw [show 1=0+0+1 from rfl, normalSymbol_bracket _ _ 0 0 hd hp,
      normalSymbol_normalD, hpa, poisson_X_axisVectorSymbol]
  have hz : hiddenAxisAffineCoefficient 0 0 0 = 0 := by
    apply Subtype.ext
    funext z
    simp [hiddenAxisAffineCoefficient, linearFunction, Fin.sum_univ_three]
  have hB : NormalDegreeLE 1 (0 : NormalForm) := fun _ _ => rfl
  have hBE : normalAction (0 : NormalForm) ∈ estimationAlgebra f h := by
    simpa only [map_zero] using (estimationAlgebra f h).zero_mem
  have hout := actual_hiddenAxis_symmetric_ladder_zero (estimationAlgebra f h) K A 0 1 0
    (by decide) hKE hAE hBE hK hA hB c e 0 k 0 0
    (by rw [hKs, kinetic_axisVectorSymbol_project, hg₂])
    (by simp only [hKs, kinetic_axisVectorSymbol_project_pderiv_zero, hg₀,
      ha₀, add_zero, pow_one])
    (by simp [hKs, kinetic_axisVectorSymbol_project_pderiv_one, hg₁, ha₁, hz])
    (by simp only [hAs, axisVectorSymbol_project, hg₀, Nat.zero_add, pow_one])
    (by simp [normalSymbol, hz])
  exact hout.1

theorem actual_firstOrder_quadratic_hidden_shear_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD₀ : D f 0 ∈ estimationAlgebra f h)
    (a : Fin 3 → Smooth) (b : Smooth)
    (hA : firstOrder f a b ∈ estimationAlgebra f h)
    (c e k : ℝ)
    (ha₀ : partialDerivative 2 (a 0) = 0)
    (ha₁ : partialDerivative 2 (a 1) = 0)
    (hg₂ : partialDerivative 2 (a 2) = c • smoothOne)
    (hg₀ : partialDerivative 0 (a 2) = hiddenAxisAffineCoefficient e k 0)
    (hg₁ : partialDerivative 1 (a 2) = 0) : k = 0 := by
  apply actual_quadratic_hidden_shear_zero f h hD₀ (normalFirstOrder f a b)
    (normalFirstOrder_degree_le_one f a b) ?_ a ?_ c e k ha₀ ha₁ hg₂ hg₀ hg₁
  · rwa [normalAction_normalFirstOrder]
  · exact normalSymbol_one_normalFirstOrder f a b

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_quadratic_hidden_shear_zero
#print axioms Wong.SmoothModel.actual_firstOrder_quadratic_hidden_shear_zero
