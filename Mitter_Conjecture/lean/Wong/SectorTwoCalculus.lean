import Wong.AdaptedGauge
import Wong.NormalSymbolsRing
import Wong.HiddenProfiles
import Wong.HiddenPrimitiveProfiles
import Wong.SmoothGeometry

set_option maxHeartbeats 1200000

/- Source section: SectorTwoCommutators -/

/-! Genuine canonical second-sector generator commutators, with the
transported scalar potential retained as an independent actual smooth function. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

abbrev x (i : Fin 3) : Smooth := linearFunction (coordinateVector i)

def F (k h c : ℝ) : Smooth :=
  (k / 2) • (x 0 * x 0) + (h / 2) • (x 1 * x 1) + c • x 1

def u (k : ℝ) : Smooth := k • x 0

def v (h c : ℝ) : Smooth := h • x 1 + c • smoothOne

def drift (b k h c : ℝ) : Fin 3 → Smooth := ![0, b • x 0, F k h c]

@[simp] theorem partial_one (i : Fin 3) : partialDerivative i smoothOne = 0 := by
  simpa only [one_smul] using partialDerivative_const i 1

@[simp] theorem partial_ring_one (i : Fin 3) : partialDerivative i (1 : Smooth) = 0 :=
  partial_one i

@[simp] theorem multiplication_ring_one : multiplication (1 : Smooth) = (1 : Operator) :=
  multiplication_smoothOne

@[simp] theorem multiplication_neg (a : Smooth) : multiplication (-a) = -multiplication a :=
  multiplicationLinear.map_neg a


@[simp] theorem partial_x (i j : Fin 3) :
    partialDerivative i (x j) = (if i = j then (1 : ℝ) else 0) • smoothOne := by
  simp [x, partialDerivative_linearFunction, coordinateVector, Pi.single_apply]

theorem partial_mul (i : Fin 3) (a b : Smooth) :
    partialDerivative i (a * b) = partialDerivative i a * b + a * partialDerivative i b :=
  partialDerivative_smoothMul i a b

@[simp] theorem partial_F (k h c : ℝ) (i : Fin 3) :
    partialDerivative i (F k h c) = ![u k, v h c, 0] i := by
  fin_cases i <;>
    simp [F, u, v, map_add, map_smul, partial_mul, partial_x, smoothOne_eq_one] <;> module

@[simp] theorem partial_u (k : ℝ) (i : Fin 3) :
    partialDerivative i (u k) = (if i = 0 then k else 0) • smoothOne := by
  simp [u]

@[simp] theorem partial_v (h c : ℝ) (i : Fin 3) :
    partialDerivative i (v h c) = (if i = 1 then h else 0) • smoothOne := by
  simp [v]

@[simp] theorem wong_drift (b k h c : ℝ) (i j : Fin 3) :
    wong (drift b k h c) i j =
      !![0, b • smoothOne, u k; -b • smoothOne, 0, v h c; -u k, -v h c, 0] i j := by
  fin_cases i <;> fin_cases j <;> simp [wong, drift] <;> module

def H (b k h c : ℝ) (V : Smooth) (i : Fin 3) : Operator :=
  ⁅filteringOperator (drift b k h c) V, D (drift b k h c) i⁆

theorem H0_eq (b k h c : ℝ) (V : Smooth) :
    H b k h c V 0 = b • D (drift b k h c) 1 +
      multiplication (u k) * D (drift b k h c) 2 +
      (1 / 2 : ℝ) • multiplication (partialDerivative 0 V) := by
  simp [H, lie_filteringOperator_D, filteringRemainder, Fin.sum_univ_three,
    multiplication_smul, multiplication_smoothOne]

theorem H1_eq (b k h c : ℝ) (V : Smooth) :
    H b k h c V 1 = (-b) • D (drift b k h c) 0 +
      multiplication (v h c) * D (drift b k h c) 2 +
      (1 / 2 : ℝ) • multiplication (partialDerivative 1 V) := by
  simp [H, lie_filteringOperator_D, filteringRemainder, Fin.sum_univ_three,
    multiplication_smul, multiplication_smoothOne]
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext z
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.zero_apply,
    multiplication_apply, smoothMul_apply, smooth_coe_mul, smooth_coe_pow,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul,
    Submodule.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]

def s00 (b k : ℝ) (V : Smooth) : Smooth :=
  (-b ^ 2) • smoothOne - u k * u k +
    (1 / 2 : ℝ) • partialDerivative 0 (partialDerivative 0 V)

def s01 (k h c : ℝ) (V : Smooth) : Smooth :=
  -(u k * v h c) + (1 / 2 : ℝ) • partialDerivative 1 (partialDerivative 0 V)

def s11 (b h c : ℝ) (V : Smooth) : Smooth :=
  (-b ^ 2) • smoothOne - v h c * v h c +
    (1 / 2 : ℝ) • partialDerivative 1 (partialDerivative 1 V)

theorem D0_H0 (b k h c : ℝ) (V : Smooth) :
    ⁅D (drift b k h c) 0, H b k h c V 0⁆ =
      k • D (drift b k h c) 2 + multiplication (s00 b k V) := by
  rw [H0_eq]
  simp only [lie_add, lie_smul, operator_lie_mul_right, lie_D_multiplication,
    lie_D_D, wong_drift, partial_u, s00,
    Matrix.cons_val_zero, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two,
    ite_true, multiplication_add, multiplication_sub, multiplication_smul,
    multiplication_smoothOne, multiplication_mul, smoothMul_eq_mul,
    mul_neg, multiplication_neg, smul_mul_assoc, one_mul]
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext z
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.zero_apply,
    multiplication_apply, smoothMul_apply, smooth_coe_mul, smooth_coe_pow,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul,
    Submodule.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  ring

theorem D1_H0 (b k h c : ℝ) (V : Smooth) :
    ⁅D (drift b k h c) 1, H b k h c V 0⁆ = multiplication (s01 k h c V) := by
  rw [H0_eq]
  simp only [lie_add, lie_smul, operator_lie_mul_right, lie_D_multiplication,
    lie_D_D, wong_drift, partial_u, s01,
    Matrix.cons_val_zero, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, zero_smul, multiplication_zero,
    smul_zero, zero_mul, zero_add, multiplication_add, multiplication_smul,
    multiplication_mul, smoothMul_eq_mul, mul_neg, multiplication_neg]
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext z
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.zero_apply,
    multiplication_apply, smoothMul_apply, smooth_coe_mul, smooth_coe_pow,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul,
    Submodule.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  ring

theorem D1_H1 (b k h c : ℝ) (V : Smooth) :
    ⁅D (drift b k h c) 1, H b k h c V 1⁆ =
      h • D (drift b k h c) 2 + multiplication (s11 b h c V) := by
  rw [H1_eq]
  simp only [lie_add, lie_smul, operator_lie_mul_right, lie_D_multiplication,
    lie_D_D, wong_drift, partial_v, s11,
    Matrix.cons_val_zero, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two,
    ite_true, multiplication_add, multiplication_sub, multiplication_smul,
    multiplication_smoothOne, multiplication_mul, smoothMul_eq_mul,
    mul_neg, multiplication_neg, smul_mul_assoc, one_mul]
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext z
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.zero_apply,
    multiplication_apply, smoothMul_apply, smooth_coe_mul, smooth_coe_pow,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul,
    Submodule.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  ring

/-- Every admitted function has zero hidden derivative in the adapted algebra. -/
theorem adapted_hidden_partial_zero (E : LieSubalgebra ℝ Operator)
    (hE : AdaptedFunctionSpace E) (a : Smooth) (ha : multiplication a ∈ E) :
    partialDerivative 2 a = 0 := by
  obtain ⟨c, a₀, a₁, he⟩ := hE a ha
  change a = c • smoothOne + a₀ • x 0 + a₁ • x 1 at he
  simp [he]

/-- An adapted function element with both visible derivatives zero is a true constant. -/
theorem adapted_visible_constant (E : LieSubalgebra ℝ Operator)
    (hE : AdaptedFunctionSpace E) (a : Smooth) (ha : multiplication a ∈ E)
    (h₀ : partialDerivative 0 a = 0) (h₁ : partialDerivative 1 a = 0) :
    ∃ c : ℝ, a = c • smoothOne := by
  obtain ⟨c, a₀, a₁, he⟩ := hE a ha
  change a = c • smoothOne + a₀ • x 0 + a₁ • x 1 at he
  have hz₀ : a₀ • smoothOne = (0 : Smooth) := by simpa [he] using h₀
  have hz₁ : a₁ • smoothOne = (0 : Smooth) := by simpa [he] using h₁
  have ha₀ : a₀ = 0 := by
    have hh := congrArg (fun w : Smooth => w.1 (0 : State)) hz₀
    simpa [smoothOne] using hh
  have ha₁ : a₁ = 0 := by
    have hh := congrArg (fun w : Smooth => w.1 (0 : State)) hz₁
    simpa [smoothOne] using hh
  exact ⟨c, by simpa [ha₀, ha₁] using he⟩

theorem D0_D0_H0 (b k h c : ℝ) (V : Smooth) :
    ⁅D (drift b k h c) 0, ⁅D (drift b k h c) 0, H b k h c V 0⁆⁆ =
      multiplication ((-k) • u k + partialDerivative 0 (s00 b k V)) := by
  rw [D0_H0, lie_add, lie_smul, lie_D_D, lie_D_multiplication, wong_drift]
  simp only [Matrix.cons_val_zero, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, multiplication_add,
    multiplication_smul]
  rw [show multiplication (-u k) = -multiplication (u k) from multiplicationLinear.map_neg _]
  module

theorem D1_D0_H0 (b k h c : ℝ) (V : Smooth) :
    ⁅D (drift b k h c) 1, ⁅D (drift b k h c) 0, H b k h c V 0⁆⁆ =
      multiplication ((-k) • v h c + partialDerivative 1 (s00 b k V)) := by
  rw [D0_H0, lie_add, lie_smul, lie_D_D, lie_D_multiplication, wong_drift]
  simp only [Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, multiplication_add,
    multiplication_smul]
  rw [show multiplication (-v h c) = -multiplication (v h c) from multiplicationLinear.map_neg _]
  module

def W (V : Smooth) : Smooth := partialDerivative 2 V

theorem hidden_s00 (b k : ℝ) (V : Smooth) :
    partialDerivative 2 (s00 b k V) =
      (1 / 2 : ℝ) • partialDerivative 0 (partialDerivative 0 (W V)) := by
  simp only [s00, map_add, map_sub, map_smul, partial_one, partial_mul, partial_u,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, zero_smul, smul_zero, zero_mul, mul_zero,
    add_zero, sub_zero, zero_add]
  rw [partialDerivative_commute_apply 2 0,
    partialDerivative_commute_apply 2 0]
  rfl

theorem hidden_s01 (k h c : ℝ) (V : Smooth) :
    partialDerivative 2 (s01 k h c V) =
      (1 / 2 : ℝ) • partialDerivative 1 (partialDerivative 0 (W V)) := by
  simp only [s01, map_add, map_neg, map_smul, partial_mul, partial_u, partial_v,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    ite_false, zero_smul, smul_zero, zero_mul, mul_zero, add_zero, neg_zero, zero_add]
  rw [partialDerivative_commute_apply 2 1,
    partialDerivative_commute_apply 2 0]
  rfl

theorem hidden_s11 (b h c : ℝ) (V : Smooth) :
    partialDerivative 2 (s11 b h c V) =
      (1 / 2 : ℝ) • partialDerivative 1 (partialDerivative 1 (W V)) := by
  simp only [s11, map_add, map_sub, map_smul, partial_one, partial_mul, partial_v,
    show (2 : Fin 3) ≠ 1 by decide, ite_false, zero_smul, smul_zero, zero_mul, mul_zero,
    add_zero, sub_zero, zero_add]
  rw [partialDerivative_commute_apply 2 1,
    partialDerivative_commute_apply 2 1]
  rfl

end Wong.SmoothModel.SectorTwo

/- Source section: SectorTwoHessian -/

/-! Actual Lie membership forces the hidden derivative of the potential
into the required visible Hessian shape, without an assumed Taylor expansion. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

theorem half_smul_eq_zero (a : Smooth) (ha : (1 / 2 : ℝ) • a = 0) : a = 0 := by
  have hh := congrArg (fun z : Smooth => (2 : ℝ) • z) ha
  norm_num [smul_smul] at hh
  exact hh

theorem H_mem (E : LieSubalgebra ℝ Operator) (b k h c : ℝ) (V : Smooth)
    (hL : filteringOperator (drift b k h c) V ∈ E) (i : Fin 3)
    (hi : D (drift b k h c) i ∈ E) : H b k h c V i ∈ E := E.lie_mem hL hi

theorem hessian_mixed_zero (E : LieSubalgebra ℝ Operator) (hE : AdaptedFunctionSpace E)
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

theorem hessian_diagonal_relation (E : LieSubalgebra ℝ Operator) (hE : AdaptedFunctionSpace E)
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

theorem third_first_visible_zero (E : LieSubalgebra ℝ Operator) (hE : AdaptedFunctionSpace E)
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

def q (k : ℝ) (V : Smooth) : Smooth :=
  k⁻¹ • ((1 / 2 : ℝ) • partialDerivative 0 (partialDerivative 0 (W V)))

theorem q_visible_partials_zero (E : LieSubalgebra ℝ Operator) (hE : AdaptedFunctionSpace E)
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

end Wong.SmoothModel.SectorTwo

/- Source section: SectorTwoPotential -/

/-! The actual second-sector scalar potential admits the required global
hidden-primitive decomposition. Every scalar restriction is obtained from
actual Lie membership in the adapted algebra. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

def T (b k h c : ℝ) (V : Smooth) : Operator :=
  k⁻¹ • ⁅D (drift b k h c) 0, H b k h c V 0⁆

theorem T_eq (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0) :
    T b k h c V = D (drift b k h c) 2 + multiplication (k⁻¹ • s00 b k V) := by
  simp [T, D0_H0, smul_add, smul_smul, hk]

theorem T_mem (E : LieSubalgebra ℝ Operator) (b k h c : ℝ) (V : Smooth)
    (hL : filteringOperator (drift b k h c) V ∈ E)
    (h₀ : D (drift b k h c) 0 ∈ E) : T b k h c V ∈ E :=
  E.smul_mem k⁻¹ (E.lie_mem h₀ (H_mem E b k h c V hL 0 h₀))

theorem transport_bracket (f : Fin 3 → Smooth) (a s t : Smooth)
    (ha : partialDerivative 2 a = 0) :
    ⁅D f 2 + multiplication s, multiplication a * D f 2 + multiplication t⁆ =
      multiplication (partialDerivative 2 t - a * partialDerivative 2 s) := by
  have hneg : ⁅multiplication s, D f 2⁆ = -multiplication (partialDerivative 2 s) := by
    rw [← lie_skew, lie_D_multiplication]
  simp only [add_lie, lie_add, operator_lie_mul_right, lie_D_multiplication,
    lie_self, lie_multiplication_multiplication, ha, multiplication_zero,
    zero_mul, mul_zero, zero_add, add_zero, hneg, mul_neg,
    multiplication_mul, smoothMul_eq_mul, multiplication_sub]
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext z
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.zero_apply,
    multiplication_apply, smoothMul_apply, smooth_coe_mul, smooth_coe_pow, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_zero, Pi.add_apply,
    Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  ring

def B0 (k : ℝ) (V : Smooth) : Smooth :=
  (1 / 2 : ℝ) • partialDerivative 0 (W V) - u k * q k V

def B1 (k h c : ℝ) (V : Smooth) : Smooth :=
  (1 / 2 : ℝ) • partialDerivative 1 (W V) - v h c * q k V

theorem T_H0 (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0) :
    ⁅T b k h c V, H b k h c V 0 - b • D (drift b k h c) 1⁆ =
      multiplication (B0 k V) := by
  have he : H b k h c V 0 - b • D (drift b k h c) 1 =
      multiplication (u k) * D (drift b k h c) 2 +
        multiplication ((1 / 2 : ℝ) • partialDerivative 0 V) := by
    rw [H0_eq, multiplication_smul]
    module
  rw [he, T_eq b k h c V hk, transport_bracket]
  · congr 1
    simp only [map_smul, hidden_s00, B0, q, W]
    rw [partialDerivative_commute_apply 2 0]
  · simp

theorem T_H1 (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0) :
    ⁅T b k h c V, H b k h c V 1 + b • D (drift b k h c) 0⁆ =
      multiplication (B1 k h c V) := by
  have he : H b k h c V 1 + b • D (drift b k h c) 0 =
      multiplication (v h c) * D (drift b k h c) 2 +
        multiplication ((1 / 2 : ℝ) • partialDerivative 1 V) := by
    rw [H1_eq, multiplication_smul]
    module
  rw [he, T_eq b k h c V hk, transport_bracket]
  · congr 1
    simp only [map_smul, hidden_s00, B1, q, W]
    rw [partialDerivative_commute_apply 2 1]
  · simp

theorem B_visible_partials (E : LieSubalgebra ℝ Operator) (hE : AdaptedFunctionSpace E)
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

theorem B_constants (E : LieSubalgebra ℝ Operator) (hE : AdaptedFunctionSpace E)
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

/-- Global scalar-potential normal form obtained from the actual adapted Lie algebra. -/
theorem potential_profile (E : LieSubalgebra ℝ Operator) (hE : AdaptedFunctionSpace E)
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

end Wong.SmoothModel.SectorTwo

/- Source section: SectorTwoFirstOrder -/

/-! Actual first-order extraction makes the scalar of the hidden transport
operator polynomial, without assuming the hidden covariant derivative belongs
to the estimation algebra. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

def g (b k h c : ℝ) (V : Smooth) : Smooth := k⁻¹ • s00 b k V - F k h c

theorem T_partial (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0) :
    T b k h c V = partialDerivative 2 + multiplication (g b k h c V) := by
  rw [T_eq b k h c V hk]
  simp only [D, drift, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, g, multiplication_sub]
  module

theorem partial_g (b k h c : ℝ) (V : Smooth) :
    partialDerivative 2 (g b k h c V) = q k V := by
  simp only [g, map_sub, map_smul, hidden_s00, partial_F, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
    sub_zero, q]

theorem filtering_hidden_partial (f : Fin 3 → Smooth) (V : Smooth)
    (hf : ∀ i, partialDerivative 2 (f i) = 0) :
    ⁅filteringOperator f V, partialDerivative 2⁆ =
      (1 / 2 : ℝ) • multiplication (partialDerivative 2 V) := by
  have hD (i : Fin 3) : ⁅D f i, partialDerivative 2⁆ = 0 := by
    have hm : ⁅multiplication (f i), partialDerivative 2⁆ = 0 := by
      rw [← lie_skew, lie_partial_multiplication, hf, multiplication_zero, neg_zero]
    simp only [D, sub_lie, lie_partial_partial, hm, sub_self]
  have hV : ⁅multiplication V, partialDerivative 2⁆ =
      -multiplication (partialDerivative 2 V) := by
    rw [← lie_skew, lie_partial_multiplication]
  simp only [filteringOperator, sub_lie, smul_lie, sum_lie,
    operator_lie_mul_left, hD, zero_mul, mul_zero, zero_add, Finset.sum_const_zero,
    smul_zero, hV, smul_neg, zero_sub, neg_neg]

theorem L_T_firstOrder (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0) :
    ⁅filteringOperator (drift b k h c) V, T b k h c V⁆ =
      firstOrder (drift b k h c)
        (fun i => partialDerivative i (g b k h c V))
        ((1 / 2 : ℝ) • W V + (1 / 2 : ℝ) •
          ∑ i : Fin 3, partialDerivative i (partialDerivative i (g b k h c V))) := by
  have hf (i : Fin 3) : partialDerivative 2 (drift b k h c i) = 0 := by
    fin_cases i <;> simp [drift]
  rw [T_partial b k h c V hk, lie_add, filtering_hidden_partial _ _ hf,
    lie_filteringOperator_multiplication]
  simp only [firstOrder, multiplication_add, multiplication_smul, W]
  module

theorem scalar_gradient_polynomial {m : ℕ} (f : Fin 3 → Smooth) (obs : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f obs)]
    (Λ : Smooth) (b k h c : ℝ) (V : Smooth) (hk : k ≠ 0)
    (hΛ : gaugeDrift Λ f = drift b k h c)
    (hL : filteringOperator (drift b k h c) V ∈ gaugeAlgebra Λ (estimationAlgebra f obs))
    (h₀ : D (drift b k h c) 0 ∈ gaugeAlgebra Λ (estimationAlgebra f obs)) :
    ∀ i : Fin 3, ∃ p : RealPoly,
      partialDerivative i (g b k h c V) = polynomialSmooth p := by
  have he : firstOrder (gaugeDrift Λ f)
      (fun i => partialDerivative i (g b k h c V))
      ((1 / 2 : ℝ) • W V + (1 / 2 : ℝ) •
        ∑ i : Fin 3, partialDerivative i (partialDerivative i (g b k h c V))) ∈
        gaugeAlgebra Λ (estimationAlgebra f obs) := by
    rw [hΛ, ← L_T_firstOrder b k h c V hk]
    exact (gaugeAlgebra Λ (estimationAlgebra f obs)).lie_mem hL
      (T_mem _ b k h c V hL h₀)
  obtain ⟨N, hN⟩ := firstOrder_gauge_coefficients_uniform_polynomial_degree Λ f obs
  intro i
  obtain ⟨p, _hp, hp⟩ := hN _ _ he i
  refine ⟨p, ?_⟩
  apply Subtype.ext
  funext z
  exact (hp z).symm

end Wong.SmoothModel.SectorTwo

/- Source section: SectorTwoAdjointCalculus -/

/-! Repeated actual commutators with a hidden transport operator. The
visible scalar in this operator is arbitrary; it is never replaced by -F. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

def hiddenTransport (g₀ : Smooth) : Operator := partialDerivative 2 + multiplication g₀

abbrev hiddenAd (g₀ : Smooth) : Module.End ℝ Operator :=
  LieAlgebra.ad ℝ Operator (hiddenTransport g₀)

@[simp] theorem hiddenTransport_multiplier (g₀ a : Smooth) :
    ⁅hiddenTransport g₀, multiplication a⁆ = multiplication (partialDerivative 2 a) := by
  simp [hiddenTransport, add_lie, lie_partial_multiplication]

@[simp] theorem hiddenTransport_partial (g₀ : Smooth) (i : Fin 3) :
    ⁅hiddenTransport g₀, partialDerivative i⁆ = -multiplication (partialDerivative i g₀) := by
  rw [hiddenTransport, add_lie, lie_partial_partial, zero_add,
    ← lie_skew, lie_partial_multiplication]

theorem hiddenAd_pow_multiplier (g₀ a : Smooth) (n : ℕ) :
    (hiddenAd g₀ ^ n) (multiplication a) = multiplication ((partialDerivative 2 ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LieAlgebra.ad_apply,
      hiddenTransport_multiplier, pow_succ', Module.End.mul_apply]

theorem hiddenAd_pow_monomial (g₀ a : Smooth)
    (hg : partialDerivative 2 g₀ = 0) (n : ℕ) :
    (hiddenAd g₀ ^ n) (multiplication a * partialDerivative 2) =
      multiplication ((partialDerivative 2 ^ n) a) * partialDerivative 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LieAlgebra.ad_apply,
      operator_lie_mul_right, hiddenTransport_multiplier, hiddenTransport_partial,
      hg, multiplication_zero, neg_zero, mul_zero, add_zero,
      pow_succ', Module.End.mul_apply]

theorem hidden_derivative_visible_partial (g₀ : Smooth)
    (hg : partialDerivative 2 g₀ = 0) (i : Fin 3) :
    partialDerivative 2 (partialDerivative i g₀) = 0 := by
  rw [partialDerivative_commute_apply, hg, map_zero]

theorem hiddenTransport_double_partial_square (g₀ : Smooth)
    (hg : partialDerivative 2 g₀ = 0) (i : Fin 3) :
    ⁅hiddenTransport g₀, ⁅hiddenTransport g₀, partialDerivative i * partialDerivative i⁆⁆ =
      (2 : ℝ) • multiplication (partialDerivative i g₀ * partialDerivative i g₀) := by
  rw [operator_lie_mul_right]
  simp only [lie_add, operator_lie_mul_right, hiddenTransport_partial, lie_neg,
    hiddenTransport_multiplier, hidden_derivative_visible_partial g₀ hg,
    multiplication_zero, neg_zero, zero_mul, mul_zero, add_zero, zero_add,
    neg_mul_neg, multiplication_mul, smoothMul_eq_mul]
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  funext z
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.zero_apply,
    multiplication_apply, smoothMul_apply, smooth_coe_mul, smooth_coe_pow, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_zero, Pi.add_apply,
    Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  ring

theorem hiddenTransport_double_visible_monomial (g₀ a : Smooth)
    (hg : partialDerivative 2 g₀ = 0) (ha : partialDerivative 2 a = 0) (i : Fin 3) :
    ⁅hiddenTransport g₀, ⁅hiddenTransport g₀, multiplication a * partialDerivative i⁆⁆ = 0 := by
  rw [operator_lie_mul_right]
  simp only [hiddenTransport_multiplier, ha, multiplication_zero, zero_mul, zero_add,
    hiddenTransport_partial, mul_neg, lie_neg, operator_lie_mul_right, hidden_derivative_visible_partial g₀ hg, mul_zero, add_zero, neg_zero]

def gradientNorm (g₀ : Smooth) : Smooth :=
  ∑ i : Fin 3, partialDerivative i g₀ * partialDerivative i g₀

theorem gradientNorm_hidden_zero (g₀ : Smooth) (hg : partialDerivative 2 g₀ = 0) :
    partialDerivative 2 (gradientNorm g₀) = 0 := by
  simp only [gradientNorm, map_sum, partial_mul,
    hidden_derivative_visible_partial g₀ hg, zero_mul, mul_zero,
    zero_add, Finset.sum_const_zero]

/-- The part of the normalized generator with no nonlinear hidden profile. -/
def stationaryGenerator (b : ℝ) (F U₀ U₁ : Smooth) : Operator :=
  (1 / 2 : ℝ) • ∑ i : Fin 3, partialDerivative i * partialDerivative i -
    b • (multiplication (x 0) * partialDerivative 1) -
    multiplication F * partialDerivative 2 + multiplication (U₀ + x 2 * U₁)

theorem stationaryGenerator_double (b : ℝ) (F U₀ U₁ g₀ : Smooth)
    (hF : partialDerivative 2 F = 0) (hU₀ : partialDerivative 2 U₀ = 0)
    (hU₁ : partialDerivative 2 U₁ = 0) (hg : partialDerivative 2 g₀ = 0) :
    (hiddenAd g₀ ^ 2) (stationaryGenerator b F U₀ U₁) = multiplication (gradientNorm g₀) := by
  have hx : partialDerivative 2 (x 0) = 0 := by simp
  have hU : partialDerivative 2 (partialDerivative 2 (U₀ + x 2 * U₁)) = 0 := by
    simp [partial_mul, hU₀, hU₁]
  change ⁅hiddenTransport g₀, ⁅hiddenTransport g₀, stationaryGenerator b F U₀ U₁⁆⁆ = _
  simp only [stationaryGenerator, lie_add, lie_sub, lie_smul, lie_sum,
    hiddenTransport_double_partial_square g₀ hg,
    hiddenTransport_double_visible_monomial g₀ _ hg hx,
    hiddenTransport_double_visible_monomial g₀ _ hg hF,
    hiddenTransport_multiplier, hU, multiplication_zero, smul_zero, sub_zero, add_zero]
  simp only [← Finset.smul_sum, smul_smul, gradientNorm, multiplication_sum]
  norm_num

theorem stationaryGenerator_triple (b : ℝ) (F U₀ U₁ g₀ : Smooth)
    (hF : partialDerivative 2 F = 0) (hU₀ : partialDerivative 2 U₀ = 0)
    (hU₁ : partialDerivative 2 U₁ = 0) (hg : partialDerivative 2 g₀ = 0) :
    (hiddenAd g₀ ^ 3) (stationaryGenerator b F U₀ U₁) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ', Module.End.mul_apply,
    stationaryGenerator_double b F U₀ U₁ g₀ hF hU₀ hU₁ hg, LieAlgebra.ad_apply,
    hiddenTransport_multiplier, gradientNorm_hidden_zero g₀ hg, multiplication_zero]

theorem stationaryGenerator_power (b : ℝ) (F U₀ U₁ g₀ : Smooth)
    (hF : partialDerivative 2 F = 0) (hU₀ : partialDerivative 2 U₀ = 0)
    (hU₁ : partialDerivative 2 U₁ = 0) (hg : partialDerivative 2 g₀ = 0)
    (n : ℕ) (hn : 2 ≤ n) :
    (hiddenAd g₀ ^ n) (stationaryGenerator b F U₀ U₁) =
      multiplication (if n = 2 then gradientNorm g₀ else 0) := by
  by_cases hn₂ : n = 2
  · subst n
    simpa using stationaryGenerator_double b F U₀ U₁ g₀ hF hU₀ hU₁ hg
  · have he : n = (n - 3) + 3 := by omega
    rw [ite_eq_right hn₂, he, pow_add, Module.End.mul_apply,
      stationaryGenerator_triple b F U₀ U₁ g₀ hF hU₀ hU₁ hg, map_zero,
      multiplication_zero]

/-- The genuine normal-order expression after the hidden gauge. -/
def normalizedGenerator (b : ℝ) (F ε r U₀ U₁ : Smooth) : Operator :=
  stationaryGenerator b F U₀ U₁ - multiplication ε * partialDerivative 2 -
    (1 / 2 : ℝ) • multiplication (partialDerivative 2 ε + r)

theorem normalizedGenerator_ad_power (b : ℝ) (F ε r U₀ U₁ g₀ : Smooth)
    (hF : partialDerivative 2 F = 0) (hU₀ : partialDerivative 2 U₀ = 0)
    (hU₁ : partialDerivative 2 U₁ = 0) (hg : partialDerivative 2 g₀ = 0)
    (n : ℕ) (hn : 2 ≤ n) :
    (hiddenAd g₀ ^ n) (normalizedGenerator b F ε r U₀ U₁) =
      multiplication (if n = 2 then gradientNorm g₀ else 0) -
      multiplication ((partialDerivative 2 ^ n) ε) * partialDerivative 2 -
      (1 / 2 : ℝ) • multiplication
        ((partialDerivative 2 ^ (n + 1)) ε + (partialDerivative 2 ^ n) r) := by
  simp only [normalizedGenerator, map_sub, map_smul,
    stationaryGenerator_power b F U₀ U₁ g₀ hF hU₀ hU₁ hg n hn,
    hiddenAd_pow_monomial g₀ ε hg, hiddenAd_pow_multiplier, map_add,
    pow_succ, Module.End.mul_apply]

theorem partial_hidden_power_commute (a : Smooth) (i : Fin 3) (n : ℕ) :
    partialDerivative i ((partialDerivative 2 ^ n) a) =
      (partialDerivative 2 ^ n) (partialDerivative i a) := by
  have hc : Commute (partialDerivative i) (partialDerivative 2) :=
    partialDerivative_commute i 2
  exact congrArg (fun A : Operator => A a) (hc.pow_right n).eq

theorem hiddenAd_pow_mem (E : LieSubalgebra ℝ Operator) (g₀ : Smooth)
    (hT : hiddenTransport g₀ ∈ E) (L : Operator) (hL : L ∈ E) (n : ℕ) :
    (hiddenAd g₀ ^ n) L ∈ E := by
  induction n with
  | zero => exact hL
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
    exact E.lie_mem hT ih

/-- The tail-degree bound is forced by a real function element in E.
No bound on the tail r is assumed. -/
theorem normalized_tail_nilpotent (E : LieSubalgebra ℝ Operator)
    (hE : AdaptedFunctionSpace E) (b : ℝ) (F ε r U₀ U₁ g₀ : Smooth)
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

end Wong.SmoothModel.SectorTwo

/- Source section: SectorTwoNormalization -/

/-! Genuine gauge normalization of the canonical second-sector generator.
The potential is transported unchanged until its already proved profile is
expanded; the transformed operator is not rebuilt from a new eta. -/

noncomputable section
namespace Wong.SmoothModel.SectorTwo

theorem covariant_square_normal (f : Fin 3 → Smooth) (i : Fin 3) :
    D f i * D f i = partialDerivative i * partialDerivative i -
      (2 : ℝ) • (multiplication (f i) * partialDerivative i) +
      multiplication (f i * f i - partialDerivative i (f i)) := by
  simp only [D, sub_mul, mul_sub, partial_mul_multiplication, multiplication_mul,
    smoothMul_eq_mul, multiplication_sub]
  module

def shiftedDrift (b k h c : ℝ) (ε : Smooth) : Fin 3 → Smooth :=
  ![0, b • x 0, F k h c + ε]

theorem filtering_shifted_normal (b k h c : ℝ) (ε V : Smooth) :
    filteringOperator (shiftedDrift b k h c ε) V =
      (1 / 2 : ℝ) • ∑ i : Fin 3, partialDerivative i * partialDerivative i -
        b • (multiplication (x 0) * partialDerivative 1) -
        multiplication (F k h c + ε) * partialDerivative 2 +
        (1 / 2 : ℝ) • multiplication
          ((b ^ 2) • (x 0 * x 0) + (F k h c + ε) * (F k h c + ε) -
            partialDerivative 2 ε - V) := by
  have hs : (b • x 0) * (b • x 0) = (b ^ 2) • (x 0 * x 0) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring
  simp only [filteringOperator, covariant_square_normal, shiftedDrift,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two,
    map_add, map_smul, map_zero, partial_F, partial_x,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, zero_smul, smul_zero, zero_mul,
    zero_sub, multiplication_zero, sub_zero, zero_add,
    hs, multiplication_add, multiplication_sub, multiplication_smul, smul_mul_assoc]
  module

def visiblePotential (b k h c : ℝ) (V₀ : Smooth) : Smooth :=
  (1 / 2 : ℝ) • ((b ^ 2) • (x 0 * x 0) + F k h c * F k h c - V₀)

def visibleLinearPotential (a₀ a₁ : ℝ) : Smooth :=
  (- (1 / 2 : ℝ)) • (a₀ • x 0 + a₁ • x 1)

def scalarTail (ε e : Smooth) : Smooth := e - ε * ε

theorem normalizedGenerator_eq_filtering (b k h c a₀ a₁ : ℝ) (ε e V₀ V : Smooth)
    (hV : V = V₀ + (2 : ℝ) • (ε * F k h c) + e +
      x 2 * (a₀ • x 0 + a₁ • x 1)) :
    normalizedGenerator b (F k h c) ε (scalarTail ε e)
      (visiblePotential b k h c V₀) (visibleLinearPotential a₀ a₁) =
      filteringOperator (shiftedDrift b k h c ε) V := by
  have hs : (1 / 2 : ℝ) •
      ((b ^ 2) • (x 0 * x 0) + (F k h c + ε) * (F k h c + ε) -
        partialDerivative 2 ε - V) =
      visiblePotential b k h c V₀ + x 2 * visibleLinearPotential a₀ a₁ -
        (1 / 2 : ℝ) • (partialDerivative 2 ε + scalarTail ε e) := by
    rw [hV]
    apply Subtype.ext
    funext z
    change (1 / 2 : ℝ) *
      (b ^ 2 * ((x 0).1 z * (x 0).1 z) + ((F k h c).1 z + ε.1 z) *
        ((F k h c).1 z + ε.1 z) - (partialDerivative 2 ε).1 z -
        (V₀.1 z + 2 * (ε.1 z * (F k h c).1 z) + e.1 z +
          (x 2).1 z * (a₀ * (x 0).1 z + a₁ * (x 1).1 z))) =
      (1 / 2 : ℝ) * (b ^ 2 * ((x 0).1 z * (x 0).1 z) +
        (F k h c).1 z * (F k h c).1 z - V₀.1 z) +
      (x 2).1 z * (-(1 / 2 : ℝ) * (a₀ * (x 0).1 z + a₁ * (x 1).1 z)) -
      (1 / 2 : ℝ) * ((partialDerivative 2 ε).1 z + (e.1 z - ε.1 z * ε.1 z))
    ring
  have hm := congrArg multiplication hs
  simp only [multiplication_smul] at hm
  rw [filtering_shifted_normal, hm]
  simp only [normalizedGenerator, stationaryGenerator, multiplication_add,
    multiplication_sub, multiplication_smul, add_mul]
  module

theorem hidden_gauge_drift (b k h c : ℝ) (ε : Smooth)
    (hε₀ : partialDerivative 0 ε = 0) (hε₁ : partialDerivative 1 ε = 0) :
    gaugeDrift (hiddenPrimitive ε) (drift b k h c) = shiftedDrift b k h c ε := by
  obtain ⟨hΛ₀, hΛ₁⟩ := hiddenPrimitive_visible_partials ε hε₀ hε₁
  funext i
  fin_cases i <;> simp [gaugeDrift, drift, shiftedDrift, hΛ₀, hΛ₁,
    partialDerivative_hiddenPrimitive]

theorem hidden_gauge_transport (b k h c : ℝ) (V ε : Smooth) (hk : k ≠ 0) :
    gaugeConjugation (hiddenPrimitive ε) (T b k h c V) =
      hiddenTransport (g b k h c V - ε) := by
  rw [T_partial b k h c V hk, map_add, gaugeConjugation_partialDerivative,
    gaugeConjugation_multiplication, partialDerivative_hiddenPrimitive]
  simp only [hiddenTransport, multiplication_sub]
  module

theorem normalized_profiles_hidden_zero (b k h c a₀ a₁ : ℝ) (ε e V₀ : Smooth)
    (hV₀ : partialDerivative 2 V₀ = 0)
    (hε₀ : partialDerivative 0 ε = 0) (hε₁ : partialDerivative 1 ε = 0)
    (he₀ : partialDerivative 0 e = 0) (he₁ : partialDerivative 1 e = 0) :
    partialDerivative 2 (visiblePotential b k h c V₀) = 0 ∧
    partialDerivative 2 (visibleLinearPotential a₀ a₁) = 0 ∧
    partialDerivative 0 (scalarTail ε e) = 0 ∧ partialDerivative 1 (scalarTail ε e) = 0 := by
  simp [visiblePotential, visibleLinearPotential, scalarTail, partial_mul,
    hV₀, hε₀, hε₁, he₀, he₁]

/-- The nilpotence conclusion is obtained in the genuine second gauge of E. -/
theorem actual_scalarTail_nilpotent (E : LieSubalgebra ℝ Operator)
    (hE : AdaptedFunctionSpace E) (b k h c a₀ a₁ : ℝ) (V ε e V₀ : Smooth)
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
  have hE' : AdaptedFunctionSpace E' := adaptedFunctionSpace_gauge _ E hE
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

end Wong.SmoothModel.SectorTwo
