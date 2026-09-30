import Wong.EulerFiniteModule

/-!
# The actual hidden Euler adjoint on faithful normal coefficients

All identities in this file concern the real smooth differential operators
and their injective normal form representation.
-/

noncomputable section
set_option maxHeartbeats 800000
namespace Wong.EulerFiniteModule

/-- Polynomial evaluation respects a genuine linear intertwiner. -/
theorem aeval_intertwiner {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (D : Module.End ℝ V) (D' : Module.End ℝ W)
    (L : V →ₗ[ℝ] W) (h : ∀ v, L (D v) = D' (L v))
    (Q : Polynomial ℝ) (v : V) :
    L ((Polynomial.aeval D Q) v) = (Polynomial.aeval D' Q) (L v) := by
  have hp (n : ℕ) : ∀ v, L ((D ^ n) v) = (D' ^ n) (L v) := by
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', pow_succ']
      change L (D ((D ^ n) v)) = D' ((D' ^ n) (L v))
      rw [h, ih]
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hp]

end Wong.EulerFiniteModule

namespace Wong.SmoothModel

/-- Leibniz rule for the commutator in its second argument. -/
theorem euler_lie_mul (A B C : Operator) :
    ⁅A, B * C⁆ = ⁅A, B⁆ * C + B * ⁅A, C⁆ := by
  apply LinearMap.ext
  intro u
  change A (B (C u)) - B (C (A u)) =
    (A (B (C u)) - B (A (C u))) + B (A (C u) - C (A u))
  rw [map_sub]
  abel

/-- Powers of a true eigenoperator have their expected commutator weight. -/
theorem euler_lie_pow (A B : Operator) (c : ℝ) (h : ⁅A, B⁆ = c • B) (n : ℕ) :
    ⁅A, B ^ n⁆ = ((n : ℝ) * c) • B ^ n := by
  induction n with
  | zero => simp [operator_lie_def]
  | succ n ih =>
    rw [pow_succ, euler_lie_mul, ih, h]
    simp only [smul_mul_assoc, mul_smul_comm, ← add_smul]
    congr 1
    push_cast
    ring

@[simp] theorem hiddenEuler_lie_partial (i : Fin 3) :
    ⁅hiddenEuler, partialDerivative i⁆ =
      (if i = 2 then (-1 : ℝ) else 0) • partialDerivative i := by
  rw [hiddenEuler, operator_lie_mul_left]
  have hp : ⁅partialDerivative 2, partialDerivative i⁆ = 0 := by
    rw [operator_lie_def, partialDerivative_commute 2 i, sub_self]
  rw [hp, mul_zero, zero_add, ← lie_skew (multiplication _) (partialDerivative i),
    lie_partial_multiplication, partialDerivative_linearFunction]
  fin_cases i <;> simp [coordinateVector, multiplication_smoothOne]
  apply LinearMap.ext
  intro u
  rfl

@[simp] theorem hiddenEuler_lie_multiPartial (α : MultiIndex) :
    ⁅hiddenEuler, multiPartial α⁆ = -(α 2 : ℝ) • multiPartial α := by
  have h0 := euler_lie_pow hiddenEuler (partialDerivative 0) 0 (by simp) (α 0)
  have h1 := euler_lie_pow hiddenEuler (partialDerivative 1) 0 (by simp) (α 1)
  have h2 := euler_lie_pow hiddenEuler (partialDerivative 2) (-1) (by simp) (α 2)
  simp only [multiPartial, euler_lie_mul, h0, h1, h2, mul_zero, zero_smul,
    zero_mul, zero_add, mul_smul_comm, mul_neg_one]

@[simp] theorem hiddenEuler_lie_multiplier (u : Smooth) :
    ⁅hiddenEuler, multiplication u⁆ = multiplication (hiddenEuler u) := by
  rw [hiddenEuler, operator_lie_mul_left, lie_partial_multiplication,
    lie_multiplication_multiplication, zero_mul, add_zero]
  exact multiplication_mul _ _

/-- The scalar differential operator occurring at one normal coefficient. -/
def shiftedHiddenEuler (α : MultiIndex) : Operator := hiddenEuler - (α 2 : ℝ) • 1

def normalHiddenEuler : Module.End ℝ NormalForm :=
  Finsupp.lsum ℝ fun α => (Finsupp.lsingle α).comp (shiftedHiddenEuler α)

@[simp] theorem normalHiddenEuler_single (α : MultiIndex) (u : Smooth) :
    normalHiddenEuler (Finsupp.single α u) = Finsupp.single α (shiftedHiddenEuler α u) := by
  simp [normalHiddenEuler]

@[simp] theorem normalHiddenEuler_apply (p : NormalForm) (α : MultiIndex) :
    normalHiddenEuler p α = shiftedHiddenEuler α (p α) := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single β u =>
    by_cases h : β = α
    · subst β; simp
    · simp [Ne.symm h]

/-- Exact coefficient formula for the actual Euler commutator. -/
theorem normalAction_hiddenEuler (p : NormalForm) :
    normalAction (normalHiddenEuler p) = ⁅hiddenEuler, normalAction p⁆ := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq, lie_add]
  | single α u =>
    rw [normalHiddenEuler_single, normalAction_single, normalAction_single,
      euler_lie_mul, hiddenEuler_lie_multiplier, hiddenEuler_lie_multiPartial]
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    change ((hiddenEuler u).1 x - (α 2 : ℝ) * u.1 x) * (multiPartial α v).1 x =
      (hiddenEuler u).1 x * (multiPartial α v).1 x +
        u.1 x * (-(α 2 : ℝ) * (multiPartial α v).1 x)
    ring

/-- A polynomial of the Euler adjoint is a polynomial of each genuine
shifted Euler coefficient operator. -/
theorem euler_annihilator_normal_coefficient (Q : Polynomial ℝ) (p : NormalForm)
    (hQ : (Polynomial.aeval (LieAlgebra.ad ℝ Operator hiddenEuler) Q) (normalAction p) = 0)
    (α : MultiIndex) :
    (Polynomial.aeval (shiftedHiddenEuler α) Q) (p α) = 0 := by
  have hnormal : (Polynomial.aeval normalHiddenEuler Q) p = 0 := by
    apply normalAction_injective
    rw [map_zero]
    have hi := Wong.EulerFiniteModule.aeval_intertwiner normalHiddenEuler
      (LieAlgebra.ad ℝ Operator hiddenEuler) normalAction
      (fun q => normalAction_hiddenEuler q) Q p
    exact hi.trans hQ
  have hc := Wong.EulerFiniteModule.aeval_intertwiner normalHiddenEuler
    (shiftedHiddenEuler α) (Finsupp.lapply α) (fun p => normalHiddenEuler_apply p α) Q p
  rw [hnormal, map_zero] at hc
  exact hc.symm

end Wong.SmoothModel
