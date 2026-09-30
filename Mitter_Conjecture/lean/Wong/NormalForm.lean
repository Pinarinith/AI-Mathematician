import Wong.DirectionalExtraction
import Wong.FiniteSupport
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Faithful smooth differential normal forms

Finite smooth-coefficient normal forms act on the actual global smooth
function space. Their action is injective: exponential test functions turn
any alleged zero operator into a polynomial vanishing at every frequency.
Consequently finite dimensionality of the original operator algebra gives
a uniform bound for any chosen monomial weight on all its normal forms.
-/

noncomputable section
namespace Wong.SmoothModel

abbrev MultiIndex := Fin 3 →₀ ℕ
abbrev NormalForm := MultiIndex →₀ Smooth

def multiPartial (α : MultiIndex) : Operator :=
  partialDerivative 0 ^ α 0 * partialDerivative 1 ^ α 1 * partialDerivative 2 ^ α 2

def normalAction : NormalForm →ₗ[ℝ] Operator :=
  Finsupp.lsum ℝ fun α => (LinearMap.mulRight ℝ (multiPartial α)).comp multiplicationLinear

@[simp] theorem normalAction_single (α : MultiIndex) (u : Smooth) :
    normalAction (Finsupp.single α u) = multiplication u * multiPartial α := by
  simp [normalAction, multiplicationLinear]

def normalCoefficientEvaluation (x : State) : Smooth →ₗ[ℝ] ℝ where
  toFun u := u.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficientsAt (x : State) : NormalForm →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap.comp
    (Finsupp.mapRange.linearMap (normalCoefficientEvaluation x))

@[simp] theorem coefficientsAt_coeff (x : State) (p : NormalForm) (α : MultiIndex) :
    (coefficientsAt x p).coeff α = (p α).1 x := rfl

@[simp] theorem coefficientsAt_single (x : State) (α : MultiIndex) (u : Smooth) :
    coefficientsAt x (Finsupp.single α u) = MvPolynomial.monomial α (u.1 x) := by
  ext β
  simp [coefficientsAt_coeff, MvPolynomial.coeff_monomial, Finsupp.single_apply]
  split_ifs <;> rfl

def exponentialTest (z : State) : Smooth :=
  ⟨fun x => Real.exp ((linearFunction z).1 x), (smooth (linearFunction z)).exp⟩

theorem partialDerivative_exponentialTest (z : State) (i : Fin 3) :
    partialDerivative i (exponentialTest z) = z i • exponentialTest z := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun y => Real.exp ((linearFunction z).1 y)) x (coordinateVector i) =
    z i * Real.exp ((linearFunction z).1 x)
  rw [fderiv_exp (((smooth (linearFunction z)).differentiable (by simp)).differentiableAt)]
  have hi := congrArg (fun u : Smooth => u.1 x) (partialDerivative_linearFunction i z)
  change fderiv ℝ (linearFunction z).1 x (coordinateVector i) = z i * 1 at hi
  change Real.exp ((linearFunction z).1 x) *
    fderiv ℝ (linearFunction z).1 x (coordinateVector i) = _
  rw [hi]
  ring

theorem end_power_eigenvector (A : Operator) (u : Smooth) (c : ℝ)
    (h : A u = c • u) (n : ℕ) : (A ^ n) u = c ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Wong.AdjointIteration.end_pow_succ_apply, ih, map_smul, h, smul_smul, pow_succ]

theorem multiPartial_exponentialTest (α : MultiIndex) (z : State) :
    multiPartial α (exponentialTest z) =
      (z 0 ^ α 0 * z 1 ^ α 1 * z 2 ^ α 2) • exponentialTest z := by
  change (partialDerivative 0 ^ α 0)
    ((partialDerivative 1 ^ α 1) ((partialDerivative 2 ^ α 2) (exponentialTest z))) = _
  rw [end_power_eigenvector _ _ _ (partialDerivative_exponentialTest z 2), map_smul,
    end_power_eigenvector _ _ _ (partialDerivative_exponentialTest z 1), map_smul,
    map_smul, end_power_eigenvector _ _ _ (partialDerivative_exponentialTest z 0)]
  simp only [smul_smul]
  congr 1
  ring

theorem normalAction_exponentialTest (p : NormalForm) (z x : State) :
    (normalAction p (exponentialTest z)).1 x =
      MvPolynomial.eval z (coefficientsAt x p) * Real.exp ((linearFunction z).1 x) := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
      add_mul, hp, hq]
  | single α u =>
    rw [normalAction_single, coefficientsAt_single, MvPolynomial.eval_monomial]
    change (smoothMul u (multiPartial α (exponentialTest z))).1 x = _
    rw [multiPartial_exponentialTest]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [Fin.prod_univ_succ, smoothMul, exponentialTest]
    ring

/-- A smooth-coefficient normal form is zero if it acts as zero on all
globally smooth test functions. No formal-symbol uniqueness is assumed. -/
theorem normalAction_eq_zero_iff (p : NormalForm) : normalAction p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    have hc : ∀ x, coefficientsAt x p = 0 := by
      intro x
      apply MvPolynomial.funext
      intro z
      have he := congrArg (fun A : Operator => (A (exponentialTest z)).1 x) hp
      rw [normalAction_exponentialTest] at he
      change MvPolynomial.eval z (coefficientsAt x p) *
        Real.exp ((linearFunction z).1 x) = 0 at he
      simpa using (mul_eq_zero.mp he).resolve_right (Real.exp_ne_zero _)
    ext α x
    have he := congrArg (fun q : MvPolynomial (Fin 3) ℝ => q.coeff α) (hc x)
    simpa using he
  · rintro rfl
    exact map_zero _

theorem normalAction_injective : Function.Injective normalAction := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply (normalAction_eq_zero_iff _).mp
  rw [map_sub, hpq, sub_self]

/-- Normal forms whose actual actions belong to the supplied operator space. -/
abbrev normalFormsIn (E : Submodule ℝ Operator) : Submodule ℝ NormalForm :=
  E.comap normalAction

def normalFormsIn_action (E : Submodule ℝ Operator) : normalFormsIn E →ₗ[ℝ] E where
  toFun p := ⟨normalAction p.1, p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add normalAction p.1 q.1
  map_smul' c p := by apply Subtype.ext; exact map_smul normalAction c p.1

theorem normalFormsIn_action_injective (E : Submodule ℝ Operator) :
    Function.Injective (normalFormsIn_action E) := by
  intro p q hpq
  apply Subtype.ext
  exact normalAction_injective (congrArg Subtype.val hpq)

/-- The earlier finite-support bound now applies to the actual operators,
even without claiming that every operator in the ambient space is a
differential operator. -/
theorem actual_uniform_normal_weight_bound (E : Submodule ℝ Operator)
    [FiniteDimensional ℝ E] (weight : MultiIndex → ℕ) :
    ∃ N, ∀ p : NormalForm, normalAction p ∈ E →
      ∀ α, N < weight α → p α = 0 := by
  let : Module.Finite ℝ (normalFormsIn E) :=
    Module.Finite.of_injective (normalFormsIn_action E) (normalFormsIn_action_injective E)
  exact Wong.finiteDimensional_uniform_weight_bound (normalFormsIn E) weight

end Wong.SmoothModel
