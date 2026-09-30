import Wong.DirectionalExtraction
import Wong.PolynomialGradient
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Real multivariate polynomials as actual globally smooth functions

The evaluation embedding is constructed and proved injective. Its algebraic
partial derivatives agree with the already-defined genuine smooth partial
operators, so polynomial degree arguments can be transported to the actual
estimation algebra without assuming a symbolic representation theorem.
-/

noncomputable section
namespace Wong.SmoothModel
open scoped ContDiff

abbrev RealPoly := MvPolynomial (Fin 3) ℝ

/-- Evaluation of a real multivariate polynomial is globally smooth. -/
theorem contDiff_mvPolynomial_eval (p : RealPoly) :
    ContDiff ℝ ∞ (fun x : State => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiff_const (c := c))
  | add p q hp hq =>
    simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp =>
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    apply hp.mul
    exact (ContinuousLinearMap.proj i : State →L[ℝ] ℝ).contDiff

/-- The faithful evaluation embedding into the real smooth function space. -/
def polynomialSmooth (p : RealPoly) : Smooth :=
  ⟨fun x => MvPolynomial.eval x p, contDiff_mvPolynomial_eval p⟩

@[simp] theorem polynomialSmooth_apply (p : RealPoly) (x : State) :
    (polynomialSmooth p).1 x = MvPolynomial.eval x p := rfl

@[simp] theorem polynomialSmooth_zero : polynomialSmooth 0 = 0 := by
  apply Subtype.ext
  funext x
  exact map_zero (MvPolynomial.eval x)

@[simp] theorem polynomialSmooth_add (p q : RealPoly) :
    polynomialSmooth (p + q) = polynomialSmooth p + polynomialSmooth q := by
  apply Subtype.ext
  funext x
  exact map_add (MvPolynomial.eval x) p q

@[simp] theorem polynomialSmooth_mul (p q : RealPoly) :
    polynomialSmooth (p * q) = smoothMul (polynomialSmooth p) (polynomialSmooth q) := by
  apply Subtype.ext
  funext x
  exact map_mul (MvPolynomial.eval x) p q

@[simp] theorem polynomialSmooth_C (c : ℝ) :
    polynomialSmooth (MvPolynomial.C c) = c • smoothOne := by
  apply Subtype.ext
  funext x
  simp [polynomialSmooth, smoothOne]

@[simp] theorem polynomialSmooth_one : polynomialSmooth 1 = smoothOne := by
  simpa only [map_one, one_smul] using polynomialSmooth_C 1

@[simp] theorem polynomialSmooth_smul (c : ℝ) (p : RealPoly) :
    polynomialSmooth (c • p) = c • polynomialSmooth p := by
  apply Subtype.ext
  funext x
  simp [polynomialSmooth, MvPolynomial.smul_eq_C_mul]

/-- The evaluation embedding as an actual linear map. -/
def polynomialSmoothLinear : RealPoly →ₗ[ℝ] Smooth where
  toFun := polynomialSmooth
  map_add' := polynomialSmooth_add
  map_smul' := polynomialSmooth_smul

@[simp] theorem polynomialSmooth_sum {ι : Type*} [Fintype ι] (p : ι → RealPoly) :
    polynomialSmooth (∑ i, p i) = ∑ i, polynomialSmooth (p i) :=
  map_sum polynomialSmoothLinear p Finset.univ

/-- Real polynomial functions have unique polynomial representatives. -/
theorem polynomialSmooth_injective : Function.Injective polynomialSmooth := by
  intro p q hpq
  apply MvPolynomial.funext
  intro x
  exact congrArg (fun u : Smooth => u.1 x) hpq

/-- The smooth derivative of a coordinate polynomial is its algebraic
    partial derivative. -/
theorem partialDerivative_polynomialSmooth_X (i j : Fin 3) :
    partialDerivative i (polynomialSmooth (MvPolynomial.X j)) =
      polynomialSmooth (MvPolynomial.pderiv i (MvPolynomial.X j)) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun y : State => MvPolynomial.eval y (MvPolynomial.X j)) x
    (coordinateVector i) = MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.X j))
  simp only [MvPolynomial.eval_X]
  change fderiv ℝ (ContinuousLinearMap.proj j : State →L[ℝ] ℝ) x (coordinateVector i) = _
  rw [ContinuousLinearMap.fderiv]
  simp [coordinateVector, MvPolynomial.pderiv_X, Pi.single_apply]

/-- Genuine smooth partial differentiation agrees with formal polynomial
    partial differentiation at every order, starting with this exact identity. -/
theorem partialDerivative_polynomialSmooth (i : Fin 3) (p : RealPoly) :
    partialDerivative i (polynomialSmooth p) = polynomialSmooth (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [polynomialSmooth_C, partialDerivative_const, MvPolynomial.pderiv_C,
      polynomialSmooth_zero]
  | add p q hp hq => simp only [polynomialSmooth_add, map_add, hp, hq]
  | mul_X p j hp =>
    simp only [MvPolynomial.pderiv_mul, polynomialSmooth_mul,
      partialDerivative_smoothMul, hp, partialDerivative_polynomialSmooth_X,
      polynomialSmooth_add]

/-- Composition with multiplier embedding gives a linear embedding into the
    actual smooth operator algebra. -/
def polynomialMultiplicationLinear : RealPoly →ₗ[ℝ] Operator :=
  multiplicationLinear.comp polynomialSmoothLinear

theorem polynomialMultiplicationLinear_injective :
    Function.Injective polynomialMultiplicationLinear :=
  multiplication_injective.comp polynomialSmooth_injective

/-- The polynomial squared gradient is precisely the smooth carré-du-champ
    expression appearing in the double filtering commutator. -/
theorem polynomialSmooth_gradientSquare (p : RealPoly) :
    polynomialSmooth (Wong.PolynomialGradient.gradientSquare p) =
      ∑ i, smoothMul (partialDerivative i (polynomialSmooth p))
        (partialDerivative i (polynomialSmooth p)) := by
  rw [Wong.PolynomialGradient.gradientSquare, polynomialSmooth_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_two, polynomialSmooth_mul, ← partialDerivative_polynomialSmooth]

/-- The exact double commutator transports to the formal squared gradient. -/
theorem double_lie_L0_polynomialSmooth {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (p : RealPoly) :
    ⁅⁅L0 f h, multiplication (polynomialSmooth p)⁆, multiplication (polynomialSmooth p)⁆ =
      multiplication (polynomialSmooth (Wong.PolynomialGradient.gradientSquare p)) := by
  rw [double_lie_L0_multiplication, polynomialSmooth_gradientSquare]

/-- The actual polynomial function elements, defined as a preimage subspace
    under the faithful evaluation-multiplier embedding. -/
def polynomialFunctionElements {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    Submodule ℝ RealPoly :=
  (estimationAlgebra f h).toSubmodule.comap polynomialMultiplicationLinear

/-- Squared-gradient closure is proved inside the actual estimation algebra. -/
theorem polynomialFunctionElements_gradient_closed {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) {p : RealPoly} (hp : p ∈ polynomialFunctionElements f h) :
    Wong.PolynomialGradient.gradientSquare p ∈ polynomialFunctionElements f h := by
  change multiplication (polynomialSmooth (Wong.PolynomialGradient.gradientSquare p)) ∈
    estimationAlgebra f h
  rw [← double_lie_L0_polynomialSmooth f h p]
  have hL : L0 f h ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  exact (estimationAlgebra f h).lie_mem ((estimationAlgebra f h).lie_mem hL hp) hp

end Wong.SmoothModel
