import Wong.FunctionElements
import Mathlib.Algebra.Polynomial.Module.Basic

/-!
# Extracting the parameter-linear coefficient in a commuting operator pencil

The coefficients are actual smooth functions. Vanishing at every real value
of the parameter forces each coefficient to vanish, proved by pointwise real
polynomial evaluation. No topology on the infinite-dimensional smooth space
is assumed.
-/

noncomputable section
namespace Wong.SmoothModel

abbrev SmoothPolynomial := PolynomialModule ℝ Smooth

def smoothEvaluation (x : State) : Smooth →ₗ[ℝ] ℝ where
  toFun u := u.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def scalarizeSmoothPolynomial (p : SmoothPolynomial) (x : State) : Polynomial ℝ :=
  PolynomialModule.equivPolynomial (PolynomialModule.map ℝ (smoothEvaluation x) p)

@[simp] theorem coeff_scalarizeSmoothPolynomial (p : SmoothPolynomial) (x : State) (n : ℕ) :
    (scalarizeSmoothPolynomial p x).coeff n = (p.coeff n).1 x := rfl

theorem eval_scalarizeSmoothPolynomial (p : SmoothPolynomial) (x : State) (t : ℝ) :
    (scalarizeSmoothPolynomial p x).eval t = (PolynomialModule.eval t p).1 x := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp [scalarizeSmoothPolynomial]
  | add p q hp hq =>
    simpa only [scalarizeSmoothPolynomial, map_add, Polynomial.eval_add,
      Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) hp hq
  | single n u =>
    simp [scalarizeSmoothPolynomial, PolynomialModule.eval_single, smoothEvaluation,
      mul_comm]

/-- Polynomial dependence with smooth coefficients is faithful on real parameters. -/
theorem smoothPolynomial_eq_zero_of_eval (p : SmoothPolynomial)
    (hp : ∀ t : ℝ, PolynomialModule.eval t p = 0) : p = 0 := by
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro n
  apply Subtype.ext
  funext x
  have hzero : scalarizeSmoothPolynomial p x = 0 := by
    apply Polynomial.funext
    intro t
    rw [eval_scalarizeSmoothPolynomial, hp]
    simp
  have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff n) hzero
  exact hcoeff

/-- Polynomial with value `(P+tQ)^n(a+tb)`. -/
def operatorPencilPolynomial (P Q : Operator) (a b : Smooth) : ℕ → SmoothPolynomial
  | 0 => PolynomialModule.single ℝ 0 a + PolynomialModule.single ℝ 1 b
  | n + 1 => PolynomialModule.map ℝ P (operatorPencilPolynomial P Q a b n) +
      (Polynomial.X : Polynomial ℝ) • PolynomialModule.map ℝ Q (operatorPencilPolynomial P Q a b n)

theorem operatorPencilPolynomial_eval (P Q : Operator) (a b : Smooth) (n : ℕ) (t : ℝ) :
    PolynomialModule.eval t (operatorPencilPolynomial P Q a b n) =
      ((P + t • Q) ^ n) (a + t • b) := by
  induction n with
  | zero => simp [operatorPencilPolynomial, PolynomialModule.eval_single]
  | succ n ih =>
    simp only [operatorPencilPolynomial, map_add, PolynomialModule.eval_map',
      PolynomialModule.eval_smul, Polynomial.eval_X, ih]
    rw [pow_succ']
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_add]
    abel

@[simp] theorem coeff_map_smoothPolynomial (A : Operator) (p : SmoothPolynomial) (n : ℕ) :
    (PolynomialModule.map ℝ A p).coeff n = A (p.coeff n) := rfl

@[simp] theorem coeff_X_smul_smoothPolynomial_zero (p : SmoothPolynomial) :
    ((Polynomial.X : Polynomial ℝ) • p).coeff 0 = 0 := by
  rw [← Polynomial.monomial_one_one_eq_X, PolynomialModule.monomial_smul_apply]
  simp

@[simp] theorem coeff_X_smul_smoothPolynomial_one (p : SmoothPolynomial) :
    ((Polynomial.X : Polynomial ℝ) • p).coeff 1 = p.coeff 0 := by
  rw [← Polynomial.monomial_one_one_eq_X, PolynomialModule.monomial_smul_apply]
  simp

theorem operatorPencilPolynomial_coeff_zero (P Q : Operator) (a b : Smooth) (n : ℕ) :
    (operatorPencilPolynomial P Q a b n).coeff 0 = (P ^ n) a := by
  induction n with
  | zero => simp [operatorPencilPolynomial]
  | succ n ih =>
    simp only [operatorPencilPolynomial, PolynomialModule.coeff_add, Finsupp.add_apply,
      coeff_map_smoothPolynomial, coeff_X_smul_smoothPolynomial_zero, add_zero, ih]
    rw [pow_succ']
    rfl

theorem operatorPencilPolynomial_coeff_one_succ (P Q : Operator) (a b : Smooth) (n : ℕ) :
    (operatorPencilPolynomial P Q a b (n + 1)).coeff 1 =
      P ((operatorPencilPolynomial P Q a b n).coeff 1) + Q ((P ^ n) a) := by
  simp only [operatorPencilPolynomial, PolynomialModule.coeff_add, Finsupp.add_apply,
    coeff_map_smoothPolynomial, coeff_X_smul_smoothPolynomial_one,
    operatorPencilPolynomial_coeff_zero]

/-- Applying P to the linear parameter coefficient avoids division and the
exceptional exponent n−1. -/
theorem apply_operatorPencilPolynomial_coeff_one (P Q : Operator) (hPQ : Commute P Q)
    (a b : Smooth) (n : ℕ) :
    P ((operatorPencilPolynomial P Q a b n).coeff 1) =
      (P ^ (n + 1)) b + n • Q ((P ^ n) a) := by
  have hcomm (u : Smooth) : P (Q u) = Q (P u) :=
    congrArg (fun A : Operator => A u) hPQ.eq
  induction n with
  | zero => simp [operatorPencilPolynomial]
  | succ n ih =>
    rw [operatorPencilPolynomial_coeff_one_succ, map_add, ih, map_add, map_nsmul,
      hcomm]
    simp only [← Module.End.mul_apply, ← pow_succ']
    rw [add_assoc, ← succ_nsmul]

/-- If the whole operator pencil vanishes for every real parameter, its
linear coefficient forces one extra P-derivative of b to vanish. -/
theorem operatorPencil_nilpotent_coefficient (P Q : Operator) (hPQ : Commute P Q)
    (a b : Smooth) (n : ℕ)
    (hvan : ∀ t : ℝ, ((P + t • Q) ^ n) (a + t • b) = 0) :
    (P ^ (n + 1)) b = 0 := by
  have hp : operatorPencilPolynomial P Q a b n = 0 :=
    smoothPolynomial_eq_zero_of_eval _ (fun t =>
      (operatorPencilPolynomial_eval P Q a b n t).trans (hvan t))
  have ha : (P ^ n) a = 0 := by
    rw [← operatorPencilPolynomial_coeff_zero, hp]
    rfl
  have h1 := apply_operatorPencilPolynomial_coeff_one P Q hPQ a b n
  simpa only [hp, PolynomialModule.coeff_zero, Finsupp.zero_apply, map_zero, ha,
    nsmul_zero, add_zero] using h1.symm

end Wong.SmoothModel
