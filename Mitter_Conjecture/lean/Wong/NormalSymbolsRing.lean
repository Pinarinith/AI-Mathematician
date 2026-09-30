import Wong.NormalFormAlgebra
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Actual pointwise ring structure on the existing global smooth function space.
No quotient or symbolic substitute for `Smooth` is introduced. -/

noncomputable section
namespace Wong.SmoothModel

instance smoothOneInstance : One Smooth := ⟨smoothOne⟩
instance smoothMulInstance : Mul Smooth := ⟨smoothMul⟩
instance smoothNatCast : NatCast Smooth := ⟨fun n => (n : ℝ) • smoothOne⟩
instance smoothIntCast : IntCast Smooth := ⟨fun n => (n : ℝ) • smoothOne⟩
instance smoothPow : Pow Smooth ℕ :=
  ⟨fun u n => ⟨fun x => u.1 x ^ n, (smooth u).pow n⟩⟩

instance smoothCommRing : CommRing Smooth :=
  Function.Injective.commRing (fun u : Smooth => u.1) Subtype.val_injective
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun n => by funext x; change (n : ℝ) * 1 = (n : ℝ); exact mul_one _)
    (fun n => by funext x; change (n : ℝ) * 1 = (n : ℝ); exact mul_one _)

instance smoothAlgebra : Algebra ℝ Smooth :=
  Algebra.ofModule (fun r u v => by
    apply Subtype.ext; funext x; exact mul_assoc r (u.1 x) (v.1 x))
    (fun r u v => by
      apply Subtype.ext; funext x; exact mul_left_comm (u.1 x) r (v.1 x))

@[simp] theorem smooth_coe_one (x : State) : (1 : Smooth).1 x = 1 := rfl
@[simp] theorem smooth_coe_mul (u v : Smooth) (x : State) : (u * v).1 x = u.1 x * v.1 x := rfl
@[simp] theorem smooth_coe_pow (u : Smooth) (n : ℕ) (x : State) : (u ^ n).1 x = u.1 x ^ n := rfl
@[simp] theorem smoothMul_eq_mul (u v : Smooth) : smoothMul u v = u * v := rfl
@[simp] theorem smoothOne_eq_one : smoothOne = (1 : Smooth) := rfl

/-- A coordinate derivative is a derivation of the real algebra of actual smooth functions. -/
def smoothPartialDerivation (i : Fin 3) : Derivation ℝ Smooth Smooth where
  toLinearMap := partialDerivative i
  map_one_eq_zero' := by simpa using partialDerivative_const i 1
  leibniz' u v := by
    change partialDerivative i (smoothMul u v) = _
    rw [partialDerivative_smoothMul]
    change (partialDerivative i u) * v + u * (partialDerivative i v) =
      u * (partialDerivative i v) + v * (partialDerivative i u)
    ring

@[simp] theorem smoothPartialDerivation_apply (i : Fin 3) (u : Smooth) :
    smoothPartialDerivation i u = partialDerivative i u := rfl

/-- Evaluation is a ring homomorphism of the actual smooth coefficient ring. -/
def smoothEvalRing (x : State) : Smooth →+* ℝ where
  toFun u := u.1 x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

abbrev SmoothSymbol := MvPolynomial (Fin 3) Smooth

/-- The ordinary total symbol, retaining all orders, is a faithful linear repackaging. -/
def normalTotalSymbol : NormalForm ≃ₗ[ℝ] SmoothSymbol :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm

@[simp] theorem normalTotalSymbol_coeff (p : NormalForm) (α : MultiIndex) :
    (normalTotalSymbol p).coeff α = p α := rfl

@[simp] theorem normalTotalSymbol_single (α : MultiIndex) (u : Smooth) :
    normalTotalSymbol (Finsupp.single α u) = MvPolynomial.monomial α u := rfl

/-- Evaluating the smooth coefficients gives the previously proved actual symbol test. -/
theorem normalTotalSymbol_eval_coefficients (p : NormalForm) (x : State) :
    MvPolynomial.map (smoothEvalRing x) (normalTotalSymbol p) = coefficientsAt x p := by
  ext α
  rw [MvPolynomial.coeff_map]
  rfl

/-- An ordinary homogeneous principal component, defined even when it vanishes. -/
def normalSymbol (n : ℕ) (p : NormalForm) : SmoothSymbol :=
  MvPolynomial.homogeneousComponent n (normalTotalSymbol p)

@[simp] theorem normalSymbol_coeff (n : ℕ) (p : NormalForm) (α : MultiIndex) :
    (normalSymbol n p).coeff α = if α.degree = n then p α else 0 := by
  simp [normalSymbol, MvPolynomial.coeff_homogeneousComponent]

end Wong.SmoothModel
