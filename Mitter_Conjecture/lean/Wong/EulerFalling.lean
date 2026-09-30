import Wong.EulerNormalCoefficients

/-!
# Integer spectral annihilators from genuine hidden derivative nilpotence

The falling Euler identity is proved as an identity of actual operators,
using the real Weyl commutator; it is not a symbolic-model assumption.
-/
noncomputable section
namespace Wong.SmoothModel
set_option maxHeartbeats 1000000

open Polynomial

def eulerFallingPolynomial (n : ℕ) : Polynomial ℝ :=
  ∏ k ∈ Finset.range n, (X - C (k : ℝ))

theorem hidden_partial_shift (n : ℕ) :
    partialDerivative 2 ^ n * (hiddenEuler - (n : ℝ) • 1) =
      hiddenEuler * partialDerivative 2 ^ n := by
  have hl := euler_lie_pow hiddenEuler (partialDerivative 2) (-1) (by simp) n
  apply LinearMap.ext
  intro u
  have hu := congrArg (fun A : Operator => A u) hl
  change hiddenEuler ((partialDerivative 2 ^ n) u) -
    (partialDerivative 2 ^ n) (hiddenEuler u) = ((n : ℝ) * -1) • (partialDerivative 2 ^ n) u at hu
  change (partialDerivative 2 ^ n) (hiddenEuler u - (n : ℝ) • u) = _
  rw [map_sub, map_smul]
  apply Subtype.ext
  funext x
  have hx := congrArg (fun z : Smooth => z.1 x) hu
  change (hiddenEuler ((partialDerivative 2 ^ n) u)).1 x -
    ((partialDerivative 2 ^ n) (hiddenEuler u)).1 x =
      ((n : ℝ) * -1) * ((partialDerivative 2 ^ n) u).1 x at hx
  change ((partialDerivative 2 ^ n) (hiddenEuler u)).1 x -
    (n : ℝ) * ((partialDerivative 2 ^ n) u).1 x =
      (hiddenEuler ((partialDerivative 2 ^ n) u)).1 x
  linarith

/-- The falling factorial of x3∂3 equals x3^n∂3^n, as actual smooth operators. -/
theorem eulerFallingPolynomial_aeval (n : ℕ) :
    aeval hiddenEuler (eulerFallingPolynomial n) =
      multiplication (linearFunction (coordinateVector 2)) ^ n * partialDerivative 2 ^ n := by
  induction n with
  | zero => simp [eulerFallingPolynomial]
  | succ n ih =>
    rw [eulerFallingPolynomial, Finset.prod_range_succ, map_mul]
    change aeval hiddenEuler (eulerFallingPolynomial n) * aeval hiddenEuler (X - C (n : ℝ)) = _
    rw [ih]
    have hfac : aeval hiddenEuler (X - C (n : ℝ)) = hiddenEuler - (n : ℝ) • 1 := by
      simp [Algebra.smul_def]
    rw [hfac, mul_assoc, hidden_partial_shift]
    simp only [hiddenEuler, pow_succ (multiplication (linearFunction (coordinateVector 2))),
      pow_succ' (partialDerivative 2), mul_assoc]

theorem eulerFallingPolynomial_annihilates (n : ℕ) (u : Smooth)
    (hu : (partialDerivative 2 ^ n) u = 0) :
    (aeval hiddenEuler (eulerFallingPolynomial n)) u = 0 := by
  rw [eulerFallingPolynomial_aeval, Module.End.mul_apply, hu, map_zero]

/-- The block belonging to hidden derivative exponent q. -/
def eulerWeightBlock (n q : ℕ) : Polynomial ℝ :=
  ∏ k ∈ Finset.range n, (X - C ((k : ℝ) - q))

theorem eulerWeightBlock_eq_comp (n q : ℕ) :
    eulerWeightBlock n q = (eulerFallingPolynomial n).comp (X + C (q : ℝ)) := by
  simp only [eulerWeightBlock, eulerFallingPolynomial, Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
  ring

theorem eulerWeightBlock_annihilates (n : ℕ) (α : MultiIndex) (u : Smooth)
    (hu : (partialDerivative 2 ^ n) u = 0) :
    (aeval (shiftedHiddenEuler α) (eulerWeightBlock n (α 2))) u = 0 := by
  rw [eulerWeightBlock_eq_comp, Polynomial.aeval_comp]
  have he : aeval (shiftedHiddenEuler α) (X + C (α 2 : ℝ)) = hiddenEuler := by
    simp [shiftedHiddenEuler, Algebra.smul_def]
  rw [he]
  exact eulerFallingPolynomial_annihilates n u hu

/-- A finite integer set containing every coefficient weight when the
hidden coefficient degree is below n and the hidden derivative order at most q. -/
def normalEulerWeights (n q : ℕ) : Finset ℤ :=
  ((Finset.range n) ×ˢ (Finset.range (q + 1))).image fun z => (z.1 : ℤ) - z.2

def integerWeightPolynomial (s : Finset ℤ) : Polynomial ℝ :=
  ∏ w ∈ s, (X - C (w : ℝ))

theorem eulerWeightBlock_dvd_integerWeightPolynomial (n q r : ℕ) (hr : r ≤ q) :
    eulerWeightBlock n r ∣ integerWeightPolynomial (normalEulerWeights n q) := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    apply isUnit_iff_ne_zero.mpr
    apply sub_ne_zero.mpr
    intro he
    apply hij
    have hijreal : (i : ℝ) = j := by linarith
    exact_mod_cast hijreal
  · intro k hk
    have hw : (k : ℤ) - r ∈ normalEulerWeights n q := by
      apply Finset.mem_image.mpr
      refine ⟨(k, r), Finset.mem_product.mpr ⟨hk, Finset.mem_range.mpr (by omega)⟩, rfl⟩
    have hd := Finset.dvd_prod_of_mem (fun w : ℤ => (X - C (w : ℝ) : Polynomial ℝ)) hw
    simpa only [integerWeightPolynomial, Int.cast_sub, Int.cast_natCast] using hd

/-- Hidden polynomial coefficients give a squarefree polynomial of the
actual Euler adjoint, with finitely many distinct integer roots. -/
theorem normalEuler_integer_annihilator (p : NormalForm) (n : ℕ)
    (hp : ∀ α, (partialDerivative 2 ^ n) (p α) = 0) :
    ∃ s : Finset ℤ,
      (aeval (LieAlgebra.ad ℝ Operator hiddenEuler) (integerWeightPolynomial s))
        (normalAction p) = 0 := by
  classical
  let q := p.support.sup (fun α => α 2)
  let s := normalEulerWeights n q
  refine ⟨s, ?_⟩
  have hcoeff (α : MultiIndex) : (aeval (shiftedHiddenEuler α) (integerWeightPolynomial s)) (p α) = 0 := by
    by_cases hα : α ∈ p.support
    · have hr : α 2 ≤ q := Finset.le_sup (f := fun β : MultiIndex => β 2) hα
      have hd := eulerWeightBlock_dvd_integerWeightPolynomial n q (α 2) hr
      have hz := eulerWeightBlock_annihilates n α (p α) (hp α)
      have he := Wong.EulerAlgebra.aeval_apply_eq_of_dvd_sub (shiftedHiddenEuler α)
        (integerWeightPolynomial s) 0 (eulerWeightBlock n (α 2)) (p α) hz
        (by simpa only [sub_zero, s] using hd)
      simpa using he
    · rw [Finsupp.notMem_support_iff.mp hα, map_zero]
  have hn : (aeval normalHiddenEuler (integerWeightPolynomial s)) p = 0 := by
    apply Finsupp.ext
    intro α
    have he := Wong.EulerFiniteModule.aeval_intertwiner normalHiddenEuler
      (shiftedHiddenEuler α) (Finsupp.lapply α) (fun p => normalHiddenEuler_apply p α)
      (integerWeightPolynomial s) p
    simpa only [Finsupp.lapply_apply, hcoeff, Finsupp.zero_apply] using he
  have he := Wong.EulerFiniteModule.aeval_intertwiner normalHiddenEuler
    (LieAlgebra.ad ℝ Operator hiddenEuler) normalAction
    (fun p => normalAction_hiddenEuler p) (integerWeightPolynomial s) p
  rw [hn, map_zero] at he
  exact he.symm

/-- A prescribed bound on the hidden derivative index gives the precise
finite weight interval, independently of the visible derivative orders. -/
theorem normalEuler_integer_annihilator_with_bound (p : NormalForm) (n q : ℕ)
    (hp : ∀ α, (partialDerivative 2 ^ n) (p α) = 0)
    (hq : ∀ α, q < α 2 → p α = 0) :
    (aeval (LieAlgebra.ad ℝ Operator hiddenEuler)
      (integerWeightPolynomial (normalEulerWeights n q))) (normalAction p) = 0 := by
  let s := normalEulerWeights n q
  have hcoeff (α : MultiIndex) : (aeval (shiftedHiddenEuler α) (integerWeightPolynomial s)) (p α) = 0 := by
    by_cases hα : α 2 ≤ q
    · have hd := eulerWeightBlock_dvd_integerWeightPolynomial n q (α 2) hα
      have hz := eulerWeightBlock_annihilates n α (p α) (hp α)
      have he := Wong.EulerAlgebra.aeval_apply_eq_of_dvd_sub (shiftedHiddenEuler α)
        (integerWeightPolynomial s) 0 (eulerWeightBlock n (α 2)) (p α) hz
        (by simpa only [sub_zero, s] using hd)
      simpa using he
    · rw [hq α (by omega), map_zero]
  have hn : (aeval normalHiddenEuler (integerWeightPolynomial s)) p = 0 := by
    apply Finsupp.ext
    intro α
    have he := Wong.EulerFiniteModule.aeval_intertwiner normalHiddenEuler
      (shiftedHiddenEuler α) (Finsupp.lapply α) (fun p => normalHiddenEuler_apply p α)
      (integerWeightPolynomial s) p
    simpa only [Finsupp.lapply_apply, hcoeff, Finsupp.zero_apply] using he
  have he := Wong.EulerFiniteModule.aeval_intertwiner normalHiddenEuler
    (LieAlgebra.ad ℝ Operator hiddenEuler) normalAction
    (fun p => normalAction_hiddenEuler p) (integerWeightPolynomial s) p
  rw [hn, map_zero] at he
  exact he.symm

theorem normalEulerWeights_lower_bound (n q : ℕ) (w : ℤ)
    (hw : w ∈ normalEulerWeights n q) : -(q : ℤ) ≤ w := by
  obtain ⟨⟨k, r⟩, hkr, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hk, hr⟩ := Finset.mem_product.mp hkr
  have hrq : r < q + 1 := Finset.mem_range.mp hr
  dsimp
  omega

end Wong.SmoothModel
