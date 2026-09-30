import Wong.SectorTwoDerivation
import Wong.WeightedSymbolsOrder
import Wong.EulerFalling
import Wong.EulerFunctionSpace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Derivation.Lie

/-!
# Faithful sector-II polynomial symbols in the actual smooth symbol space

The four variables are sent to real coordinate functions and actual momentum
variables. Weighted nonvanishing is proved from the actual hidden Euler
equation and the proved falling-factorial differential identity.
-/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial
set_option maxHeartbeats 1800000

def sectorTwoSymbolLift : Wong.SectorTwo.Symbols →ₐ[ℝ] SmoothSymbol :=
  aeval ![C (linearFunction (coordinateVector 0)),
    C (linearFunction (coordinateVector 2)), X 0, X 2]

theorem sectorTwoSymbolLift_C (c : ℝ) :
    sectorTwoSymbolLift (C c) = C (c • smoothOne) := by
  rw [sectorTwoSymbolLift, aeval_C, Algebra.algebraMap_eq_smul_one]
  rw [show (1 : SmoothSymbol) = C smoothOne from (map_one C).symm]
  simp only [C_apply, smul_monomial]

theorem sectorTwoSymbolLift_X (i : Fin 4) :
    sectorTwoSymbolLift (X i) =
      ![C (linearFunction (coordinateVector 0)),
        C (linearFunction (coordinateVector 2)), X 0, X 2] i := by
  simp [sectorTwoSymbolLift]

theorem sectorTwoSymbolLift_eval (p : Wong.SectorTwo.Symbols) (x z : State) :
    eval₂ (smoothEvalRing x) z (sectorTwoSymbolLift p) = eval ![x 0, x 2, z 0, z 2] p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [sectorTwoSymbolLift_C, eval₂_C, eval_C]
    change c * 1 = c
    ring
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, eval₂_mul, eval_mul, hp, sectorTwoSymbolLift_X]
    congr 1
    fin_cases i <;>
      simp [smoothEvalRing, linearFunction, coordinateVector, Fin.sum_univ_three] <;> rfl

theorem sectorTwoSymbolLift_injective : Function.Injective sectorTwoSymbolLift := by
  intro p q hpq
  apply MvPolynomial.funext
  intro y
  have he := congrArg (eval₂ (smoothEvalRing ![y 0, 0, y 1]) ![y 2, 0, y 3]) hpq
  have hy : ![y 0, y 1, y 2, y 3] = y := by
    funext i
    fin_cases i <;> rfl
  rw [sectorTwoSymbolLift_eval, sectorTwoSymbolLift_eval] at he
  change eval ![y 0, y 1, y 2, y 3] p = eval ![y 0, y 1, y 2, y 3] q at he
  simpa only [hy] using he

def normalWeightedEuler : Module.End ℝ NormalForm :=
  Finsupp.lsum ℝ fun α => (Finsupp.lsingle α).comp
    (hiddenEuler + (momentumWeight α : ℝ) • (1 : Operator))

@[simp] theorem normalWeightedEuler_single (α : MultiIndex) (u : Smooth) :
    normalWeightedEuler (Finsupp.single α u) =
      Finsupp.single α (hiddenEuler u + (momentumWeight α : ℝ) • u) := by
  simp [normalWeightedEuler]

@[simp] theorem normalWeightedEuler_apply (p : NormalForm) (α : MultiIndex) :
    normalWeightedEuler p α = hiddenEuler (p α) + (momentumWeight α : ℝ) • p α := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq, smul_add]; abel
  | single β u =>
    by_cases he : β = α
    · subst β; simp
    · simp [Ne.symm he]

def weightedSymbolEuler : Module.End ℝ SmoothSymbol :=
  normalTotalSymbol.toLinearMap.comp (normalWeightedEuler.comp normalTotalSymbol.symm.toLinearMap)

@[simp] theorem weightedSymbolEuler_coeff (p : SmoothSymbol) (α : MultiIndex) :
    (weightedSymbolEuler p).coeff α =
      hiddenEuler (p.coeff α) + (momentumWeight α : ℝ) • p.coeff α := by
  exact normalWeightedEuler_apply (normalTotalSymbol.symm p) α

@[simp] theorem weightedSymbolEuler_monomial (α : MultiIndex) (u : Smooth) :
    weightedSymbolEuler (monomial α u) =
      monomial α (hiddenEuler u + (momentumWeight α : ℝ) • u) := by
  change normalTotalSymbol (normalWeightedEuler (Finsupp.single α u)) = _
  rw [normalWeightedEuler_single, normalTotalSymbol_single]

theorem sectorTwo_hiddenEuler_mul (u v : Smooth) :
    hiddenEuler (u * v) = hiddenEuler u * v + u * hiddenEuler v := by
  change smoothMul (linearFunction (coordinateVector 2))
    (partialDerivative 2 (smoothMul u v)) = _
  rw [partialDerivative_smoothMul]
  change (linearFunction (coordinateVector 2)) *
    ((partialDerivative 2 u) * v + u * partialDerivative 2 v) =
      ((linearFunction (coordinateVector 2)) * partialDerivative 2 u) * v +
        u * ((linearFunction (coordinateVector 2)) * partialDerivative 2 v)
  ring

theorem weightedSymbolEuler_mul (p q : SmoothSymbol) :
    weightedSymbolEuler (p * q) = weightedSymbolEuler p * q + p * weightedSymbolEuler q := by
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [add_mul, map_add, hp, hr]; ring
  | monomial α u =>
    induction q using MvPolynomial.induction_on' with
    | add q r hq hr => simp only [mul_add, map_add, hq, hr]; ring
    | monomial β v =>
      simp only [monomial_mul_monomial, weightedSymbolEuler_monomial, momentumWeight_add,
        Nat.cast_add, ← map_add]
      congr 1
      rw [sectorTwo_hiddenEuler_mul]
      apply Subtype.ext
      funext x
      simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_smul, Pi.smul_apply,
        smooth_coe_mul, smul_eq_mul]
      ring

@[simp] theorem weightedSymbolEuler_C (u : Smooth) :
    weightedSymbolEuler (C u) = C (hiddenEuler u) := by
  simpa only [C_apply, momentumWeight_zero, Nat.cast_zero, zero_smul, add_zero] using
    weightedSymbolEuler_monomial 0 u

theorem sectorTwo_hiddenEuler_real_constant (c : ℝ) : hiddenEuler (c • smoothOne) = 0 := by
  change multiplication _ (partialDerivative 2 (c • smoothOne)) = 0
  rw [partialDerivative_const, map_zero]

@[simp] theorem weightedSymbolEuler_X (i : Fin 3) :
    weightedSymbolEuler (X i) = (momentumCoordinateWeight i : ℝ) • (X i : SmoothSymbol) := by
  have hone : hiddenEuler (1 : Smooth) = 0 := by
    simpa using sectorTwo_hiddenEuler_real_constant 1
  simp only [MvPolynomial.X, weightedSymbolEuler_monomial, hone, zero_add,
    momentumWeight_single, mul_one, momentumCoordinateWeight, smul_monomial]

theorem eulerFallingPolynomial_eval_nat_ne_zero (n : ℕ) :
    (eulerFallingPolynomial n).eval (n : ℝ) ≠ 0 := by
  classical
  simp only [eulerFallingPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  exact_mod_cast Nat.ne_of_gt (Finset.mem_range.mp hj)

theorem hiddenEuler_eigen_zero_of_strict_degree (r : ℤ) (u : Smooth)
    (hdegree : HiddenDegreeLE (r - 1) u) (heigen : hiddenEuler u = (r : ℝ) • u) : u = 0 := by
  by_cases hr : 0 ≤ r
  · let n := r.toNat
    have hn : (n : ℤ) = r := Int.toNat_of_nonneg hr
    have hnil : (partialDerivative 2 ^ n) u = 0 := hdegree n (by omega)
    have hpoly := eulerFallingPolynomial_annihilates n u hnil
    have hrn : (r : ℝ) = (n : ℝ) := by exact_mod_cast hn.symm
    have he : hiddenEuler u = (n : ℝ) • u := by
      simpa only [hrn] using heigen
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul he] at hpoly
    exact (smul_eq_zero.mp hpoly).resolve_left (eulerFallingPolynomial_eval_nat_ne_zero n)
  · exact hdegree.eq_zero_of_neg (by omega)

theorem weightedSymbolEuler_eigen_zero_of_lower_bound (n : ℤ) (p : SmoothSymbol)
    (heigen : weightedSymbolEuler p = (n : ℝ) • p)
    (hbound : WeightedSymbolOrderLE (n - 1) p) : p = 0 := by
  apply MvPolynomial.ext
  intro α
  rw [AddMonoidAlgebra.coeff_zero]
  have he := congrArg (fun q : SmoothSymbol => q.coeff α) heigen
  simp only [weightedSymbolEuler_coeff, coeff_smul] at he
  apply hiddenEuler_eigen_zero_of_strict_degree (n - (momentumWeight α : ℤ)) (p.coeff α)
  · convert hbound α using 1; omega
  · rw [Int.cast_sub, Int.cast_natCast]
    rw [sub_smul]
    exact eq_sub_iff_add_eq.mpr he

theorem hiddenEuler_eigen_hiddenDegreeLE (r : ℤ) (u : Smooth)
    (heigen : hiddenEuler u = (r : ℝ) • u) : HiddenDegreeLE r u := by
  intro k hk
  have hc : 0 < (k : ℝ) - (r : ℝ) := by exact_mod_cast sub_pos.mpr hk
  apply positive_hiddenEuler_shift_kernel ((k : ℝ) - r) hc
  have he := congrArg (fun A : Operator => A u) (hidden_partial_shift k)
  change (partialDerivative 2 ^ k) (hiddenEuler u - (k : ℝ) • u) =
    hiddenEuler ((partialDerivative 2 ^ k) u) at he
  rw [heigen, map_sub, map_smul, map_smul] at he
  change hiddenEuler ((partialDerivative 2 ^ k) u) +
    ((k : ℝ) - r) • (partialDerivative 2 ^ k) u = 0
  rw [← he, sub_smul]
  module

theorem weightedSymbolEuler_eigen_order (n : ℤ) (p : SmoothSymbol)
    (heigen : weightedSymbolEuler p = (n : ℝ) • p) : WeightedSymbolOrderLE n p := by
  intro α
  have he := congrArg (fun q : SmoothSymbol => q.coeff α) heigen
  simp only [weightedSymbolEuler_coeff, coeff_smul] at he
  apply hiddenEuler_eigen_hiddenDegreeLE
  rw [Int.cast_sub, Int.cast_natCast, sub_smul]
  exact eq_sub_iff_add_eq.mpr he

end Wong.SmoothModel

namespace Wong.SectorTwo
open MvPolynomial
set_option maxHeartbeats 1800000

def weightedEuler : Derivation ℝ Symbols Symbols :=
  mkDerivation ℝ ![0, X 1, X 2, (2 : ℝ) • X 3]

theorem weightedEuler_lie_dynamics (a k : ℝ) :
    ⁅weightedEuler, dynamics a k⁆ = dynamics a k := by
  apply derivation_ext
  intro i
  fin_cases i <;>
    simp [weightedEuler, dynamics, Derivation.commutator_apply, Derivation.leibniz,
      Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, derivation_C] <;>
      (try simp only [two_smul]) <;> ring

theorem weightedEuler_dynamics (a k : ℝ) (p : Symbols) :
    weightedEuler (dynamics a k p) = dynamics a k (weightedEuler p) + dynamics a k p := by
  have he := congrArg (fun D : Derivation ℝ Symbols Symbols => D p)
    (weightedEuler_lie_dynamics a k)
  rw [Derivation.commutator_apply] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem weightedEuler_momentum_iterate (a k : ℝ) (n : ℕ) :
    weightedEuler ((dynamics a k)^[n] (X 2)) =
      (n + 1 : ℝ) • ((dynamics a k)^[n] (X 2)) := by
  induction n with
  | zero => simp [weightedEuler]
  | succ n ih =>
    rw [Function.iterate_succ_apply', weightedEuler_dynamics, ih, Derivation.map_smul]
    simp only [Nat.cast_add, Nat.cast_one]
    module

end Wong.SectorTwo

namespace Wong.SmoothModel
open MvPolynomial

theorem sectorTwo_hiddenEuler_linear_coordinate (i : Fin 3) :
    hiddenEuler (linearFunction (coordinateVector i)) =
      if i = 2 then linearFunction (coordinateVector 2) else 0 := by
  fin_cases i <;>
    simp [hiddenEuler, Module.End.mul_apply, partialDerivative_linearFunction, coordinateVector,
      multiplication, smoothMul, smoothOne] <;> rfl

theorem sectorTwoSymbolLift_intertwines (p : Wong.SectorTwo.Symbols) :
    weightedSymbolEuler (sectorTwoSymbolLift p) = sectorTwoSymbolLift (Wong.SectorTwo.weightedEuler p) := by
  have hX (i : Fin 4) :
      weightedSymbolEuler (sectorTwoSymbolLift (X i)) =
        sectorTwoSymbolLift (Wong.SectorTwo.weightedEuler (X i)) := by
    fin_cases i <;>
      simp [sectorTwoSymbolLift_X, Wong.SectorTwo.weightedEuler,
        sectorTwo_hiddenEuler_linear_coordinate, momentumCoordinateWeight]
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [sectorTwoSymbolLift_C, weightedSymbolEuler_C, sectorTwo_hiddenEuler_real_constant,
      derivation_C, map_zero, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, weightedSymbolEuler_mul, hp, hX, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    ring

theorem sectorTwoSymbolLift_momentum_eigen (a k : ℝ) (n : ℕ) :
    weightedSymbolEuler (sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[n] (X 2))) =
      (n + 1 : ℝ) • sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[n] (X 2)) := by
  rw [sectorTwoSymbolLift_intertwines, Wong.SectorTwo.weightedEuler_momentum_iterate, map_smul]

theorem sectorTwoSymbolLift_momentum_order (a k : ℝ) (n : ℕ) :
    WeightedSymbolOrderLE (n + 1)
      (sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[n] (X 2))) := by
  apply weightedSymbolEuler_eigen_order
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using sectorTwoSymbolLift_momentum_eigen a k n

theorem sectorTwoSymbolLift_momentum_not_lower (a k : ℝ) (hk : k ≠ 0) (n : ℕ) :
    ¬ WeightedSymbolOrderLE n
      (sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[n] (X 2))) := by
  intro hbound
  have hz := weightedSymbolEuler_eigen_zero_of_lower_bound (n + 1)
    (sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[n] (X 2)))
    (by simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
      sectorTwoSymbolLift_momentum_eigen a k n)
    (by simpa only [add_sub_cancel_right] using hbound)
  have he : (Wong.SectorTwo.dynamics a k)^[n] (X 2) = 0 := by
    apply sectorTwoSymbolLift_injective
    simpa only [map_zero] using hz
  exact Wong.SectorTwo.momentum_iterates_nonzero a k hk n he

end Wong.SmoothModel
