import Wong.NormalSymbolsPrincipal
import Wong.NormalSymbolsQuotient
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

theorem normalQuantize_injective : Function.Injective normalQuantize :=
  normalAction_injective.comp normalTotalSymbol.symm.injective

@[simp] theorem normalQuantize_C (u : Smooth) : normalQuantize (C u) = multiplication u := by
  change normalAction (Finsupp.single 0 u) = _
  exact normalAction_scalar u

theorem smoothSymbol_pderiv_commute (p : SmoothSymbol) (i j : Fin 3) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  apply normalQuantize_injective
  rw [normalQuantize_pderiv, normalQuantize_pderiv, normalQuantize_pderiv,
    normalQuantize_pderiv]
  have hh := lie_multiplication_multiplication
    (linearFunction (coordinateVector i)) (linearFunction (coordinateVector j))
  simp only [operator_lie_def, mul_sub, sub_mul, mul_assoc] at hh ⊢
  have hc : multiplication (linearFunction (coordinateVector i)) *
      multiplication (linearFunction (coordinateVector j)) =
      multiplication (linearFunction (coordinateVector j)) *
      multiplication (linearFunction (coordinateVector i)) := sub_eq_zero.mp hh
  have hh₁ := congrArg (fun A : Operator => normalQuantize p * A) hc
  have hh₂ := congrArg (fun A : Operator => A * normalQuantize p) hc
  simp only [mul_assoc] at hh₁ hh₂
  rw [hh₁, hh₂]
  abel

/-- A double actual coordinate commutator determines the corresponding
Hessian entry of the genuine second principal symbol. -/
theorem normalSymbol_two_head (p : NormalForm) (i j : Fin 3) (u : Smooth)
    (hh : ⁅⁅normalAction p, multiplication (linearFunction (coordinateVector j))⁆,
      multiplication (linearFunction (coordinateVector i))⁆ = multiplication u) :
    pderiv i (pderiv j (normalSymbol 2 p)) = C u := by
  have he : pderiv i (pderiv j (normalTotalSymbol p)) = C u := by
    apply normalQuantize_injective
    rw [normalQuantize_pderiv, normalQuantize_pderiv, normalQuantize_totalSymbol,
      normalQuantize_C, hh]
  have he' := congrArg (homogeneousComponent 0) he
  rw [homogeneousComponent_smoothSymbol_pderiv,
    homogeneousComponent_smoothSymbol_pderiv] at he'
  have hC : homogeneousComponent 0 (C u : SmoothSymbol) = C u := by
    apply MvPolynomial.ext
    intro α
    simp only [coeff_homogeneousComponent, coeff_C]
    by_cases ha : α=0
    · subst α; simp
    · simp [Ne.symm ha]
  rw [hC] at he'
  exact he'

/-- Euler's identity, differentiated once, recovers a quadratic symbol
from its Hessian. This avoids any assumed coefficient normal form. -/
theorem smoothSymbol_quadratic_hessian (p : SmoothSymbol) (hp : p.IsHomogeneous 2) :
    (2 : SmoothSymbol) * p =
      ∑i : Fin 3, ∑j : Fin 3, X i * X j * pderiv j (pderiv i p) := by
  have he := hp.sum_X_mul_pderiv
  have hd (i : Fin 3) := hp.pderiv (i:=i) |>.sum_X_mul_pderiv
  norm_num at hd
  calc
    (2 : SmoothSymbol)*p = ∑i : Fin 3,X i*pderiv i p := by
      rw [show (2:ℕ) • p = p+p by exact two_smul ℕ p] at he
      calc
        (2 : SmoothSymbol)*p = p+p := by ring
        _ = _ := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => arg 2; rw [← hd i]
      rw [Finset.mul_sum]
      simp only [mul_assoc]

/-- The three actual visible Hessian entries recover the entire visible
second principal symbol; all coefficients in hidden momentum are discarded. -/
theorem normalSymbol_two_projected_heads (p : NormalForm) (u00 u11 u01 : Smooth)
    (h00 : pderiv 0 (pderiv 0 (normalSymbol 2 p)) = C u00)
    (h11 : pderiv 1 (pderiv 1 (normalSymbol 2 p)) = C u11)
    (h01 : pderiv 0 (pderiv 1 (normalSymbol 2 p)) = C u01) :
    (2 : SmoothSymbol) * projectHiddenSymbol (normalSymbol 2 p) =
      C u00 * X 0^2 + C u11 * X 1^2 + 2 * C u01 * X 0 * X 1 := by
  have hh := congrArg projectHiddenSymbol
    (smoothSymbol_quadratic_hessian (normalSymbol 2 p) (homogeneousComponent_isHomogeneous 2 (normalTotalSymbol p)))
  have h10 : pderiv 1 (pderiv 0 (normalSymbol 2 p)) = C u01 := by
    rw [smoothSymbol_pderiv_commute, h01]
  simp only [map_mul, map_ofNat, map_sum, projectHiddenSymbol_X] at hh
  simp only [Fin.sum_univ_three] at hh
  change (2 : SmoothSymbol) * projectHiddenSymbol (normalSymbol 2 p) = _ at hh
  norm_num only [show (0:Fin 3) ≠ 2 by decide,
    show (1:Fin 3) ≠ 2 by decide, ite_false, ite_true,
    zero_mul, mul_zero, add_zero, zero_add] at hh
  rw [h00, h11, h01, h10] at hh
  simp only [projectHiddenSymbol_C] at hh
  convert hh using 1; ring

end Wong.SmoothModel
