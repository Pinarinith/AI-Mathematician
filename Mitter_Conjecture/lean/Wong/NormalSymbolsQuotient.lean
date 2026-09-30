import Wong.NormalSymbolsBracket

/-!
# The hidden-momentum quotient for actual smooth principal symbols

Only the third momentum is set to zero. Coefficients remain actual globally
smooth functions. The precise hypothesis for the bracket quotient is that
the two projected symbols have coefficients independent of the third position.
No polynomiality of arbitrary discarded coefficients is required.
-/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

/-- Set the hidden momentum to zero, fixing all actual smooth coefficients. -/
def projectHiddenSymbol : SmoothSymbol →ₐ[Smooth] SmoothSymbol :=
  aeval fun i : Fin 3 => if i = 2 then 0 else X i

@[simp] theorem projectHiddenSymbol_C (u : Smooth) : projectHiddenSymbol (C u) = C u := by
  simp [projectHiddenSymbol]

@[simp] theorem projectHiddenSymbol_X (i : Fin 3) :
    projectHiddenSymbol (X i) = if i = 2 then 0 else X i := by
  simp [projectHiddenSymbol]

/-- The projection commutes with each actual position derivative. -/
theorem projectHiddenSymbol_coefficientDerivative (p : SmoothSymbol) (i : Fin 3) :
    projectHiddenSymbol (symbolCoefficientDerivative i p) =
      symbolCoefficientDerivative i (projectHiddenSymbol p) := by
  induction p using MvPolynomial.induction_on with
  | C u => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = 2
    · simp [map_mul, symbolCoefficientDerivative_mul, hp, hj]
    · simp [map_mul, symbolCoefficientDerivative_mul, hp, hj]

/-- Every retained momentum derivative commutes with discarding the hidden momentum. -/
theorem projectHiddenSymbol_pderiv (p : SmoothSymbol) (i : Fin 3) (hi : i ≠ 2) :
    projectHiddenSymbol (pderiv i p) = pderiv i (projectHiddenSymbol p) := by
  induction p using MvPolynomial.induction_on with
  | C u => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = 2
    · subst j
      simp [map_mul, hp, Ne.symm hi]
    · by_cases hji : j = i <;> simp [map_mul, hp, hj, hji, hi]

/-- The projected symbol no longer contains the hidden momentum. -/
@[simp] theorem pderiv_hidden_projectHiddenSymbol (p : SmoothSymbol) :
    pderiv 2 (projectHiddenSymbol p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C u => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
    by_cases hj : j = 2
    · simp [map_mul, hj]
    · simp [map_mul, hp, hj]

@[simp] theorem projectHiddenSymbol_idempotent (p : SmoothSymbol) :
    projectHiddenSymbol (projectHiddenSymbol p) = projectHiddenSymbol p := by
  induction p using MvPolynomial.induction_on with
  | C u => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = 2 <;> simp [map_mul, hp, hj]

/-- One Leibniz correction respects the quotient whenever the right input's
projected coefficients are independent of the hidden position. -/
theorem projectHiddenSymbol_firstCorrection (p q : SmoothSymbol)
    (hq : symbolCoefficientDerivative 2 (projectHiddenSymbol q) = 0) :
    projectHiddenSymbol (symbolFirstCorrection p q) =
      symbolFirstCorrection (projectHiddenSymbol p) (projectHiddenSymbol q) := by
  simp only [symbolFirstCorrection, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change projectHiddenSymbol (_ + (_ + (_ + 0))) = _ + (_ + (_ + 0))
  simp only [map_add, map_mul, map_zero, projectHiddenSymbol_coefficientDerivative]
  change projectHiddenSymbol (pderiv 0 p) * symbolCoefficientDerivative 0
    (projectHiddenSymbol q) + (projectHiddenSymbol (pderiv 1 p) *
    symbolCoefficientDerivative 1 (projectHiddenSymbol q) +
    (projectHiddenSymbol (pderiv 2 p) * symbolCoefficientDerivative 2
      (projectHiddenSymbol q) + 0)) = _
  rw [projectHiddenSymbol_pderiv p 0 (by decide),
    projectHiddenSymbol_pderiv p 1 (by decide), hq]
  simp


/-- The genuine smooth-coefficient Poisson quotient: proved, not postulated. -/
theorem projectHiddenSymbol_poisson (p q : SmoothSymbol)
    (hp : symbolCoefficientDerivative 2 (projectHiddenSymbol p) = 0)
    (hq : symbolCoefficientDerivative 2 (projectHiddenSymbol q) = 0) :
    projectHiddenSymbol (symbolPoisson p q) =
      symbolPoisson (projectHiddenSymbol p) (projectHiddenSymbol q) := by
  rw [symbolPoisson, map_sub, projectHiddenSymbol_firstCorrection p q hq,
    projectHiddenSymbol_firstCorrection q p hp]
  rfl

@[simp] theorem projectHiddenSymbol_hidden_mul (p : SmoothSymbol) :
    projectHiddenSymbol (X 2 * p) = 0 := by simp

/-- Arbitrary smooth hidden remainders cannot contaminate the visible Poisson quotient. -/
theorem projectHiddenSymbol_discard_remainders (p q r s : SmoothSymbol)
    (hp : symbolCoefficientDerivative 2 (projectHiddenSymbol p) = 0)
    (hq : symbolCoefficientDerivative 2 (projectHiddenSymbol q) = 0) :
    projectHiddenSymbol (symbolPoisson (p + X 2 * r) (q + X 2 * s)) =
      symbolPoisson (projectHiddenSymbol p) (projectHiddenSymbol q) := by
  rw [projectHiddenSymbol_poisson]
  · simp
  · simpa using hp
  · simpa using hq

/-- Apply the quotient directly to the genuine principal symbol of an actual bracket. -/
theorem normalSymbol_bracket_projectHidden (p q : NormalForm) (m n : ℕ)
    (hp : NormalDegreeLE (m + 1) p) (hq : NormalDegreeLE (n + 1) q)
    (hp₃ : symbolCoefficientDerivative 2 (projectHiddenSymbol (normalSymbol (m + 1) p)) = 0)
    (hq₃ : symbolCoefficientDerivative 2 (projectHiddenSymbol (normalSymbol (n + 1) q)) = 0) :
    projectHiddenSymbol (normalSymbol (m + n + 1) (normalBracket p q)) =
      symbolPoisson (projectHiddenSymbol (normalSymbol (m + 1) p))
        (projectHiddenSymbol (normalSymbol (n + 1) q)) := by
  rw [normalSymbol_bracket p q m n hp hq, projectHiddenSymbol_poisson _ _ hp₃ hq₃]

end Wong.SmoothModel
