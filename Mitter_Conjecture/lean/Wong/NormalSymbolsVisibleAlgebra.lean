import Wong.NormalSymbolsQuotient
import Wong.Visible

/-! Exact constant-coefficient recurrence in the visible momentum plane,
inside the genuine smooth coefficient symbol ring. -/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

def realCoefficient : ℝ →+* SmoothSymbol := C.comp (algebraMap ℝ Smooth)

theorem realCoefficient_apply (c : ℝ) :
    realCoefficient c = C (c • smoothOne) := by
  simp [realCoefficient, Algebra.algebraMap_eq_smul_one]

@[simp] theorem symbolCoefficientDerivative_realCoefficient (i : Fin 3) (c : ℝ) :
    symbolCoefficientDerivative i (realCoefficient c) = 0 := by
  rw [realCoefficient_apply, symbolCoefficientDerivative_C, partialDerivative_const, map_zero]

@[simp] theorem pderiv_realCoefficient (i : Fin 3) (c : ℝ) :
    pderiv i (realCoefficient c) = 0 := by rw [realCoefficient_apply, pderiv_C]

@[simp] theorem symbolCoefficientDerivative_X_pow (i j : Fin 3) (n : ℕ) :
    symbolCoefficientDerivative i ((X j : SmoothSymbol)^n) = 0 := by
  induction n with
  | zero =>
    have hh := symbolCoefficientDerivative_realCoefficient i 1
    simpa only [map_one, pow_zero] using hh
  | succ n ih => simp only [pow_succ, symbolCoefficientDerivative_mul, ih,
      symbolCoefficientDerivative_X, zero_mul, mul_zero, add_zero]

/-- Three slots in an ordinary homogeneous visible symbol, with no division. -/
def visibleQuadSymbol (n : ℕ) (q : Wong.Visible.Quad) : SmoothSymbol :=
  realCoefficient q.c₀ * X 0^(n+2) +
  realCoefficient q.c₁ * X 0^(n+1) * X 1 +
  realCoefficient q.c₂ * X 0^n * X 1^2

@[simp] theorem symbolCoefficientDerivative_visibleQuadSymbol
    (i : Fin 3) (n : ℕ) (q : Wong.Visible.Quad) :
    symbolCoefficientDerivative i (visibleQuadSymbol n q) = 0 := by
  simp only [visibleQuadSymbol, map_add, symbolCoefficientDerivative_mul,
    symbolCoefficientDerivative_realCoefficient, symbolCoefficientDerivative_X_pow,
    symbolCoefficientDerivative_X, zero_mul, mul_zero, add_zero]

/-- The constant two-momentum recurrence, now embedded in the actual coefficient ring. -/
theorem visibleQuadSymbol_step (A G : ℝ) (n : ℕ) (q : Wong.Visible.Quad) :
    visibleQuadSymbol (n+1) (q.step 1 A G) =
      pderiv 1 (visibleQuadSymbol n q) *
        (realCoefficient A * X 0^2 + realCoefficient G * X 0 * X 1) := by
  simp only [visibleQuadSymbol, Wong.Visible.Quad.step, one_mul,
    map_add, map_mul, pderiv_mul, pderiv_pow, pderiv_X, pderiv_realCoefficient]
  norm_num [Pi.single_apply]
  simp only [pow_succ, map_ofNat]
  ring

/-- Restrict smooth coefficients to the origin and set ξ₀=1, ξ₁=z. -/
def visibleSymbolTest : SmoothSymbol →+* Polynomial ℝ :=
  eval₂Hom (Polynomial.C.comp (smoothEvalRing 0))
    (fun i : Fin 3 => if i=1 then Polynomial.X else 1)

@[simp] theorem visibleSymbolTest_realCoefficient (c : ℝ) :
    visibleSymbolTest (realCoefficient c) = Polynomial.C c := by
  rw [realCoefficient_apply]
  simp only [visibleSymbolTest, eval₂Hom_C, RingHom.comp_apply]
  congr 1
  change c * 1 = c
  ring

@[simp] theorem visibleSymbolTest_X (i : Fin 3) :
    visibleSymbolTest (X i) = if i=1 then Polynomial.X else 1 := by
  simp [visibleSymbolTest]

theorem visibleSymbolTest_quad (n : ℕ) (q : Wong.Visible.Quad) :
    visibleSymbolTest (visibleQuadSymbol n q) = q.poly := by
  simp [visibleQuadSymbol, Wong.Visible.Quad.poly]

/-- No actual smooth-symbol iterate vanishes when the mixed slope is nonzero. -/
theorem visibleQuadSymbol_iterate_ne_zero (A G : ℝ) (hG : G ≠ 0) (r : ℕ) :
    visibleQuadSymbol (r+1) (Wong.Visible.visibleSymbols 1 A G r) ≠ 0 := by
  intro hh
  have ht := congrArg visibleSymbolTest hh
  rw [visibleSymbolTest_quad, map_zero] at ht
  exact Wong.Visible.visibleSymbols_poly_ne_zero 1 A G one_ne_zero hG r ht

/-- The second-order visible symbol whose mixed slope is eliminated by order growth. -/
def visibleQuadratic (A G c0 c1 c01 : ℝ) : SmoothSymbol :=
  C (A • linearFunction (coordinateVector 1) + c0 • smoothOne) * X 0^2 +
  realCoefficient c1 * X 1^2 +
  C (G • linearFunction (coordinateVector 1) + c01 • smoothOne) * X 0 * X 1

theorem symbolCoefficientDerivative_visibleQuadratic (i : Fin 3)
    (A G c0 c1 c01 : ℝ) :
    symbolCoefficientDerivative i (visibleQuadratic A G c0 c1 c01) =
      if i=1 then realCoefficient A * X 0^2 + realCoefficient G * X 0 * X 1 else 0 := by
  have hone (j : Fin 3) : partialDerivative j smoothOne = 0 := by
    simpa only [one_smul] using partialDerivative_const j 1
  simp only [visibleQuadratic, map_add, symbolCoefficientDerivative_mul,
    symbolCoefficientDerivative_C, symbolCoefficientDerivative_X_pow,
    symbolCoefficientDerivative_X, symbolCoefficientDerivative_realCoefficient,
    map_smul, hone, partialDerivative_linearFunction,
    smul_zero, add_zero, mul_zero, zero_mul]
  by_cases hi : i=1
  · subst i
    simp [coordinateVector, realCoefficient_apply]
  · simp [coordinateVector, hi]

theorem symbolPoisson_quad_visibleQuadratic (n : ℕ) (q : Wong.Visible.Quad)
    (A G c0 c1 c01 : ℝ) :
    symbolPoisson (visibleQuadSymbol n q) (visibleQuadratic A G c0 c1 c01) =
      visibleQuadSymbol (n+1) (q.step 1 A G) := by
  simp only [symbolPoisson, symbolFirstCorrection,
    symbolCoefficientDerivative_visibleQuadSymbol, mul_zero, Finset.sum_const_zero,
    sub_zero, symbolCoefficientDerivative_visibleQuadratic, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact (visibleQuadSymbol_step A G n q).symm

end Wong.SmoothModel
