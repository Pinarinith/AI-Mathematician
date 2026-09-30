import Wong.NormalSymbolsVisibleAlgebra
import Wong.NormalSymbolsPrincipal

/-! Actual Lie-word order growth eliminating the mixed visible slope. -/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

def visibleKinetic : SmoothSymbol :=
  realCoefficient (1/2) * (X 0^2+X 1^2)

theorem symbolCoefficientDerivative_visibleKinetic (i : Fin 3) :
    symbolCoefficientDerivative i visibleKinetic = 0 := by
  simp only [visibleKinetic, symbolCoefficientDerivative_mul,
    symbolCoefficientDerivative_realCoefficient, map_add,
    symbolCoefficientDerivative_X_pow, zero_mul, add_zero, mul_zero]

theorem projectHiddenSymbol_normalL0 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    projectHiddenSymbol (normalSymbol 2 (normalL0 f h)) = visibleKinetic := by
  rw [normalSymbol_normalL0, AlgHom.map_smul_of_tower]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]
  simp [visibleKinetic, realCoefficient, Fin.sum_univ_three]

theorem symbolPoisson_visibleKinetic_quadratic (A G c0 c1 c01 : ℝ) :
    symbolPoisson visibleKinetic (visibleQuadratic A G c0 c1 c01) =
      visibleQuadSymbol 1 (Wong.Visible.visibleSymbols 1 A G 0) := by
  have hhalf : realCoefficient (1/2) * (2 : SmoothSymbol) = 1 := by
    calc
      _ = realCoefficient ((1/2 : ℝ)*2) := by rw [map_mul, map_ofNat]
      _ = 1 := by norm_num
  have hd : pderiv 1 visibleKinetic = (X 1 : SmoothSymbol) := by
    simp only [visibleKinetic, pderiv_mul, pderiv_realCoefficient, zero_mul, zero_add,
      map_add, pderiv_pow, pderiv_X]
    norm_num [Pi.single_apply]
    calc
      _ = (realCoefficient (1/2) * 2) * X 1 := by ring
      _ = _ := by rw [hhalf, one_mul]
  simp only [symbolPoisson, symbolFirstCorrection, symbolCoefficientDerivative_visibleKinetic,
    mul_zero, Finset.sum_const_zero, sub_zero, symbolCoefficientDerivative_visibleQuadratic,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hd]
  simp only [visibleQuadSymbol, Wong.Visible.visibleSymbols, one_mul, map_zero, zero_mul,
    zero_add]
  ring

def visibleNormalWords (l p : NormalForm) : ℕ → NormalForm
  | 0 => normalBracket l p
  | n+1 => normalBracket (visibleNormalWords l p n) p

theorem visibleNormalWords_order (l p : NormalForm)
    (hl : NormalDegreeLE 2 l) (hp : NormalDegreeLE 2 p) (r : ℕ) :
    NormalDegreeLE (r+3) (visibleNormalWords l p r) := by
  induction r with
  | zero =>
    apply normalDegreeLE_of_action_order
    rw [visibleNormalWords, normalAction_bracket]
    exact lie_mem_orderSpace_sharp (action_order_of_normalDegreeLE _ _ hl)
      (action_order_of_normalDegreeLE _ _ hp)
  | succ r ih =>
    apply normalDegreeLE_of_action_order
    rw [visibleNormalWords, normalAction_bracket]
    convert lie_mem_orderSpace_sharp (action_order_of_normalDegreeLE _ _ ih)
      (action_order_of_normalDegreeLE _ _ hp) using 1
    congr 1

theorem visibleNormalWords_projected_symbol {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (p : NormalForm)
    (hp : NormalDegreeLE 2 p) (A G c0 c1 c01 : ℝ)
    (hq : projectHiddenSymbol (normalSymbol 2 p) = visibleQuadratic A G c0 c1 c01)
    (r : ℕ) :
    projectHiddenSymbol (normalSymbol (r+3) (visibleNormalWords (normalL0 f h) p r)) =
      visibleQuadSymbol (r+1) (Wong.Visible.visibleSymbols 1 A G r) := by
  have hl : NormalDegreeLE 2 (normalL0 f h) :=
    normalDegreeLE_of_action_order _ _ (by
      rw [normalAction_normalL0]
      exact L0_mem_orderSpace_two f h)
  have hp3 : symbolCoefficientDerivative 2 (projectHiddenSymbol (normalSymbol 2 p)) = 0 := by
    rw [hq, symbolCoefficientDerivative_visibleQuadratic]
    rfl
  induction r with
  | zero =>
    change projectHiddenSymbol (normalSymbol 3 (normalBracket (normalL0 f h) p)) = _
    rw [normalSymbol_bracket_projectHidden _ _ 1 1 hl hp]
    · rw [projectHiddenSymbol_normalL0, hq]
      exact symbolPoisson_visibleKinetic_quadratic A G c0 c1 c01
    · rw [projectHiddenSymbol_normalL0, symbolCoefficientDerivative_visibleKinetic]
    · exact hp3
  | succ r ih =>
    change projectHiddenSymbol (normalSymbol (r+1+3)
      (normalBracket (visibleNormalWords (normalL0 f h) p r) p)) = _
    have hword := visibleNormalWords_order (normalL0 f h) p hl hp r
    rw [show r+1+3=(r+2)+1+1 by omega,
      normalSymbol_bracket_projectHidden _ _ (r+2) 1 (by simpa only [Nat.add_assoc] using hword) hp]
    · rw [show r+2+1=r+3 by omega, ih, hq, symbolPoisson_quad_visibleQuadratic]
      rfl
    · rw [show r+2+1=r+3 by omega, ih, symbolCoefficientDerivative_visibleQuadSymbol]
    · exact hp3

theorem normalSymbol_eq_zero_above_order (p : NormalForm) (N k : ℕ)
    (hp : NormalDegreeLE N p) (hk : N<k) : normalSymbol k p=0 := by
  apply MvPolynomial.ext
  intro α
  rw [normalSymbol_coeff]
  change (if α.degree=k then p α else 0) = 0
  split_ifs with hα
  · exact hp α (by omega)
  · rfl

/-- A nonzero mixed visible slope produces actual Lie words of arbitrarily
large ordinary order, contradicting finite dimensionality of the original algebra. -/
theorem visible_mixed_slope_zero {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] (p : NormalForm)
    (hpE : normalAction p ∈ estimationAlgebra f h) (hp : NormalDegreeLE 2 p)
    (A G c0 c1 c01 : ℝ)
    (hq : projectHiddenSymbol (normalSymbol 2 p) = visibleQuadratic A G c0 c1 c01) :
    G=0 := by
  by_contra hG
  obtain ⟨N,hN⟩ := estimationAlgebra_uniform_order_bound f h
  have hE (r : ℕ) : normalAction (visibleNormalWords (normalL0 f h) p r) ∈
      estimationAlgebra f h := by
    induction r with
    | zero =>
      rw [visibleNormalWords, normalAction_bracket, normalAction_normalL0]
      exact (estimationAlgebra f h).lie_mem
        (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hpE
    | succ r ih =>
      rw [visibleNormalWords, normalAction_bracket]
      exact (estimationAlgebra f h).lie_mem ih hpE
  have hz := normalSymbol_eq_zero_above_order (visibleNormalWords (normalL0 f h) p N)
    N (N+3) (normalDegreeLE_of_action_order _ _ (hN (hE N))) (by omega)
  have hsym := visibleNormalWords_projected_symbol f h p hp A G c0 c1 c01 hq N
  rw [hz, map_zero] at hsym
  exact visibleQuadSymbol_iterate_ne_zero A G hG N hsym.symm

end Wong.SmoothModel
