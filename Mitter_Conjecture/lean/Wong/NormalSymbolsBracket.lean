import Wong.NormalSymbolsProduct

/-!
# The genuine principal-symbol Poisson formula

The composition remainder, already attached to actual smooth operators,
proves cancellation of the two top product terms. Ordinary bracket symbols
are therefore the canonical Poisson bracket, with actual coefficient derivatives.
-/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

/-- Canonical Poisson bracket: momentum derivatives precede position derivatives. -/
def symbolPoisson (p q : SmoothSymbol) : SmoothSymbol :=
  symbolFirstCorrection p q - symbolFirstCorrection q p

/-- Total symbol of the actual commutator. -/
def symbolBracket (p q : SmoothSymbol) : SmoothSymbol :=
  symbolCompose p q - symbolCompose q p

theorem symbolBracket_action (p q : SmoothSymbol) :
    normalAction (normalTotalSymbol.symm (symbolBracket p q)) =
      ⁅normalAction (normalTotalSymbol.symm p), normalAction (normalTotalSymbol.symm q)⁆ := by
  rw [symbolBracket, map_sub, map_sub, symbolCompose_action, symbolCompose_action, operator_lie_def]

/-- Only terms with at least two coefficient derivatives remain beyond Poisson order. -/
theorem symbolBracket_sub_poisson_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : SymbolOrderLE m p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE (m + n - 2) (symbolBracket p q - symbolPoisson p q) := by
  have he : symbolBracket p q - symbolPoisson p q =
      symbolCompositionRemainder p q - symbolCompositionRemainder q p := by
    unfold symbolBracket symbolPoisson symbolCompositionRemainder
    ring
  rw [he]
  exact (symbolCompositionRemainder_order p q m n hp hq).sub
    (by simpa only [add_comm n m] using symbolCompositionRemainder_order q p n m hq hp)

theorem symbolPoisson_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : SymbolOrderLE m p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE (m + n - 1) (symbolPoisson p q) := by
  exact (symbolFirstCorrection_order p q m n hp hq).sub
    (by simpa only [add_comm n m] using symbolFirstCorrection_order q p n m hq hp)

/-- The sharp commutator-order bound follows from genuine normal composition. -/
theorem symbolBracket_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : SymbolOrderLE m p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE (m + n - 1) (symbolBracket p q) := by
  have he : symbolBracket p q = symbolPoisson p q +
      (symbolBracket p q - symbolPoisson p q) := by ring
  rw [he]
  exact (symbolPoisson_order p q m n hp hq).add
    ((symbolBracket_sub_poisson_order p q m n hp hq).mono (by omega))

/-- At maximal possible commutative product degree, only the two principal components contribute. -/
theorem smoothSymbol_topComponent_mul (p q : SmoothSymbol) (m n : ℕ)
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) :
    homogeneousComponent (m + n) (p * q) =
      homogeneousComponent m p * homogeneousComponent n q := by
  classical
  apply MvPolynomial.ext
  intro α
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases hα : α.degree = m + n
  · simp only [hα, ite_true]
    apply Finset.sum_congr rfl
    intro ab hab
    have he : ab.1 + ab.2 = α := Finset.mem_antidiagonal.mp hab
    have hdeg : ab.1.degree + ab.2.degree = α.degree := by rw [← map_add, he]
    by_cases ha : p.coeff ab.1 = 0
    · simp [coeff_homogeneousComponent, ha]
    by_cases hb : q.coeff ab.2 = 0
    · simp [coeff_homogeneousComponent, hb]
    have ha' : ab.1.degree ≤ m := (le_totalDegree (mem_support_iff.mpr ha)).trans hp
    have hb' : ab.2.degree ≤ n := (le_totalDegree (mem_support_iff.mpr hb)).trans hq
    have hea : ab.1.degree = m := by omega
    have heb : ab.2.degree = n := by omega
    simp [coeff_homogeneousComponent, hea, heb]
  · simp only [hα, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro ab hab
    have he : ab.1 + ab.2 = α := Finset.mem_antidiagonal.mp hab
    have hdeg : ab.1.degree + ab.2.degree = α.degree := by rw [← map_add, he]
    simp only [coeff_homogeneousComponent]
    split_ifs <;> simp_all

theorem homogeneousComponent_smoothSymbol_pderiv (p : SmoothSymbol) (i : Fin 3) (n : ℕ) :
    homogeneousComponent n (pderiv i p) = pderiv i (homogeneousComponent (n + 1) p) := by
  classical
  apply MvPolynomial.ext
  intro α
  simp [coeff_homogeneousComponent, coeff_pderiv, map_add, Finsupp.degree_single]

theorem symbolFirstCorrection_principal (p q : SmoothSymbol) (m n : ℕ)
    (hp : SymbolOrderLE ((m + 1 : ℕ) : ℤ) p)
    (hq : SymbolOrderLE ((n + 1 : ℕ) : ℤ) q) :
    homogeneousComponent (m + n + 1) (symbolFirstCorrection p q) =
      symbolFirstCorrection (homogeneousComponent (m + 1) p)
        (homogeneousComponent (n + 1) q) := by
  simp only [symbolFirstCorrection, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hpd : SymbolOrderLE (m : ℤ) (pderiv i p) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hp.pderiv i
  rw [show m + n + 1 = m + (n + 1) by omega,
    smoothSymbol_topComponent_mul _ _ m (n + 1)
      ((symbolOrderLE_nat_iff _ _).mp hpd)
      ((symbolOrderLE_nat_iff _ _).mp (hq.coefficientDerivative i)),
    homogeneousComponent_smoothSymbol_pderiv, homogeneousComponent_symbolCoefficientDerivative]

theorem symbolPoisson_principal (p q : SmoothSymbol) (m n : ℕ)
    (hp : SymbolOrderLE ((m + 1 : ℕ) : ℤ) p)
    (hq : SymbolOrderLE ((n + 1 : ℕ) : ℤ) q) :
    homogeneousComponent (m + n + 1) (symbolPoisson p q) =
      symbolPoisson (homogeneousComponent (m + 1) p)
        (homogeneousComponent (n + 1) q) := by
  rw [symbolPoisson, map_sub, symbolFirstCorrection_principal p q m n hp hq]
  have hh := symbolFirstCorrection_principal q p n m hq hp
  rw [Nat.add_comm n m] at hh
  rw [hh]
  rfl

/-- Principal symbols of actual positive-order commutators obey the canonical Poisson rule. -/
theorem symbolBracket_principal (p q : SmoothSymbol) (m n : ℕ)
    (hp : SymbolOrderLE ((m + 1 : ℕ) : ℤ) p)
    (hq : SymbolOrderLE ((n + 1 : ℕ) : ℤ) q) :
    homogeneousComponent (m + n + 1) (symbolBracket p q) =
      symbolPoisson (homogeneousComponent (m + 1) p)
        (homogeneousComponent (n + 1) q) := by
  have hh := symbolBracket_sub_poisson_order p q _ _ hp hq
  have hh' : SymbolOrderLE (((m + n + 1 : ℕ) : ℤ) - 1)
      (symbolBracket p q - symbolPoisson p q) := by
    convert hh using 1; push_cast; ring
  rw [homogeneousComponent_eq_of_order_sub _ _ _ hh']
  exact symbolPoisson_principal p q m n hp hq

/-- Conversion back to the normal forms whose actions are the actual smooth operators. -/
theorem normalSymbol_bracket (p q : NormalForm) (m n : ℕ)
    (hp : NormalDegreeLE (m + 1) p) (hq : NormalDegreeLE (n + 1) q) :
    normalSymbol (m + n + 1) (normalBracket p q) =
      symbolPoisson (normalSymbol (m + 1) p) (normalSymbol (n + 1) q) := by
  have hp' := (symbolOrderLE_nat_iff (m + 1) (normalTotalSymbol p)).mpr
    ((normalDegreeLE_iff _ _).mp hp)
  have hq' := (symbolOrderLE_nat_iff (n + 1) (normalTotalSymbol q)).mpr
    ((normalDegreeLE_iff _ _).mp hq)
  have he : symbolBracket (normalTotalSymbol p) (normalTotalSymbol q) =
      normalTotalSymbol (normalBracket p q) := by
    simp only [symbolBracket, symbolCompose, LinearEquiv.symm_apply_apply,
      normalBracket, map_sub]
  simpa only [he, normalSymbol] using
    symbolBracket_principal (normalTotalSymbol p) (normalTotalSymbol q) m n hp' hq'

end Wong.SmoothModel
