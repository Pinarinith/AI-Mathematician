import Wong.NormalSymbolsBracket
import Wong.NormalSymbolsOrderBridge

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

theorem symbolCompose_sub_mul_order (p q : SmoothSymbol) (m n : ℤ)
    (hp : SymbolOrderLE m p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE (m + n - 1) (symbolCompose p q - p * q) := by
  have he : symbolCompose p q - p * q = symbolFirstCorrection p q +
      symbolCompositionRemainder p q := by unfold symbolCompositionRemainder; ring
  rw [he]
  exact (symbolFirstCorrection_order p q m n hp hq).add
    ((symbolCompositionRemainder_order p q m n hp hq).mono (by omega))

theorem symbolCompose_principal (p q : SmoothSymbol) (m n : ℕ)
    (hp : SymbolOrderLE (m : ℤ) p) (hq : SymbolOrderLE (n : ℤ) q) :
    homogeneousComponent (m + n) (symbolCompose p q) =
      homogeneousComponent m p * homogeneousComponent n q := by
  have hh : SymbolOrderLE (((m+n : ℕ) : ℤ)-1) (symbolCompose p q-p*q) := by
    simpa using symbolCompose_sub_mul_order p q m n hp hq
  rw [homogeneousComponent_eq_of_order_sub _ _ _ hh]
  exact smoothSymbol_topComponent_mul p q m n
    ((symbolOrderLE_nat_iff _ _).mp hp) ((symbolOrderLE_nat_iff _ _).mp hq)

theorem normalSymbol_compose (p q : NormalForm) (m n : ℕ)
    (hp : NormalDegreeLE m p) (hq : NormalDegreeLE n q) :
    normalSymbol (m+n) (normalCompose p q) = normalSymbol m p * normalSymbol n q := by
  have hp' := (symbolOrderLE_nat_iff m (normalTotalSymbol p)).mpr
    ((normalDegreeLE_iff _ _).mp hp)
  have hq' := (symbolOrderLE_nat_iff n (normalTotalSymbol q)).mpr
    ((normalDegreeLE_iff _ _).mp hq)
  simpa only [symbolCompose, LinearEquiv.symm_apply_apply, normalSymbol] using
    symbolCompose_principal (normalTotalSymbol p) (normalTotalSymbol q) m n hp' hq'

@[simp] theorem normalSymbol_add (n : ℕ) (p q : NormalForm) :
    normalSymbol n (p+q) = normalSymbol n p + normalSymbol n q := by
  simp [normalSymbol]

@[simp] theorem normalSymbol_sub (n : ℕ) (p q : NormalForm) :
    normalSymbol n (p-q) = normalSymbol n p - normalSymbol n q := by
  simp [normalSymbol]

@[simp] theorem normalSymbol_smul (n : ℕ) (c : ℝ) (p : NormalForm) :
    normalSymbol n (c • p) = c • normalSymbol n p := by
  classical
  apply MvPolynomial.ext
  intro α
  simp only [normalSymbol_coeff, Finsupp.smul_apply, coeff_smul]
  split_ifs <;> simp

@[simp] theorem normalSymbol_sum {ι : Type*} (s : Finset ι) (p : ι → NormalForm) (n : ℕ) :
    normalSymbol n (∑i∈s,p i) = ∑i∈s,normalSymbol n (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normalSymbol]
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

@[simp] theorem normalSymbol_single (n : ℕ) (α : MultiIndex) (u : Smooth) :
    normalSymbol n (Finsupp.single α u) = if α.degree=n then monomial α u else 0 := by
  rw [normalSymbol, normalTotalSymbol_single]
  apply MvPolynomial.ext
  intro β
  simp only [coeff_homogeneousComponent, coeff_monomial]
  by_cases h : α=β
  · subst β; split_ifs <;> simp_all
  · split_ifs <;> simp_all

@[simp] theorem normalSymbol_normalD (f : Fin 3 → Smooth) (i : Fin 3) :
    normalSymbol 1 (normalD f i) = X i := by
  simp [normalD, Finsupp.degree_single, smoothOne_eq_one, X]

/-- The principal symbol of the actual diffusion generator is Euclidean kinetic energy. -/
theorem normalSymbol_normalL0 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    normalSymbol 2 (normalL0 f h) = (1/2 : ℝ) • ∑i : Fin 3, (X i : SmoothSymbol)^2 := by
  have hd (i : Fin 3) : NormalDegreeLE 1 (normalD f i) :=
    normalDegreeLE_of_action_order _ _ (by
      rw [normalAction_normalD]
      exact D_mem_orderSpace_one f i)
  simp only [normalL0, normalSymbol_sub, normalSymbol_smul, normalSymbol_sum]
  have hc (i : Fin 3) : normalSymbol 2 (normalCompose (normalD f i) (normalD f i)) =
      (X i : SmoothSymbol)^2 := by
    rw [show 2=1+1 from rfl, normalSymbol_compose _ _ 1 1 (hd i) (hd i), normalSymbol_normalD]
    ring
  simp only [hc, normalSymbol_single, map_zero, show ¬(0:ℕ)=2 by decide,
    ite_false, smul_zero, sub_zero]

end Wong.SmoothModel
