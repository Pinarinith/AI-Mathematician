import Wong.WeightedNormalOrder

/-! Weighted symbol bounds on genuine smooth coefficients, measured by the
actual hidden derivative. The visible coefficients retain weight zero. -/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

def momentumCoordinateWeight (i : Fin 3) : ℕ := if i=2 then 2 else 1
def positionDerivativeWeight (i : Fin 3) : ℕ := if i=2 then 1 else 0

/-- Exact derivative-nilpotence filtration, after faithful symbol repackaging. -/
def WeightedSymbolOrderLE (n : ℤ) (p : SmoothSymbol) : Prop :=
  ∀ α, HiddenDegreeLE (n-(momentumWeight α:ℤ)) (p.coeff α)

namespace HiddenDegreeLE

theorem nsmul {n : ℤ} {u : Smooth} (hu : HiddenDegreeLE n u) (c : ℕ) :
    HiddenDegreeLE n (c • u) := by
  intro k hk
  rw [map_nsmul, hu k hk, smul_zero]

theorem sum {ι : Type*} (s : Finset ι) (u : ι → Smooth) (n : ℤ)
    (hu : ∀i∈s,HiddenDegreeLE n (u i)) : HiddenDegreeLE n (∑i∈s,u i) := by
  intro k hk
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => hu i hi k hk)

end HiddenDegreeLE

namespace WeightedSymbolOrderLE

theorem zero (n : ℤ) : WeightedSymbolOrderLE n 0 := by
  intro α; rw [AddMonoidAlgebra.coeff_zero]; exact HiddenDegreeLE.zero _

theorem mono {m n : ℤ} {p : SmoothSymbol} (hp : WeightedSymbolOrderLE m p) (hmn : m≤n) :
    WeightedSymbolOrderLE n p := by intro α; exact (hp α).mono (by omega)

theorem add {n : ℤ} {p q : SmoothSymbol}
    (hp : WeightedSymbolOrderLE n p) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE n (p+q) := by
  intro α; rw [AddMonoidAlgebra.coeff_add]; exact (hp α).add (hq α)


theorem smul {n : ℤ} {p : SmoothSymbol} (hp : WeightedSymbolOrderLE n p) (c : ℝ) :
    WeightedSymbolOrderLE n (c • p) := by
  intro α
  rw [coeff_smul]
  exact (hp α).smul c

theorem neg {n : ℤ} {p : SmoothSymbol} (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE n (-p) := by
  intro α; rw [coeff_neg]; exact (hp α).neg

theorem sub {n : ℤ} {p q : SmoothSymbol}
    (hp : WeightedSymbolOrderLE n p) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE n (p-q) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem sum {ι : Type*} (s : Finset ι) (p : ι → SmoothSymbol) (n : ℤ)
    (hp : ∀i∈s,WeightedSymbolOrderLE n (p i)) : WeightedSymbolOrderLE n (∑i∈s,p i) := by
  intro α
  rw [coeff_sum]
  exact HiddenDegreeLE.sum s _ _ (fun i hi => hp i hi α)

theorem mul {m n : ℤ} {p q : SmoothSymbol}
    (hp : WeightedSymbolOrderLE m p) (hq : WeightedSymbolOrderLE n q) :
    WeightedSymbolOrderLE (m+n) (p*q) := by
  classical
  intro α
  rw [coeff_mul]
  apply HiddenDegreeLE.sum
  intro ab hab
  have he := Finset.mem_antidiagonal.mp hab
  have hw : momentumWeight ab.1+momentumWeight ab.2=momentumWeight α := by
    rw [← momentumWeight_add, he]
  have hh := (hp ab.1).mul (hq ab.2)
  convert hh using 1; omega

theorem monomial {k : ℤ} (α : MultiIndex) (u : Smooth) (hu : HiddenDegreeLE k u) :
    WeightedSymbolOrderLE (k+momentumWeight α) (MvPolynomial.monomial α u) := by
  classical
  intro β
  rw [coeff_monomial]
  by_cases h : α=β
  · subst β
    simpa only [ite_true, add_sub_cancel_right] using hu
  · simp only [h, ite_false]
    exact HiddenDegreeLE.zero _

theorem C {k : ℤ} (u : Smooth) (hu : HiddenDegreeLE k u) :
    WeightedSymbolOrderLE k (MvPolynomial.C u) := by
  simpa only [momentumWeight_zero, Nat.cast_zero, add_zero, C_apply] using monomial 0 u hu

theorem X (i : Fin 3) :
    WeightedSymbolOrderLE (momentumCoordinateWeight i) (MvPolynomial.X i : SmoothSymbol) := by
  have ho : HiddenDegreeLE 0 smoothOne := by
    simpa only [one_smul] using HiddenDegreeLE.constant 1
  have hh := monomial (Finsupp.single i 1) smoothOne ho
  simpa only [one_smul, zero_add, momentumWeight_single, mul_one,
    momentumCoordinateWeight, MvPolynomial.X, smoothOne_eq_one] using hh

theorem coefficientDerivative {n : ℤ} {p : SmoothSymbol} (hp : WeightedSymbolOrderLE n p)
    (i : Fin 3) : WeightedSymbolOrderLE (n-positionDerivativeWeight i)
      (symbolCoefficientDerivative i p) := by
  intro α
  rw [symbolCoefficientDerivative_coeff]
  by_cases hi : i=2
  · subst i
    have hh := (hp α).hiddenDerivative
    convert hh using 1
    simp only [positionDerivativeWeight, ite_true]
    omega
  · simpa only [positionDerivativeWeight, hi, ite_false, Nat.cast_zero, sub_zero] using
      (hp α).coordinateDerivative i

theorem pderiv {n : ℤ} {p : SmoothSymbol} (hp : WeightedSymbolOrderLE n p)
    (i : Fin 3) : WeightedSymbolOrderLE (n-momentumCoordinateWeight i) (MvPolynomial.pderiv i p) := by
  intro α
  rw [coeff_pderiv]
  have he : p.coeff (α+Finsupp.single i 1) * ((α i:Smooth)+1) =
      (α i+1) • p.coeff (α+Finsupp.single i 1) := by
    simp [Nat.cast_add, mul_comm]
  rw [he]
  have hh := (hp (α+Finsupp.single i 1)).nsmul (α i+1)
  convert hh using 1
  simp only [momentumWeight_add, momentumWeight_single, mul_one, momentumCoordinateWeight,
    Nat.cast_add]
  omega

end WeightedSymbolOrderLE

theorem weightedSymbolOrderLE_iff_normal (n : ℤ) (p : NormalForm) :
    WeightedSymbolOrderLE n (normalTotalSymbol p) ↔ p ∈ weightedNormalSpace n := Iff.rfl

theorem weightedSymbolOrderLE_negative_iff (n : ℤ) (hn : n<0) (p : SmoothSymbol) :
    WeightedSymbolOrderLE n p ↔ p=0 := by
  constructor
  · intro hp
    apply MvPolynomial.ext
    intro α
    rw [AddMonoidAlgebra.coeff_zero]
    exact (hp α).eq_zero_of_neg (by omega)
  · rintro rfl
    exact WeightedSymbolOrderLE.zero n


/-- The intrinsic finite-dimensional weighted bound in the faithful smooth-symbol presentation. -/
theorem actual_uniform_weighted_symbol_bound (E : Submodule ℝ Operator)
    [FiniteDimensional ℝ E] :
    ∃ N : ℕ, ∀ p : SmoothSymbol, normalQuantize p ∈ E →
      (∃ n : ℕ, WeightedSymbolOrderLE n p) → WeightedSymbolOrderLE N p := by
  obtain ⟨N,hN⟩ := actual_uniform_weighted_normal_bound E
  refine ⟨N, ?_⟩
  intro p hp ⟨n,hn⟩
  have hp' : normalAction (normalTotalSymbol.symm p) ∈ E := hp
  have hn' : normalTotalSymbol.symm p ∈ weightedNormalSpace n := by
    rw [← weightedSymbolOrderLE_iff_normal, LinearEquiv.apply_symm_apply]
    exact hn
  have hh := hN (normalTotalSymbol.symm p) hp' ⟨n,hn'⟩
  rw [← weightedSymbolOrderLE_iff_normal, LinearEquiv.apply_symm_apply] at hh
  exact hh

end Wong.SmoothModel
