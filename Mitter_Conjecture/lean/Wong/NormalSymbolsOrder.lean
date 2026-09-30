import Wong.NormalSymbols
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Integer-indexed order bounds avoid silently retaining constants at negative order.
Every assertion is a proved support property of the actual smooth total symbol. -/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

/-- Momentum order at most an integer; negative bounds force the symbol to vanish. -/
def SymbolOrderLE (n : ℤ) (p : SmoothSymbol) : Prop :=
  ∀ α : MultiIndex, n < (α.degree : ℤ) → p.coeff α = 0

namespace SymbolOrderLE

theorem zero (n : ℤ) : SymbolOrderLE n 0 := by intro α _; simp

theorem mono {m n : ℤ} {p : SmoothSymbol} (h : SymbolOrderLE m p) (hmn : m ≤ n) :
    SymbolOrderLE n p := by
  intro α hα
  exact h α (hmn.trans_lt hα)

theorem add {n : ℤ} {p q : SmoothSymbol} (hp : SymbolOrderLE n p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE n (p + q) := by
  intro α hα
  simp [hp α hα, hq α hα]

theorem neg {n : ℤ} {p : SmoothSymbol} (hp : SymbolOrderLE n p) :
    SymbolOrderLE n (-p) := by
  intro α hα
  simp [hp α hα]

theorem sub {n : ℤ} {p q : SmoothSymbol} (hp : SymbolOrderLE n p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE n (p - q) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem sum {ι : Type*} (s : Finset ι) (p : ι → SmoothSymbol) (n : ℤ)
    (hp : ∀ i ∈ s, SymbolOrderLE n (p i)) : SymbolOrderLE n (∑ i ∈ s, p i) := by
  intro α hα
  simp only [coeff_sum]
  exact Finset.sum_eq_zero (fun i hi => hp i hi α hα)

theorem mul {m n : ℤ} {p q : SmoothSymbol} (hp : SymbolOrderLE m p) (hq : SymbolOrderLE n q) :
    SymbolOrderLE (m + n) (p * q) := by
  classical
  intro α hα
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have he := Finset.mem_antidiagonal.mp hab
  have hdeg : ab.1.degree + ab.2.degree = α.degree := by rw [← map_add, he]
  by_cases hp' : m < (ab.1.degree : ℤ)
  · rw [hp _ hp', zero_mul]
  · have hq' : n < (ab.2.degree : ℤ) := by omega
    rw [hq _ hq', mul_zero]

theorem monomial (α : MultiIndex) (u : Smooth) :
    SymbolOrderLE (α.degree : ℤ) (MvPolynomial.monomial α u) := by
  classical
  intro β hβ
  have hne : α ≠ β := by intro he; subst β; omega
  simp [coeff_monomial, hne]

theorem C (u : Smooth) : SymbolOrderLE 0 (MvPolynomial.C u) := by
  simpa only [map_zero, Nat.cast_zero, C_apply] using monomial (0 : MultiIndex) u

theorem X (i : Fin 3) : SymbolOrderLE 1 (MvPolynomial.X i : SmoothSymbol) := by
  simpa only [MvPolynomial.X, Finsupp.degree_single, Nat.cast_one] using
    monomial (Finsupp.single i 1) (1 : Smooth)

theorem coefficientDerivative {n : ℤ} {p : SmoothSymbol} (hp : SymbolOrderLE n p)
    (i : Fin 3) : SymbolOrderLE n (symbolCoefficientDerivative i p) := by
  intro α hα
  simp [hp α hα]

theorem pderiv {n : ℤ} {p : SmoothSymbol} (hp : SymbolOrderLE n p)
    (i : Fin 3) : SymbolOrderLE (n - 1) (MvPolynomial.pderiv i p) := by
  intro α hα
  rw [coeff_pderiv]
  have hh : n < ((α + Finsupp.single i 1).degree : ℤ) := by
    simp only [map_add, Finsupp.degree_single, Nat.cast_add, Nat.cast_one]
    omega
  rw [hp _ hh, zero_mul]

end SymbolOrderLE

theorem symbolOrderLE_nat_iff (n : ℕ) (p : SmoothSymbol) :
    SymbolOrderLE (n : ℤ) p ↔ p.totalDegree ≤ n := by
  constructor
  · intro hp
    rw [totalDegree, Finset.sup_le_iff]
    intro α hα
    by_contra hn
    have hh : (n : ℤ) < (α.degree : ℤ) := by
      change ¬α.degree ≤ n at hn
      omega
    exact (mem_support_iff.mp hα) (hp α hh)
  · intro hp α hα
    exact coeff_eq_zero_of_totalDegree_lt (by
      change p.totalDegree < α.degree
      omega)

theorem symbolOrderLE_negative_iff (n : ℤ) (hn : n < 0) (p : SmoothSymbol) :
    SymbolOrderLE n p ↔ p = 0 := by
  constructor
  · intro hp
    apply MvPolynomial.ext
    intro α
    exact hp α (by omega)
  · rintro rfl
    exact SymbolOrderLE.zero n

theorem homogeneousComponent_eq_of_order_sub (p q : SmoothSymbol) (n : ℕ)
    (h : SymbolOrderLE ((n : ℤ) - 1) (p - q)) :
    homogeneousComponent n p = homogeneousComponent n q := by
  apply MvPolynomial.ext
  intro α
  simp only [coeff_homogeneousComponent]
  split_ifs with he
  · have hh := h α (by omega)
    rw [coeff_sub] at hh
    exact sub_eq_zero.mp hh
  · rfl

/-- The exact coefficient derivative acts trivially on a constant-coefficient momentum monomial. -/
@[simp] theorem symbolCoefficientDerivative_momentum (i : Fin 3) (α : MultiIndex) :
    symbolCoefficientDerivative i (monomial α (1 : Smooth)) = 0 := by
  rw [symbolCoefficientDerivative_monomial]
  have hz : partialDerivative i (1 : Smooth) = 0 := by simpa using partialDerivative_const i 1
  rw [hz, monomial_zero]

/-- Smooth mixed-partial symmetry transfers coefficientwise to symbols. -/
theorem symbolCoefficientDerivative_commute (i j : Fin 3) (p : SmoothSymbol) :
    symbolCoefficientDerivative i (symbolCoefficientDerivative j p) =
      symbolCoefficientDerivative j (symbolCoefficientDerivative i p) := by
  apply MvPolynomial.ext
  intro α
  simp only [symbolCoefficientDerivative_coeff]
  exact partialDerivative_commute_apply i j _

end Wong.SmoothModel
