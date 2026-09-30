import Wong.NormalSymbolsBracket
import Wong.NormalSymbolsOrderBridge

/-!
# Intrinsic hidden-polynomial weighted order of actual normal forms

The hidden degree is measured by actual iterated partial derivatives.
Negative degree means zero. No formal polynomial representation of a smooth
coefficient is assumed, and no symbolic principal-map hypothesis is used.
-/
noncomputable section
namespace Wong.SmoothModel

/-- The actual hidden derivative annihilates every power beyond the bound. -/
def HiddenDegreeLE (n : ℤ) (u : Smooth) : Prop :=
  ∀ k : ℕ, n < (k : ℤ) → (partialDerivative 2 ^ k) u = 0

namespace HiddenDegreeLE

theorem zero (n : ℤ) : HiddenDegreeLE n 0 := by intro k _; exact map_zero _

theorem mono {m n : ℤ} {u : Smooth} (h : HiddenDegreeLE m u) (hmn : m≤n) :
    HiddenDegreeLE n u := by intro k hk; exact h k (hmn.trans_lt hk)

theorem eq_zero_of_neg {n : ℤ} {u : Smooth} (h : HiddenDegreeLE n u) (hn : n<0) : u=0 := by
  simpa using h 0 hn

theorem add {n : ℤ} {u v : Smooth} (hu : HiddenDegreeLE n u) (hv : HiddenDegreeLE n v) :
    HiddenDegreeLE n (u+v) := by
  intro k hk
  rw [map_add, hu k hk, hv k hk, add_zero]

theorem smul {n : ℤ} {u : Smooth} (hu : HiddenDegreeLE n u) (c : ℝ) :
    HiddenDegreeLE n (c • u) := by
  intro k hk
  rw [map_smul, hu k hk, smul_zero]

theorem neg {n : ℤ} {u : Smooth} (hu : HiddenDegreeLE n u) : HiddenDegreeLE n (-u) := by
  intro k hk
  rw [map_neg, hu k hk, neg_zero]

theorem sub {n : ℤ} {u v : Smooth} (hu : HiddenDegreeLE n u) (hv : HiddenDegreeLE n v) :
    HiddenDegreeLE n (u-v) := by simpa only [sub_eq_add_neg] using hu.add hv.neg

/-- A genuine hidden derivative lowers hidden polynomial degree by one. -/
theorem hiddenDerivative {n : ℤ} {u : Smooth} (hu : HiddenDegreeLE n u) :
    HiddenDegreeLE (n-1) (partialDerivative 2 u) := by
  intro k hk
  have hh := hu (k+1) (by push_cast; omega)
  simpa only [pow_succ, Module.End.mul_apply] using hh

/-- Visible derivatives do not increase the hidden polynomial degree. -/
theorem coordinateDerivative {n : ℤ} {u : Smooth} (hu : HiddenDegreeLE n u) (i : Fin 3) :
    HiddenDegreeLE n (partialDerivative i u) := by
  intro k hk
  have hcomm : Commute (partialDerivative 2) (partialDerivative i) := partialDerivative_commute 2 i
  have hc := congrArg (fun A : Operator => A u) (hcomm.pow_left k).eq
  change (partialDerivative 2 ^ k) (partialDerivative i u) =
    partialDerivative i ((partialDerivative 2 ^ k) u) at hc
  rw [hc, hu k hk, map_zero]

/-- Leibniz plus induction proves the product degree bound for actual smooth functions. -/
theorem mul {m n : ℤ} {u v : Smooth} (hu : HiddenDegreeLE m u) (hv : HiddenDegreeLE n v) :
    HiddenDegreeLE (m+n) (u*v) := by
  intro k
  induction k generalizing m n u v with
  | zero =>
    intro hk
    by_cases hm : m<0
    · rw [hu.eq_zero_of_neg hm, zero_mul, map_zero]
    · have hn : n<0 := by simp only [Nat.cast_zero] at hk; omega
      rw [hv.eq_zero_of_neg hn, mul_zero, map_zero]
  | succ k ih =>
    intro hk
    rw [pow_succ, Module.End.mul_apply]
    change (partialDerivative 2 ^ k) (partialDerivative 2 (smoothMul u v)) = 0
    rw [partialDerivative_smoothMul, map_add]
    have h₁ := ih hu.hiddenDerivative hv (show m-1+n < (k:ℤ) by push_cast at hk; omega)
    have h₂ := ih hu hv.hiddenDerivative (show m+(n-1) < (k:ℤ) by push_cast at hk; omega)
    exact (congrArg₂ (·+·) h₁ h₂).trans (add_zero 0)

theorem constant (c : ℝ) : HiddenDegreeLE 0 (c • smoothOne) := by
  intro k hk
  cases k with
  | zero => norm_num at hk
  | succ k =>
    rw [pow_succ, Module.End.mul_apply, partialDerivative_const, map_zero]

/-- Independence of the hidden coordinate is precisely degree zero. -/
theorem of_hiddenDerivative_eq_zero (u : Smooth) (hu : partialDerivative 2 u=0) :
    HiddenDegreeLE 0 u := by
  intro k hk
  cases k with
  | zero => norm_num at hk
  | succ k => rw [pow_succ, Module.End.mul_apply, hu, map_zero]


end HiddenDegreeLE

/-- Hidden coefficient degree plus ordinary visible and double hidden derivative weight. -/
def momentumWeight (α : MultiIndex) : ℕ := α 0 + α 1 + 2*α 2

@[simp] theorem momentumWeight_zero : momentumWeight 0=0 := rfl

@[simp] theorem momentumWeight_add (α β : MultiIndex) :
    momentumWeight (α+β)=momentumWeight α+momentumWeight β := by
  simp only [momentumWeight, Finsupp.add_apply]
  ring

@[simp] theorem momentumWeight_single (i : Fin 3) (n : ℕ) :
    momentumWeight (Finsupp.single i n) = (if i=2 then 2 else 1)*n := by
  fin_cases i <;> simp [momentumWeight]

/-- The real weighted filtration, defined directly on faithful actual normal forms. -/
def weightedNormalSpace (n : ℤ) : Submodule ℝ NormalForm where
  carrier := {p | ∀ α, HiddenDegreeLE (n-(momentumWeight α:ℤ)) (p α)}
  zero_mem' := by intro α; exact HiddenDegreeLE.zero _
  add_mem' := by intro p q hp hq α; exact (hp α).add (hq α)
  smul_mem' := by intro c p hp α; exact (hp α).smul c

theorem weightedNormalSpace_monotone {m n : ℤ} (hmn : m≤n) :
    weightedNormalSpace m ≤ weightedNormalSpace n := by
  intro p hp α
  exact (hp α).mono (by omega)

/-- The union of the actual nonnegative weighted levels is a vector subspace. -/
def polynomialNormalSpace : Submodule ℝ NormalForm where
  carrier := {p | ∃ n : ℕ, p ∈ weightedNormalSpace n}
  zero_mem' := ⟨0, (weightedNormalSpace 0).zero_mem⟩
  add_mem' := by
    rintro p q ⟨m,hm⟩ ⟨n,hn⟩
    refine ⟨max m n, (weightedNormalSpace ((max m n : ℕ) : ℤ)).add_mem ?_ ?_⟩
    · exact weightedNormalSpace_monotone (by exact_mod_cast le_max_left m n) hm
    · exact weightedNormalSpace_monotone (by exact_mod_cast le_max_right m n) hn
  smul_mem' := by
    rintro c p ⟨n,hn⟩
    exact ⟨n, (weightedNormalSpace n).smul_mem c hn⟩

abbrev weightedNormalFormsIn (E : Submodule ℝ Operator) : Submodule ℝ NormalForm :=
  normalFormsIn E ⊓ polynomialNormalSpace

def weightedNormalFormsIn_action (E : Submodule ℝ Operator) : weightedNormalFormsIn E →ₗ[ℝ] E where
  toFun p := ⟨normalAction p.1,p.property.1⟩
  map_add' p q := by apply Subtype.ext; exact map_add normalAction p.1 q.1
  map_smul' c p := by apply Subtype.ext; exact map_smul normalAction c p.1

theorem weightedNormalFormsIn_action_injective (E : Submodule ℝ Operator) :
    Function.Injective (weightedNormalFormsIn_action E) := by
  intro p q hpq
  apply Subtype.ext
  apply normalAction_injective
  exact congrArg Subtype.val hpq

/-- Finite dimensionality bounds all hidden-polynomial actual normal forms
in the algebra, even without assuming that every algebra element is such a form. -/
theorem actual_uniform_weighted_normal_bound (E : Submodule ℝ Operator)
    [FiniteDimensional ℝ E] :
    ∃ N : ℕ, ∀ p : NormalForm, normalAction p ∈ E →
      (∃ n : ℕ, p ∈ weightedNormalSpace n) → p ∈ weightedNormalSpace N := by
  classical
  let : Module.Finite ℝ (weightedNormalFormsIn E) :=
    Module.Finite.of_injective (weightedNormalFormsIn_action E)
      (weightedNormalFormsIn_action_injective E)
  obtain ⟨s,hs⟩ := Module.Finite.fg_top (R:=ℝ) (M:=weightedNormalFormsIn E)
  choose n hn using fun p : weightedNormalFormsIn E => p.property.2
  let N := s.sup n
  refine ⟨N, ?_⟩
  have hspan : Submodule.span ℝ (s : Set (weightedNormalFormsIn E)) ≤
      (weightedNormalSpace N).comap (weightedNormalFormsIn E).subtype := by
    apply Submodule.span_le.mpr
    intro p hp
    exact weightedNormalSpace_monotone (by exact_mod_cast Finset.le_sup hp) (hn p)
  rw [hs] at hspan
  intro p hp hpw
  exact hspan (show (⟨p, hp, hpw⟩ : weightedNormalFormsIn E) ∈
    (⊤ : Submodule ℝ (weightedNormalFormsIn E)) from Submodule.mem_top)

end Wong.SmoothModel
