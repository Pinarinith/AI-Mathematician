import Wong.NormalSymbolsVisible
import Wong.SectorTwoDiagonalization

/-!
# A genuine highest-hidden-axis Lie ladder

The ordinary total-order bounds and the value/first transverse jets of the
principal symbol are explicit hypotheses. Thus arbitrary same-total-order
terms with at least two visible momenta in K, and at least one visible
momentum in Q, are retained. The projection lemma proves precisely why they
cannot contaminate the highest pure-hidden coefficient in the next bracket.
This is the principal-symbol configuration used in Shi--Yau 2017 Lemma 3.5.
No published mathematical input is used.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Wong.SmoothModel
open MvPolynomial

/-- Retain only the hidden momentum, leaving actual smooth coefficients intact. -/
def projectHiddenAxis : SmoothSymbol →ₐ[Smooth] SmoothSymbol :=
  aeval fun i : Fin 3 => if i = 2 then X 2 else 0

@[simp] theorem projectHiddenAxis_C (u : Smooth) : projectHiddenAxis (C u) = C u := by
  simp [projectHiddenAxis]

@[simp] theorem projectHiddenAxis_X (i : Fin 3) :
    projectHiddenAxis (X i) = if i = 2 then X 2 else 0 := by
  simp [projectHiddenAxis]

theorem projectHiddenAxis_coefficientDerivative (p : SmoothSymbol) (i : Fin 3) :
    projectHiddenAxis (symbolCoefficientDerivative i p) =
      symbolCoefficientDerivative i (projectHiddenAxis p) := by
  induction p using MvPolynomial.induction_on with
  | C u => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases hj : j = 2
    · simp [map_mul, symbolCoefficientDerivative_mul, hp, hj]
    · simp [map_mul, symbolCoefficientDerivative_mul, hp, hj]

theorem coefficientDerivative_hiddenAxisMonomial (i : Fin 3) (u : Smooth) (l : ℕ) :
    symbolCoefficientDerivative i (C u * X 2 ^ l) = C (partialDerivative i u) * X 2 ^ l := by
  rw [C_mul_X_pow_eq_monomial, symbolCoefficientDerivative_monomial,
    ← C_mul_X_pow_eq_monomial]

/-- Exact projection of the genuine Poisson bracket. No restrictions on the
unrecorded transverse terms of q are needed: their reverse contributions
multiply derivatives of the constant pure-hidden coefficient of k. -/
theorem projectHiddenAxis_poisson (k q : SmoothSymbol) (n l : ℕ)
    (c : ℝ) (v₀ v₁ u : Smooth)
    (hk : projectHiddenAxis k = C (c • smoothOne) * X 2 ^ (n + 1))
    (hk₀ : projectHiddenAxis (pderiv 0 k) = C v₀ * X 2 ^ n)
    (hk₁ : projectHiddenAxis (pderiv 1 k) = C v₁ * X 2 ^ n)
    (hq : projectHiddenAxis q = C u * X 2 ^ l)
    (hu : partialDerivative 2 u = 0) :
    projectHiddenAxis (symbolPoisson k q) =
      C (v₀ * partialDerivative 0 u + v₁ * partialDerivative 1 u) * X 2 ^ (n+l) := by
  have hDk (i : Fin 3) : projectHiddenAxis (symbolCoefficientDerivative i k) = 0 := by
    rw [projectHiddenAxis_coefficientDerivative, hk,
      coefficientDerivative_hiddenAxisMonomial, partialDerivative_const, map_zero, zero_mul]
  have hDq (i : Fin 3) : projectHiddenAxis (symbolCoefficientDerivative i q) =
      C (partialDerivative i u) * X 2 ^ l := by
    rw [projectHiddenAxis_coefficientDerivative, hq, coefficientDerivative_hiddenAxisMonomial]
  simp only [symbolPoisson, symbolFirstCorrection, map_sub, map_mul,
    Fin.sum_univ_three, hDk, hDq, hk₀, hk₁, hu, map_zero, zero_mul, mul_zero,
    add_zero, sub_zero, map_add, map_mul, pow_add]
  ring

/-- The projection is attached to actual principal symbols and hence to
actual brackets; the lower ordinary-order remainder is discharged by the
proved principal-symbol bridge. -/
theorem hiddenAxis_principal_bracket (K Q : NormalForm) (n l : ℕ)
    (hK : NormalDegreeLE (n+1) K) (hQ : NormalDegreeLE (l+1) Q)
    (c : ℝ) (v₀ v₁ u : Smooth)
    (hk : projectHiddenAxis (normalSymbol (n+1) K) = C (c • smoothOne) * X 2 ^ (n+1))
    (hk₀ : projectHiddenAxis (pderiv 0 (normalSymbol (n+1) K)) = C v₀ * X 2 ^ n)
    (hk₁ : projectHiddenAxis (pderiv 1 (normalSymbol (n+1) K)) = C v₁ * X 2 ^ n)
    (hq : projectHiddenAxis (normalSymbol (l+1) Q) = C u * X 2 ^ (l+1))
    (hu : partialDerivative 2 u = 0) :
    projectHiddenAxis (normalSymbol (n+l+1) (normalBracket K Q)) =
      C (v₀ * partialDerivative 0 u + v₁ * partialDerivative 1 u) * X 2 ^ (n+l+1) := by
  rw [normalSymbol_bracket K Q n l hK hQ]
  simpa only [Nat.add_assoc] using
    projectHiddenAxis_poisson _ _ n (l+1) c v₀ v₁ u hk hk₀ hk₁ hq hu

def hiddenAxisWords (K Q : NormalForm) : ℕ → NormalForm
  | 0 => Q
  | r+1 => normalBracket K (hiddenAxisWords K Q r)

theorem hiddenAxisWords_mem (E : LieSubalgebra ℝ Operator) (K Q : NormalForm)
    (hK : normalAction K ∈ E) (hQ : normalAction Q ∈ E) (r : ℕ) :
    normalAction (hiddenAxisWords K Q r) ∈ E := by
  induction r with
  | zero => exact hQ
  | succ r ih =>
    rw [hiddenAxisWords, normalAction_bracket]
    exact E.lie_mem hK ih

theorem hiddenAxisWords_order (K Q : NormalForm) (n l : ℕ)
    (hK : NormalDegreeLE (n+1) K) (hQ : NormalDegreeLE (l+1) Q) (r : ℕ) :
    NormalDegreeLE (l+r*n+1) (hiddenAxisWords K Q r) := by
  induction r with
  | zero => simpa only [hiddenAxisWords, Nat.zero_mul, Nat.add_zero] using hQ
  | succ r ih =>
    apply normalDegreeLE_of_action_order
    rw [hiddenAxisWords, normalAction_bracket]
    have hh := lie_mem_orderSpace_sharp (action_order_of_normalDegreeLE K _ hK)
      (action_order_of_normalDegreeLE _ _ ih)
    have hi : (n+1)+(l+r*n+1)-1 = l+(r+1)*n+1 := by
      simp only [Nat.add_mul, one_mul]
      omega
    simpa only [hi] using hh

theorem hiddenAxisWords_projected (K Q : NormalForm) (n l : ℕ)
    (hK : NormalDegreeLE (n+1) K) (hQ : NormalDegreeLE (l+1) Q)
    (c lam : ℝ) (v₀ v₁ u : Smooth)
    (hk : projectHiddenAxis (normalSymbol (n+1) K) = C (c • smoothOne) * X 2 ^ (n+1))
    (hk₀ : projectHiddenAxis (pderiv 0 (normalSymbol (n+1) K)) = C v₀ * X 2 ^ n)
    (hk₁ : projectHiddenAxis (pderiv 1 (normalSymbol (n+1) K)) = C v₁ * X 2 ^ n)
    (hq : projectHiddenAxis (normalSymbol (l+1) Q) = C u * X 2 ^ (l+1))
    (hu : partialDerivative 2 u = 0)
    (heigen : v₀ * partialDerivative 0 u + v₁ * partialDerivative 1 u = lam • u)
    (r : ℕ) :
    projectHiddenAxis (normalSymbol (l+r*n+1) (hiddenAxisWords K Q r)) =
      C ((lam^r) • u) * X 2 ^ (l+r*n+1) := by
  induction r with
  | zero => simpa only [hiddenAxisWords, Nat.zero_mul, Nat.add_zero, pow_zero, one_smul] using hq
  | succ r ih =>
    have hcoef : v₀ * partialDerivative 0 ((lam^r) • u) +
        v₁ * partialDerivative 1 ((lam^r) • u) = (lam^(r+1)) • u := by
      rw [map_smul, map_smul, mul_smul_comm, mul_smul_comm, ← smul_add,
        heigen, smul_smul, pow_succ]
    have hh := hiddenAxis_principal_bracket K (hiddenAxisWords K Q r) n (l+r*n)
      hK (hiddenAxisWords_order K Q n l hK hQ r) c v₀ v₁ ((lam^r) • u)
      hk hk₀ hk₁ ih (by rw [map_smul, hu, smul_zero])
    rw [hcoef] at hh
    have hi : n+(l+r*n)+1=l+(r+1)*n+1 := by
      simp only [Nat.add_mul, one_mul]
      omega
    simpa only [hiddenAxisWords, hi] using hh

theorem hiddenAxisMonomial_ne_zero (u : Smooth) (l : ℕ) (hu : u ≠ 0) :
    (C u * X 2 ^ l : SmoothSymbol) ≠ 0 := by
  intro hz
  have hc := congrArg (fun p : SmoothSymbol => p.coeff (Finsupp.single 2 l)) hz
  apply hu
  simpa [C_mul_X_pow_eq_monomial] using hc

/-- A genuine eigenfunction for the visible transport produces arbitrarily
large actual differential order, even with arbitrary permitted transverse
remainders. The conclusion uses actual finite-dimensional Lie membership. -/
theorem actual_hiddenAxis_eigen_ladder_obstruction
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (K Q : NormalForm) (n l : ℕ) (hn : 0 < n)
    (hKE : normalAction K ∈ E) (hQE : normalAction Q ∈ E)
    (hK : NormalDegreeLE (n+1) K) (hQ : NormalDegreeLE (l+1) Q)
    (c lam : ℝ) (hlam : lam ≠ 0) (v₀ v₁ u : Smooth) (hu0 : u ≠ 0)
    (hk : projectHiddenAxis (normalSymbol (n+1) K) = C (c • smoothOne) * X 2 ^ (n+1))
    (hk₀ : projectHiddenAxis (pderiv 0 (normalSymbol (n+1) K)) = C v₀ * X 2 ^ n)
    (hk₁ : projectHiddenAxis (pderiv 1 (normalSymbol (n+1) K)) = C v₁ * X 2 ^ n)
    (hq : projectHiddenAxis (normalSymbol (l+1) Q) = C u * X 2 ^ (l+1))
    (hu : partialDerivative 2 u = 0)
    (heigen : v₀ * partialDerivative 0 u + v₁ * partialDerivative 1 u = lam • u) : False := by
  obtain ⟨N, hN⟩ := actual_uniform_normal_weight_bound E.toSubmodule (fun α => α.degree)
  have hbound : NormalDegreeLE N (hiddenAxisWords K Q N) :=
    hN _ (hiddenAxisWords_mem E K Q hKE hQE N)
  have hNn : N ≤ N*n := Nat.le_mul_of_pos_right N hn
  have hz := normalSymbol_eq_zero_above_order (hiddenAxisWords K Q N) N (l+N*n+1)
    hbound (by omega)
  have hh := hiddenAxisWords_projected K Q n l hK hQ c lam v₀ v₁ u hk hk₀ hk₁ hq hu heigen N
  rw [hz, map_zero] at hh
  exact hiddenAxisMonomial_ne_zero ((lam^N) • u) _
    (smul_ne_zero (pow_ne_zero N hlam) hu0) hh.symm

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_hiddenAxis_eigen_ladder_obstruction

namespace Wong.SmoothModel
open MvPolynomial

/-- Actual affine visible coefficient, with no hidden dependence. -/
def hiddenAxisAffineCoefficient (c a b : ℝ) : Smooth :=
  c • smoothOne + linearFunction ![a, b, 0]

@[simp] theorem partial_hiddenAxisAffineCoefficient_zero (c a b : ℝ) :
    partialDerivative 0 (hiddenAxisAffineCoefficient c a b) = a • smoothOne := by
  rw [hiddenAxisAffineCoefficient, map_add, partialDerivative_const,
    partialDerivative_linearFunction, zero_add]
  rfl

@[simp] theorem partial_hiddenAxisAffineCoefficient_one (c a b : ℝ) :
    partialDerivative 1 (hiddenAxisAffineCoefficient c a b) = b • smoothOne := by
  rw [hiddenAxisAffineCoefficient, map_add, partialDerivative_const,
    partialDerivative_linearFunction, zero_add]
  rfl

@[simp] theorem partial_hiddenAxisAffineCoefficient_two (c a b : ℝ) :
    partialDerivative 2 (hiddenAxisAffineCoefficient c a b) = 0 := by
  rw [hiddenAxisAffineCoefficient, map_add, partialDerivative_const,
    partialDerivative_linearFunction, zero_add]
  simp

/-- The exact symmetric affine-coefficient configuration of the hidden-axis
ladder. The value and first visible momentum jets encode all the displayed
highest-hidden terms, while retaining arbitrary lower-hidden remainders. -/
theorem actual_hiddenAxis_symmetric_ladder_zero
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (K A B : NormalForm) (n l : ℕ) (hn : 0 < n)
    (hKE : normalAction K ∈ E) (hAE : normalAction A ∈ E) (hBE : normalAction B ∈ E)
    (hK : NormalDegreeLE (n+1) K)
    (hA : NormalDegreeLE (l+1) A) (hB : NormalDegreeLE (l+1) B)
    (c e f k d h : ℝ)
    (hk : projectHiddenAxis (normalSymbol (n+1) K) = C (c • smoothOne) * X 2 ^ (n+1))
    (hk₀ : projectHiddenAxis (pderiv 0 (normalSymbol (n+1) K)) =
      C (hiddenAxisAffineCoefficient e k d) * X 2 ^ n)
    (hk₁ : projectHiddenAxis (pderiv 1 (normalSymbol (n+1) K)) =
      C (hiddenAxisAffineCoefficient f d h) * X 2 ^ n)
    (hAaxis : projectHiddenAxis (normalSymbol (l+1) A) =
      C (hiddenAxisAffineCoefficient e k d) * X 2 ^ (l+1))
    (hBaxis : projectHiddenAxis (normalSymbol (l+1) B) =
      C (hiddenAxisAffineCoefficient f d h) * X 2 ^ (l+1)) :
    k = 0 ∧ d = 0 ∧ h = 0 := by
  by_contra hzero
  have hne : k ≠ 0 ∨ d ≠ 0 ∨ h ≠ 0 := by tauto
  obtain ⟨a, b, lam, hab, hlam, he₀, he₁⟩ :=
    VisibleHeads.symmetric_two_nonzero_unit_eigenvector k d h hne
  let v₀ := hiddenAxisAffineCoefficient e k d
  let v₁ := hiddenAxisAffineCoefficient f d h
  let u := a • v₀ - b • v₁
  have hu₀ : partialDerivative 0 u = (lam*a) • smoothOne := by
    dsimp only [u, v₀, v₁]
    rw [map_sub, map_smul, map_smul, partial_hiddenAxisAffineCoefficient_zero,
      partial_hiddenAxisAffineCoefficient_zero, smul_smul, smul_smul, ← sub_smul]
    congr 1
    linear_combination he₀
  have hu₁ : partialDerivative 1 u = (-(lam*b)) • smoothOne := by
    dsimp only [u, v₀, v₁]
    rw [map_sub, map_smul, map_smul, partial_hiddenAxisAffineCoefficient_one,
      partial_hiddenAxisAffineCoefficient_one, smul_smul, smul_smul, ← sub_smul]
    congr 1
    linear_combination he₁
  have hu₂ : partialDerivative 2 u = 0 := by
    simp [u, v₀, v₁]
  have hu : u ≠ 0 := by
    intro hz
    have h₀ := congrArg (fun w : Smooth => w.1 (0 : State)) hu₀
    have h₁ := congrArg (fun w : Smooth => w.1 (0 : State)) hu₁
    rw [hz, map_zero] at h₀ h₁
    have ha : a = 0 := (mul_eq_zero.mp (by simpa [smoothOne] using h₀.symm)).resolve_left hlam
    have hb : b = 0 := (mul_eq_zero.mp (by simpa [smoothOne] using h₁.symm)).resolve_left hlam
    simp [ha, hb] at hab
  have heigen : v₀ * partialDerivative 0 u + v₁ * partialDerivative 1 u = lam • u := by
    rw [hu₀, hu₁]
    simp only [smoothOne_eq_one, mul_smul_comm, mul_one]
    dsimp only [u]
    module
  let Q : NormalForm := a • A - b • B
  have hQE : normalAction Q ∈ E := by
    simpa only [Q, map_sub, map_smul] using E.sub_mem (E.smul_mem a hAE) (E.smul_mem b hBE)
  have hQ : NormalDegreeLE (l+1) Q := by
    intro α hα
    simp only [Q, Finsupp.sub_apply, Finsupp.smul_apply, hA α hα, hB α hα,
      smul_zero, sub_self]
  have hq : projectHiddenAxis (normalSymbol (l+1) Q) = C u * X 2 ^ (l+1) := by
    simp only [Q, normalSymbol_sub, normalSymbol_smul, map_sub,
      AlgHom.map_smul_of_tower, hAaxis, hBaxis, u, v₀, v₁]
    simp only [sub_mul, C_mul_X_pow_eq_monomial, smul_monomial]
  exact actual_hiddenAxis_eigen_ladder_obstruction E K Q n l hn hKE hQE hK hQ
    c lam hlam v₀ v₁ u hu hk hk₀ hk₁ hq hu₂ heigen

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_hiddenAxis_symmetric_ladder_zero
