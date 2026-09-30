import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-!
# A genuine principal-symbol quotient calculation

This file proves, in Mathlib's multivariable polynomial algebra, the
Poisson-bracket identity used to discard terms containing the hidden momentum.
The five retained variables are `x₁,x₂,x₃,ξ₁,ξ₂`; the extra `Unit` variable is
`ξ₃`. Independence of the restricted symbols from `x₃` is the precise and
necessary hypothesis. The quotient identity itself is proved from formal
partial derivatives, and is not assumed.

The bridge from smooth differential operators to these polynomial principal
symbols and the external polynomiality theorem remain separate obligations.
-/

namespace Wong.PoissonQuotient

noncomputable section

open MvPolynomial

variable {R : Type*} [CommRing R]

abbrev Full (R : Type*) [CommRing R] := MvPolynomial (Fin 5 ⊕ Unit) R
abbrev Visible (R : Type*) [CommRing R] := MvPolynomial (Fin 5) R

/-- Set the hidden momentum `ξ₃` to zero and leave the other five variables unchanged. -/
def project : Full R →ₐ[R] Visible R :=
  aeval (Sum.elim X (fun _ : Unit => 0))

/-- Substitution commutes with every retained-variable partial derivative. -/
theorem project_pderiv (p : Full R) (i : Fin 5) :
    project (pderiv (Sum.inl i) p) = pderiv i (project p) := by
  simpa [project, Function.comp_def] using
    (aeval_sumElim_pderiv_inl p (fun _ : Unit => (0 : R)) i)

def poisson (p q : Full R) : Full R :=
  pderiv (Sum.inl 3) p * pderiv (Sum.inl 0) q -
    pderiv (Sum.inl 0) p * pderiv (Sum.inl 3) q +
  (pderiv (Sum.inl 4) p * pderiv (Sum.inl 1) q -
    pderiv (Sum.inl 1) p * pderiv (Sum.inl 4) q) +
  (pderiv (Sum.inr ()) p * pderiv (Sum.inl 2) q -
    pderiv (Sum.inl 2) p * pderiv (Sum.inr ()) q)

def poissonVisible (p q : Visible R) : Visible R :=
  pderiv 3 p * pderiv 0 q - pderiv 0 p * pderiv 3 q +
    (pderiv 4 p * pderiv 1 q - pderiv 1 p * pderiv 4 q)

/-- The visible symbol quotient respects this bracket when the retained symbols
are independent of the hidden position `x₃`. -/
theorem project_poisson (p q : Full R)
    (hp : pderiv 2 (project p) = 0)
    (hq : pderiv 2 (project q) = 0) :
    project (poisson p q) = poissonVisible (project p) (project q) := by
  simp [poisson, poissonVisible, map_add, map_sub, map_mul,
    project_pderiv, hp, hq]

@[simp] theorem project_hidden :
    project (X (Sum.inr ()) : Full R) = 0 := by
  simp [project]

@[simp] theorem project_hidden_mul (p : Full R) :
    project (X (Sum.inr ()) * p) = 0 := by
  simp only [map_mul, project_hidden, zero_mul]

/-- Two terms containing the hidden momentum cannot create a visible term. -/
theorem hidden_hidden (p q : Full R) :
    project (poisson (X (Sum.inr ()) * p) (X (Sum.inr ()) * q)) = 0 := by
  rw [project_poisson]
  · simp [poissonVisible]
  · simp
  · simp

/-- A hidden term cannot enter the visible quotient when the other visible symbol
is independent of the hidden position. -/
theorem hidden_left (p q : Full R) (hq : pderiv 2 (project q) = 0) :
    project (poisson (X (Sum.inr ()) * p) q) = 0 := by
  rw [project_poisson]
  · simp [poissonVisible]
  · simp
  · exact hq

theorem hidden_right (p q : Full R) (hp : pderiv 2 (project p) = 0) :
    project (poisson p (X (Sum.inr ()) * q)) = 0 := by
  rw [project_poisson]
  · simp [poissonVisible]
  · exact hp
  · simp

/-- Arbitrary hidden remainders can be discarded on both sides of the bracket. -/
theorem discard_hidden_remainders (p q r s : Full R)
    (hp : pderiv 2 (project p) = 0)
    (hq : pderiv 2 (project q) = 0) :
    project (poisson (p + X (Sum.inr ()) * r) (q + X (Sum.inr ()) * s)) =
      poissonVisible (project p) (project q) := by
  rw [project_poisson]
  · simp
  · simpa using hp
  · simpa using hq

/-- The canonical bracket for one position and one momentum. -/
def poissonOne (p q : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  pderiv 1 p * pderiv 0 q - pderiv 0 p * pderiv 1 q

/-- The exact pure-direction principal-symbol step; `c₀` is an arbitrary constant tail. -/
theorem pure_direction_step (A c₀ c : R) (n : ℕ) :
    poissonOne (C c * X 1 ^ (n + 1)) ((C A * X 0 + C c₀) * X 1 ^ 2) =
      C (((n + 1 : ℕ) : R) * A * c) * X 1 ^ (n + 2) := by
  simp only [poissonOne, pderiv_mul, pderiv_pow, pderiv_C, map_add, pderiv_X,
    Pi.single_apply]
  simp [map_mul, pow_succ]
  ring

def headCoefficient (A : R) : ℕ → R
  | 0 => A
  | n + 1 => ((n + 3 : ℕ) : R) * A * headCoefficient A n

def pureSymbols (A : R) (n : ℕ) : MvPolynomial (Fin 2) R :=
  C (headCoefficient A n) * X 1 ^ (n + 3)

/-- Every step of the pure-direction symbol ladder is the actual Poisson bracket. -/
theorem pureSymbols_step (A c₀ : R) (n : ℕ) :
    poissonOne (pureSymbols A n) ((C A * X 0 + C c₀) * X 1 ^ 2) =
      pureSymbols A (n + 1) := by
  simpa [pureSymbols, headCoefficient, Nat.add_assoc] using
    (pure_direction_step A c₀ (headCoefficient A n) (n + 2))

/-- In characteristic zero the tracked coefficient never vanishes. -/
theorem headCoefficient_ne_zero [IsDomain R] [CharZero R]
    (A : R) (hA : A ≠ 0) (n : ℕ) : headCoefficient A n ≠ 0 := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    exact mul_ne_zero
      (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (n + 2))) hA) ih

/-- The principal symbol produced at every order is nonzero. -/
theorem pureSymbols_ne_zero [IsDomain R] [CharZero R]
    (A : R) (hA : A ≠ 0) (n : ℕ) : pureSymbols A n ≠ 0 := by
  exact mul_ne_zero (C_ne_zero.mpr (headCoefficient_ne_zero A hA n))
    (pow_ne_zero _ (X_ne_zero (1 : Fin 2)))

/-! For the pure-direction quotient, retain `x₁,x₂,x₃,ξ₁` and discard both
`ξ₂` and `ξ₃`. This is a separate indexing of the same six-variable algebra. -/

abbrev HeadFull (R : Type*) [CommRing R] := MvPolynomial (Fin 4 ⊕ Fin 2) R
abbrev HeadVisible (R : Type*) [CommRing R] := MvPolynomial (Fin 4) R

def headProject : HeadFull R →ₐ[R] HeadVisible R :=
  aeval (Sum.elim X (fun _ : Fin 2 => 0))

theorem headProject_pderiv (p : HeadFull R) (i : Fin 4) :
    headProject (pderiv (Sum.inl i) p) = pderiv i (headProject p) := by
  simpa [headProject, Function.comp_def] using
    (aeval_sumElim_pderiv_inl p (fun _ : Fin 2 => (0 : R)) i)

def headPoisson (p q : HeadFull R) : HeadFull R :=
  pderiv (Sum.inl 3) p * pderiv (Sum.inl 0) q -
    pderiv (Sum.inl 0) p * pderiv (Sum.inl 3) q +
  (pderiv (Sum.inr 0) p * pderiv (Sum.inl 1) q -
    pderiv (Sum.inl 1) p * pderiv (Sum.inr 0) q) +
  (pderiv (Sum.inr 1) p * pderiv (Sum.inl 2) q -
    pderiv (Sum.inl 2) p * pderiv (Sum.inr 1) q)

def headPoissonVisible (p q : HeadVisible R) : HeadVisible R :=
  pderiv 3 p * pderiv 0 q - pderiv 0 p * pderiv 3 q

/-- The pure-direction quotient, proved with both discarded canonical pairs present. -/
theorem headProject_poisson (p q : HeadFull R)
    (hp₁ : pderiv 1 (headProject p) = 0) (hp₂ : pderiv 2 (headProject p) = 0)
    (hq₁ : pderiv 1 (headProject q) = 0) (hq₂ : pderiv 2 (headProject q) = 0) :
    headProject (headPoisson p q) = headPoissonVisible (headProject p) (headProject q) := by
  simp [headPoisson, headPoissonVisible, map_add, map_sub, map_mul,
    headProject_pderiv, hp₁, hp₂, hq₁, hq₂]

theorem head_visible_step (A c₀ c : R) (n : ℕ) :
    headPoissonVisible (C c * X 3 ^ (n + 1)) ((C A * X 0 + C c₀) * X 3 ^ 2) =
      C (((n + 1 : ℕ) : R) * A * c) * X 3 ^ (n + 2) := by
  simp only [headPoissonVisible, pderiv_mul, pderiv_pow, pderiv_C, map_add,
    pderiv_X, Pi.single_apply]
  simp [map_mul, pow_succ]
  ring

/-- Arbitrary hidden remainder terms cannot alter the pure-direction coefficient
recurrence. The hypotheses specify only the two input symbols modulo `(ξ₂,ξ₃)`. -/
theorem full_pure_direction_step (p q : HeadFull R) (A c₀ c : R) (n : ℕ)
    (hp : headProject p = C c * X 3 ^ (n + 1))
    (hq : headProject q = (C A * X 0 + C c₀) * X 3 ^ 2) :
    headProject (headPoisson p q) =
      C (((n + 1 : ℕ) : R) * A * c) * X 3 ^ (n + 2) := by
  rw [headProject_poisson]
  · rw [hp, hq]
    exact head_visible_step A c₀ c n
  · simp [hp]
  · simp [hp]
  · simp [hq]
  · simp [hq]

/-- The initial kinetic-symbol bracket produces `A ξ₁³`; the sole condition on
`half` is the ring identity defining one half. -/
theorem initial_full_pure (p q : HeadFull R) (A c₀ half : R)
    (hhalf : 2 * half = 1)
    (hp : headProject p = C half * X 3 ^ 2)
    (hq : headProject q = (C A * X 0 + C c₀) * X 3 ^ 2) :
    headProject (headPoisson p q) = C A * X 3 ^ 3 := by
  have hc : 2 * A * half = A := by
    calc
      _ = (2 * half) * A := by ring
      _ = A := by rw [hhalf, one_mul]
  simpa [hc] using (full_pure_direction_step p q A c₀ half 1 hp hq)

def fullHeadWords (p₀ q : HeadFull R) : ℕ → HeadFull R
  | 0 => p₀
  | n + 1 => headPoisson (fullHeadWords p₀ q n) q

/-- All-order propagation of the exact quotient, allowing arbitrary hidden
terms in the initial symbol and in the fixed second-order symbol. -/
theorem fullHeadWords_projection (p₀ q : HeadFull R) (A c₀ : R)
    (hp₀ : headProject p₀ = C A * X 3 ^ 3)
    (hq : headProject q = (C A * X 0 + C c₀) * X 3 ^ 2) (n : ℕ) :
    headProject (fullHeadWords p₀ q n) =
      C (headCoefficient A n) * X 3 ^ (n + 3) := by
  induction n with
  | zero => exact hp₀
  | succ n ih =>
    simpa [fullHeadWords, headCoefficient, Nat.add_assoc] using
      (full_pure_direction_step (fullHeadWords p₀ q n) q A c₀
        (headCoefficient A n) (n + 2) ih hq)

/-- The actual full Poisson iterates, including all hidden remainders, are nonzero. -/
theorem fullHeadWords_ne_zero [IsDomain R] [CharZero R]
    (p₀ q : HeadFull R) (A c₀ : R) (hA : A ≠ 0)
    (hp₀ : headProject p₀ = C A * X 3 ^ 3)
    (hq : headProject q = (C A * X 0 + C c₀) * X 3 ^ 2) (n : ℕ) :
    fullHeadWords p₀ q n ≠ 0 := by
  intro hzero
  have h := fullHeadWords_projection p₀ q A c₀ hp₀ hq n
  rw [hzero, map_zero] at h
  exact (mul_ne_zero (C_ne_zero.mpr (headCoefficient_ne_zero A hA n))
    (pow_ne_zero _ (X_ne_zero (3 : Fin 4)))) h.symm

end

end Wong.PoissonQuotient
