import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-!
# Algebraic core of the smooth Euler decomposition

These lemmas verify two algebraic steps of the manuscript independently of
smooth differential-operator theory:

* a commuting perturbation nilpotent on a vector transfers annihilation;
* polynomial congruences isolate a component annihilated by its block polynomial.

The analytic Euler ODE and existence of the smooth finite decomposition are
not postulated as axioms or claimed to be proved here. The CRT projection
polynomials are constructed below from pairwise coprimality.
-/

namespace Wong.EulerAlgebra

section CommutingPowers

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- On a vector killed by `A`, powers of `A + B` agree with powers of `B`
when the two endomorphisms commute. -/
theorem add_pow_apply_eq_of_annihilate
    (A B : Module.End R V) (hAB : Commute A B) (v : V) (hA : A v = 0)
    (n : ℕ) : ((A + B) ^ n) v = (B ^ n) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    have hcomm : Commute (A + B) (B ^ n) :=
      (hAB.add_left (Commute.refl B)).pow_right n
    calc
      (A + B) ((B ^ n) v) = (B ^ n) ((A + B) v) :=
        congrArg (fun F : Module.End R V => F v) hcomm.eq
      _ = (B ^ n) (B v) := by simp [hA]
      _ = (B ^ (n + 1)) v := by rw [pow_succ, Module.End.mul_apply]

/-- The commuting nilpotent-perturbation step used after Cayley--Hamilton.
In the paper, `A = χ(T)` and `A - N * S = χ(D)`. No preservation of the
finite-dimensional Lie algebra by `N` or `S` is assumed. -/
theorem annihilator_transfer
    (A N S : Module.End R V) (hAN : Commute A N) (hAS : Commute A S)
    (hNS : Commute N S) (v : V) (hA : A v = 0)
    (n : ℕ) (hN : (N ^ n) v = 0) : ((A - N * S) ^ n) v = 0 := by
  have hproduct : ((N * S) ^ n) v = 0 := by
    rw [hNS.mul_pow, (hNS.pow_pow n n).eq, Module.End.mul_apply, hN, map_zero]
  have hnegative : ((-(N * S)) ^ n) v = 0 := by
    rw [neg_pow, Module.End.mul_apply, hproduct, map_zero]
  have hcomm : Commute A (-(N * S)) := (hAN.mul_right hAS).neg_right
  simpa only [sub_eq_add_neg, hnegative] using
    add_pow_apply_eq_of_annihilate A (-(N * S)) hcomm v hA n

end CommutingPowers

section CRTExistence

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

/-- An elementary finite Chinese-remainder construction for a single
projection: Bezout between the chosen modulus and the product of the others. -/
theorem exists_coprime_projection
    (s : Finset ι) (i : ι) (q : ι → R)
    (hcop : ∀ j ∈ s, j ≠ i → IsCoprime (q i) (q j)) :
    ∃ p : R, ∀ j ∈ s, q j ∣ p - if j = i then 1 else 0 := by
  have hprod : IsCoprime (q i) (∏ j ∈ s.erase i, q j) :=
    IsCoprime.prod_right fun j hj =>
      hcop j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  obtain ⟨a, b, hbez⟩ := hprod
  refine ⟨b * ∏ j ∈ s.erase i, q j, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [ite_true]
    refine ⟨-a, ?_⟩
    rw [← hbez]
    ring
  · simp only [hji, ite_false, sub_zero]
    exact dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem q (Finset.mem_erase.mpr ⟨hji, hj⟩)) b

end CRTExistence

section PolynomialProjection

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A submodule stable under the actual endomorphism `T` is stable under
polynomials in `T`. In the application, `T` is the adjoint action of `J`. -/
theorem aeval_mem_of_invariant
    (U : Submodule R V) (T : Module.End R V)
    (hT : ∀ v ∈ U, T v ∈ U) (p : Polynomial R) (v : V) (hv : v ∈ U) :
    (Polynomial.aeval T p) v ∈ U := by
  have hpow (n : ℕ) : (T ^ n) v ∈ U := by
    induction n with
    | zero => simpa using hv
    | succ n ih => simpa [pow_succ', Module.End.mul_apply] using hT _ ih
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using U.add_mem hp hq
  | monomial n a =>
    simpa [Polynomial.aeval_monomial, Module.End.mul_apply] using U.smul_mem a (hpow n)

/-- Congruent polynomials have the same action on a vector annihilated by
the modulus. This only needs annihilation of this vector, not of the entire
ambient space. -/
theorem aeval_apply_eq_of_dvd_sub
    (T : Module.End R V) (p r q : Polynomial R) (v : V)
    (hq : (Polynomial.aeval T q) v = 0) (hdiv : q ∣ p - r) :
    (Polynomial.aeval T p) v = (Polynomial.aeval T r) v := by
  obtain ⟨u, hu⟩ := hdiv
  have hzero : (Polynomial.aeval T (p - r)) v = 0 := by
    rw [hu, mul_comm q u, map_mul, Module.End.mul_apply, hq, map_zero]
  simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using hzero

/-- Any polynomial satisfying the CRT congruences extracts exactly the
chosen component. The congruences are explicit hypotheses, so this theorem
does not silently assume the existence of a spectral projection. -/
theorem polynomial_projection_of_congruences
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) (hi : i ∈ s)
    (T : Module.End R V) (v : ι → V) (q : ι → Polynomial R)
    (p : Polynomial R)
    (hann : ∀ j ∈ s, (Polynomial.aeval T (q j)) (v j) = 0)
    (hcong : ∀ j ∈ s, q j ∣ p - if j = i then 1 else 0) :
    (Polynomial.aeval T p) (∑ j ∈ s, v j) = v i := by
  have heach (j : ι) (hj : j ∈ s) :
      (Polynomial.aeval T p) (v j) = if j = i then v i else 0 := by
    have h := aeval_apply_eq_of_dvd_sub T p (if j = i then 1 else 0)
      (q j) (v j) (hann j hj) (hcong j hj)
    split_ifs at h ⊢ with hij
    · subst j
      simpa using h
    · simpa using h
  rw [map_sum]
  calc
    ∑ j ∈ s, (Polynomial.aeval T p) (v j) =
        ∑ j ∈ s, if j = i then v i else 0 := Finset.sum_congr rfl heach
    _ = v i := by simp [hi]

/-- Pairwise-coprime block annihilators yield an actual polynomial in `T`
which extracts a specified summand. Both CRT existence and action are proved. -/
theorem exists_polynomial_projection
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) (hi : i ∈ s)
    (T : Module.End R V) (v : ι → V) (q : ι → Polynomial R)
    (hann : ∀ j ∈ s, (Polynomial.aeval T (q j)) (v j) = 0)
    (hcop : ∀ j ∈ s, j ≠ i → IsCoprime (q i) (q j)) :
    ∃ p : Polynomial R, (Polynomial.aeval T p) (∑ j ∈ s, v j) = v i := by
  obtain ⟨p, hp⟩ := exists_coprime_projection s i q hcop
  exact ⟨p, polynomial_projection_of_congruences s i hi T v q p hann hp⟩

end PolynomialProjection

section GeneralizedWeightProjection

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [DecidableEq ι]

/-- Generalized eigenspaces at distinct weights admit genuine polynomial
projection. The nilpotence exponent may be chosen uniformly as in the paper. -/
theorem generalized_weight_projection
    (s : Finset ι) (i : ι) (hi : i ∈ s) (w : ι → K)
    (hw : Set.InjOn w (s : Set ι)) (n : ℕ)
    (T : Module.End K V) (v : ι → V)
    (hann : ∀ j ∈ s,
      ((T - algebraMap K (Module.End K V) (w j)) ^ n) (v j) = 0) :
    ∃ p : Polynomial K, (Polynomial.aeval T p) (∑ j ∈ s, v j) = v i := by
  let q : ι → Polynomial K := fun j => (Polynomial.X - Polynomial.C (w j)) ^ n
  apply exists_polynomial_projection s i hi T v q
  · intro j hj
    simpa [q] using hann j hj
  · intro j hj hji
    have hne : w i ≠ w j := fun heq => hji (hw hj hi heq.symm)
    have hc : IsCoprime (Polynomial.X - Polynomial.C (w i))
        (Polynomial.X - Polynomial.C (w j)) :=
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    exact hc.pow

/-- A generalized weight component of a finite decomposition belongs to any
`T`-invariant submodule containing the original vector. This is the genuine
Lie-word projection conclusion at the level of its linear-algebraic core. -/
theorem generalized_weight_mem_invariant
    (s : Finset ι) (i : ι) (hi : i ∈ s) (w : ι → K)
    (hw : Set.InjOn w (s : Set ι)) (n : ℕ)
    (T : Module.End K V) (v : ι → V)
    (hann : ∀ j ∈ s,
      ((T - algebraMap K (Module.End K V) (w j)) ^ n) (v j) = 0)
    (U : Submodule K V) (hT : ∀ x ∈ U, T x ∈ U)
    (hmem : (∑ j ∈ s, v j) ∈ U) : v i ∈ U := by
  obtain ⟨p, hp⟩ := generalized_weight_projection s i hi w hw n T v hann
  rw [← hp]
  exact aeval_mem_of_invariant U T hT p _ hmem

end GeneralizedWeightProjection

end Wong.EulerAlgebra
