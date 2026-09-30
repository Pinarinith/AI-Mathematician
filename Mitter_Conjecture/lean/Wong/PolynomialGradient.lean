import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.Positivity

/-!
# Noncancellation of the squared gradient over the reals

The crucial positivity argument is on real evaluations: a sum of squares
can vanish only when every partial derivative vanishes. Euler's identity
then excludes a nonzero homogeneous polynomial of positive degree.
-/

noncomputable section
namespace Wong.PolynomialGradient
open MvPolynomial

variable {σ : Type*} [Fintype σ]

def gradientSquare (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i, (pderiv i p) ^ 2

theorem gradientSquare_homogeneous (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    (gradientSquare p).IsHomogeneous ((d - 1) * 2) := by
  apply IsHomogeneous.sum
  intro i _
  exact hp.pderiv.pow 2

theorem homogeneous_gradientSquare_ne_zero (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) (hp0 : p ≠ 0) (hd : 0 < d) :
    gradientSquare p ≠ 0 := by
  intro hzero
  have hpartial : ∀ i, pderiv i p = 0 := by
    intro i
    apply hp.pderiv.eq_zero_of_forall_eval_eq_zero
    intro x
    have heval : ∑ j, (eval x (pderiv j p)) ^ 2 = 0 := by
      simpa [gradientSquare] using congrArg (eval x) hzero
    have hsq : (eval x (pderiv i p)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp heval i (Finset.mem_univ i)
    exact eq_zero_of_pow_eq_zero hsq
  have heuler := hp.sum_X_mul_pderiv
  simp only [hpartial, mul_zero, Finset.sum_const_zero] at heuler
  have hprod : (d : MvPolynomial σ ℝ) * p = 0 := by
    simpa only [nsmul_eq_mul] using heuler.symm
  exact hp0 ((mul_eq_zero.mp hprod).resolve_left
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)))

theorem homogeneous_gradientSquare_totalDegree (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) (hp0 : p ≠ 0) (hd : 0 < d) :
    (gradientSquare p).totalDegree = 2 * d - 2 := by
  have h := (gradientSquare_homogeneous p d hp).totalDegree
    (homogeneous_gradientSquare_ne_zero p d hp hp0 hd)
  have hn : (d - 1) * 2 = 2 * d - 2 := by omega
  exact h.trans hn

theorem homogeneous_gradientSquare_strict_growth (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) (hp0 : p ≠ 0) (hd : 2 < d) :
    p.totalDegree < (gradientSquare p).totalDegree := by
  rw [hp.totalDegree hp0, homogeneous_gradientSquare_totalDegree p d hp hp0 (by omega)]
  omega

omit [Fintype σ] in
theorem monomial_degree_le (p : MvPolynomial σ ℝ) (s : σ →₀ ℕ)
    (hs : p.coeff s ≠ 0) : s.degree ≤ p.totalDegree :=
  le_totalDegree (mem_support_iff.mpr hs)

omit [Fintype σ] in
theorem partial_totalDegree_le (p : MvPolynomial σ ℝ) (i : σ) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro s hs
  have hcoeff : (pderiv i p).coeff s ≠ 0 := mem_support_iff.mp hs
  rw [coeff_pderiv] at hcoeff
  have hsource := monomial_degree_le p (s + Finsupp.single i 1)
    (left_ne_zero_of_mul hcoeff)
  simp only [map_add, Finsupp.degree_single] at hsource
  change s.degree ≤ p.totalDegree - 1
  omega

omit [Fintype σ] in
theorem partial_homogeneousComponent (p : MvPolynomial σ ℝ) (i : σ) (n : ℕ) :
    homogeneousComponent n (pderiv i p) = pderiv i (homogeneousComponent (n + 1) p) := by
  classical
  ext s
  simp [coeff_homogeneousComponent, coeff_pderiv, map_add, Finsupp.degree_single]

omit [Fintype σ] in
/-- At the maximal possible product degree, only the two maximal components contribute. -/
theorem topComponent_mul (p q : MvPolynomial σ ℝ) (m n : ℕ)
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) :
    homogeneousComponent (m + n) (p * q) =
      homogeneousComponent m p * homogeneousComponent n q := by
  classical
  ext s
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases hs : s.degree = m + n
  · simp only [hs, ite_true]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' : ab.1 + ab.2 = s := Finset.mem_antidiagonal.mp hab
    have hdeg : ab.1.degree + ab.2.degree = s.degree := by
      rw [← map_add, hab']
    by_cases ha : p.coeff ab.1 = 0
    · simp [coeff_homogeneousComponent, ha]
    by_cases hb : q.coeff ab.2 = 0
    · simp [coeff_homogeneousComponent, hb]
    have ha' := (monomial_degree_le p ab.1 ha).trans hp
    have hb' := (monomial_degree_le q ab.2 hb).trans hq
    have haeq : ab.1.degree = m := by omega
    have hbeq : ab.2.degree = n := by omega
    simp [coeff_homogeneousComponent, haeq, hbeq]
  · simp only [hs, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro ab hab
    have hab' : ab.1 + ab.2 = s := Finset.mem_antidiagonal.mp hab
    have hdeg : ab.1.degree + ab.2.degree = s.degree := by
      rw [← map_add, hab']
    simp only [coeff_homogeneousComponent]
    split_ifs <;> simp_all

omit [Fintype σ] in
theorem topComponent_ne_zero (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  have hsupport : p.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (by simpa using hp)
  obtain ⟨s, hs, hdeg⟩ := p.support.exists_mem_eq_sup hsupport Finsupp.degree
  have heq : s.degree = p.totalDegree := hdeg.symm
  intro hzero
  have hc := congrArg (fun q : MvPolynomial σ ℝ => q.coeff s) hzero
  simp [coeff_homogeneousComponent, heq, mem_support_iff.mp hs] at hc

theorem gradientSquare_topComponent (p : MvPolynomial σ ℝ) (hd : 0 < p.totalDegree) :
    homogeneousComponent ((p.totalDegree - 1) * 2) (gradientSquare p) =
      gradientSquare (homogeneousComponent p.totalDegree p) := by
  classical
  have hd' : p.totalDegree - 1 + 1 = p.totalDegree := by omega
  have htwo : (p.totalDegree - 1) * 2 =
      (p.totalDegree - 1) + (p.totalDegree - 1) := by omega
  unfold gradientSquare
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [htwo, pow_two, topComponent_mul _ _ _ _
    (partial_totalDegree_le p i) (partial_totalDegree_le p i),
    partial_homogeneousComponent, hd', pow_two]

/-- The squared gradient of every nonconstant real polynomial has exact degree `2d-2`. -/
theorem gradientSquare_totalDegree (p : MvPolynomial σ ℝ) (hd : 0 < p.totalDegree) :
    (gradientSquare p).totalDegree = 2 * p.totalDegree - 2 := by
  classical
  have hp : p ≠ 0 := by intro h; simp [h] at hd
  have htop : homogeneousComponent ((p.totalDegree - 1) * 2) (gradientSquare p) ≠ 0 := by
    rw [gradientSquare_topComponent p hd]
    exact homogeneous_gradientSquare_ne_zero _ _ (homogeneousComponent_isHomogeneous _ _)
      (topComponent_ne_zero p hp) hd
  have hupper : (gradientSquare p).totalDegree ≤ 2 * (p.totalDegree - 1) := by
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (partial_totalDegree_le p i))
  have hlower : (p.totalDegree - 1) * 2 ≤ (gradientSquare p).totalDegree := by
    by_contra h
    exact htop (homogeneousComponent_eq_zero _ _ (Nat.lt_of_not_ge h))
  omega

theorem gradientSquare_strict_growth (p : MvPolynomial σ ℝ) (hd : 2 < p.totalDegree) :
    p.totalDegree < (gradientSquare p).totalDegree := by
  rw [gradientSquare_totalDegree p (by omega)]
  omega

def gradientIter (p : MvPolynomial σ ℝ) : ℕ → MvPolynomial σ ℝ
  | 0 => p
  | n + 1 => gradientSquare (gradientIter p n)

theorem gradientIter_degree_lower (p : MvPolynomial σ ℝ) (hp : 2 < p.totalDegree)
    (n : ℕ) : n + p.totalDegree ≤ (gradientIter p n).totalDegree := by
  induction n with
  | zero => simp [gradientIter]
  | succ n ih =>
    have hg : 2 < (gradientIter p n).totalDegree := by omega
    have hnext := gradientSquare_strict_growth (gradientIter p n) hg
    change n + 1 + p.totalDegree ≤ (gradientSquare (gradientIter p n)).totalDegree
    omega

/-- Uniform boundedness of the degrees of actual squared-gradient iterates forces degree at most two. -/
theorem degree_le_two_of_iterates_bounded (p : MvPolynomial σ ℝ) (N : ℕ)
    (hb : ∀ n, (gradientIter p n).totalDegree ≤ N) : p.totalDegree ≤ 2 := by
  by_contra h
  have hp : 2 < p.totalDegree := by omega
  have hl := gradientIter_degree_lower p hp (N + 1)
  have hu := hb (N + 1)
  omega

/-- Ocone's degree bound after polynomial reconstruction: only closure under
the genuine carré-du-champ operation and one common degree bound are required. -/
theorem degree_le_two_of_gradient_closed (S : Set (MvPolynomial σ ℝ))
    (hclosed : ∀ p ∈ S, gradientSquare p ∈ S) (N : ℕ)
    (hbound : ∀ p ∈ S, p.totalDegree ≤ N) (p : MvPolynomial σ ℝ) (hp : p ∈ S) :
    p.totalDegree ≤ 2 := by
  apply degree_le_two_of_iterates_bounded p N
  intro n
  apply hbound
  induction n with
  | zero => exact hp
  | succ n ih => exact hclosed _ ih

end Wong.PolynomialGradient
