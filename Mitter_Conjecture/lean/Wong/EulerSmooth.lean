import Wong.EulerSystem
import Wong.FunctionElements
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Genuine smooth Euler equations and polynomial functions

The finite-dimensional companion system is an actual curve in Euclidean
space. Polynomiality follows from the proved dissipative Euler-system
argument, not from an assumed absence of flat solutions.
-/

noncomputable section
namespace Wong.EulerSmooth
open scoped ContDiff

/-- Continuous linear maps commute with all ordinary derivatives of a smooth curve. -/
theorem iteratedDeriv_clm {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K] (A : H →L[ℝ] K) (V : ℝ → H)
    (hV : ContDiff ℝ ∞ V) (n : ℕ) :
    iteratedDeriv n (fun t => A (V t)) = fun t => A (iteratedDeriv n V t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [iteratedDeriv_succ]
    have hs : ContDiff ℝ ∞ (iteratedDeriv n V) := by
      rw [iteratedDeriv_eq_iterate]
      exact hV.iterate_deriv n
    exact (A.hasFDerivAt.comp_hasDerivAt t
      ((hs.differentiable (by simp)) t).hasDerivAt).deriv

/-- Every component of a finite, genuinely smooth Euler system is polynomial. -/
theorem polynomial_of_finite_euler_system {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (g : ι → ℝ → ℝ)
    (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (he : ∀ i t, t * deriv (g i) t = ∑ j, a i j * g j t) :
    ∀ i, ∃ p : Polynomial ℝ, ∀ t, p.eval t = g i t := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := EuclideanSpace.equiv ι ℝ
  let M : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi (fun i => ∑ j, a i j • ContinuousLinearMap.proj j)
  let A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    e.symm.toContinuousLinearMap.comp (M.comp e.toContinuousLinearMap)
  let V : ℝ → EuclideanSpace ℝ ι := fun t => e.symm (fun i => g i t)
  have hV : ContDiff ℝ ∞ V := e.symm.contDiff.comp (contDiff_pi.mpr hg)
  have hder (t : ℝ) : deriv V t = e.symm (fun i => deriv (g i) t) := by
    apply HasDerivAt.deriv
    apply e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    apply hasDerivAt_pi.mpr
    intro i
    exact ((hg i).differentiable (by simp) t).hasDerivAt
  have hsys : ∀ t, t • deriv V t = A (V t) := by
    intro t
    apply e.injective
    rw [map_smul, hder]
    simp only [A, V, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    simpa only [M, ContinuousLinearMap.pi_apply, sum_apply,
      smul_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply,
      smul_eq_mul] using he i t
  obtain ⟨m, hm, hzero⟩ := Wong.EulerSystem.exists_iteratedDeriv_eq_zero A V hV hsys
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  intro i
  let pr : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have hgi : (fun t => pr (V t)) = g i := by
    funext t
    simp [pr, V]
  have hi : iteratedDeriv (n + 1) (g i) = 0 := by
    rw [← hgi, iteratedDeriv_clm pr V hV, hzero]
    funext t
    simp
  obtain ⟨p, _, hp⟩ := Wong.FunctionElements.polynomial_of_iteratedDeriv_eq_zero
    n (g i) (hg i) hi
  exact ⟨p, hp⟩

/-- Powers of the genuine Euler differential operator `t d/dt`. -/
def eulerIterate (f : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => f
  | n + 1 => fun t => t * deriv (eulerIterate f n) t

theorem eulerIterate_smooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (eulerIterate f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact contDiff_id.mul (contDiff_infty_iff_deriv.mp ih).2

/-- The usual polynomial in the Euler operator, written as its finite sum
of actual iterated differential operators on the given smooth function. -/
def eulerPolynomialAction (Q : Polynomial ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * eulerIterate f k t

/-- A globally smooth function annihilated by a nonzero polynomial in
`t d/dt` is an actual ordinary real polynomial function. The proof includes
the singular point and both half-lines, with no flat-solution hypothesis. -/
theorem polynomial_of_euler_annihilator (Q : Polynomial ℝ) (hQ : Q ≠ 0)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hzero : eulerPolynomialAction Q f = 0) :
    ∃ p : Polynomial ℝ, ∀ t, p.eval t = f t := by
  have hc : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  by_cases hd : Q.natDegree = 0
  · refine ⟨0, ?_⟩
    intro t
    have ht := congrFun hzero t
    simp only [eulerPolynomialAction, hd, Nat.zero_add, Finset.sum_range_one,
      eulerIterate, Pi.zero_apply] at ht
    have hc0 : Q.coeff 0 ≠ 0 := by simpa only [hd] using hc
    have hft : f t = 0 := (mul_eq_zero.mp ht).resolve_left hc0
    simp only [hft, Polynomial.eval_zero]
  · have hdpos : 0 < Q.natDegree := Nat.pos_of_ne_zero hd
    let c : Fin Q.natDegree → ℝ := fun j => -Q.coeff j / Q.coeff Q.natDegree
    have htop (t : ℝ) : eulerIterate f Q.natDegree t =
        ∑ j : Fin Q.natDegree, c j * eulerIterate f j t := by
      have ht := congrFun hzero t
      simp only [eulerPolynomialAction, Finset.sum_range_succ, Pi.zero_apply] at ht
      apply mul_left_cancel₀ hc
      rw [Finset.mul_sum]
      have hcj (j : Fin Q.natDegree) : Q.coeff Q.natDegree *
          (c j * eulerIterate f j t) = -Q.coeff j * eulerIterate f j t := by
        dsimp [c]
        field_simp [Polynomial.leadingCoeff_ne_zero.mpr hQ]
      simp_rw [hcj, neg_mul, Finset.sum_neg_distrib]
      rw [Fin.sum_univ_eq_sum_range (fun k => Q.coeff k * eulerIterate f k t) Q.natDegree]
      linarith
    let a : Fin Q.natDegree → Fin Q.natDegree → ℝ := fun i j =>
      if hi : i.val + 1 < Q.natDegree then
        if j = ⟨i.val + 1, hi⟩ then 1 else 0
      else c j
    let g : Fin Q.natDegree → ℝ → ℝ := fun i => eulerIterate f i.val
    have hsys (i : Fin Q.natDegree) (t : ℝ) :
        t * deriv (g i) t = ∑ j, a i j * g j t := by
      change eulerIterate f (i.val + 1) t = _
      by_cases hi : i.val + 1 < Q.natDegree
      · simp [a, hi, g, ite_mul]
      · have hlast : i.val + 1 = Q.natDegree := by omega
        simpa only [a, dite_eq_right hi, g, hlast] using htop t
    obtain ⟨p, hp⟩ := polynomial_of_finite_euler_system a g
      (fun i => eulerIterate_smooth f hf i.val) hsys ⟨0, hdpos⟩
    exact ⟨p, hp⟩

/-- A finite Euler matrix gives a uniform ordinary derivative order for
all its globally smooth solutions. -/
theorem uniform_nilpotence_of_finite_euler_system {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) :
    ∃ n : ℕ, 0 < n ∧ ∀ g : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (g i)) →
      (∀ i t, t * deriv (g i) t = ∑ j, a i j * g j t) →
      ∀ i, iteratedDeriv n (g i) = 0 := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := EuclideanSpace.equiv ι ℝ
  let M : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi (fun i => ∑ j, a i j • ContinuousLinearMap.proj j)
  let A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    e.symm.toContinuousLinearMap.comp (M.comp e.toContinuousLinearMap)
  obtain ⟨n, hn, hnil⟩ := Wong.EulerSystem.uniform_iteratedDeriv_eq_zero A
  refine ⟨n, hn, ?_⟩
  intro g hg he i
  let V : ℝ → EuclideanSpace ℝ ι := fun t => e.symm (fun i => g i t)
  have hV : ContDiff ℝ ∞ V := e.symm.contDiff.comp (contDiff_pi.mpr hg)
  have hder (t : ℝ) : deriv V t = e.symm (fun i => deriv (g i) t) := by
    apply HasDerivAt.deriv
    apply e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    apply hasDerivAt_pi.mpr
    intro i
    exact ((hg i).differentiable (by simp) t).hasDerivAt
  have hsys : ∀ t, t • deriv V t = A (V t) := by
    intro t
    apply e.injective
    rw [map_smul, hder]
    simp only [A, V, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    simpa only [M, ContinuousLinearMap.pi_apply, sum_apply,
      smul_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply,
      smul_eq_mul] using he i t
  have hzero := hnil V hV hsys
  let pr : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have hgi : (fun t => pr (V t)) = g i := by
    funext t
    simp [pr, V]
  rw [← hgi, iteratedDeriv_clm pr V hV, hzero]
  funext t
  simp

/-- One nonzero Euler polynomial gives a common ordinary derivative bound
for all globally smooth functions it annihilates. -/
theorem uniform_nilpotence_of_euler_annihilator (Q : Polynomial ℝ) (hQ : Q ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f →
      eulerPolynomialAction Q f = 0 → iteratedDeriv n f = 0 := by
  have hc : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  by_cases hd : Q.natDegree = 0
  · refine ⟨1, by omega, ?_⟩
    intro f hf hzero
    have hfzero : f = 0 := by
      funext t
      have ht := congrFun hzero t
      simp only [eulerPolynomialAction, hd, Nat.zero_add, Finset.sum_range_one,
        eulerIterate, Pi.zero_apply] at ht
      have hc0 : Q.coeff 0 ≠ 0 := by simpa only [hd] using hc
      exact (mul_eq_zero.mp ht).resolve_left hc0
    rw [hfzero]
    simp
  · have hdpos : 0 < Q.natDegree := Nat.pos_of_ne_zero hd
    let c : Fin Q.natDegree → ℝ := fun j => -Q.coeff j / Q.coeff Q.natDegree
    let a : Fin Q.natDegree → Fin Q.natDegree → ℝ := fun i j =>
      if hi : i.val + 1 < Q.natDegree then
        if j = ⟨i.val + 1, hi⟩ then 1 else 0
      else c j
    obtain ⟨n, hn, hnil⟩ := uniform_nilpotence_of_finite_euler_system a
    refine ⟨n, hn, ?_⟩
    intro f hf hzero
    have htop (t : ℝ) : eulerIterate f Q.natDegree t =
        ∑ j : Fin Q.natDegree, c j * eulerIterate f j t := by
      have ht := congrFun hzero t
      simp only [eulerPolynomialAction, Finset.sum_range_succ, Pi.zero_apply] at ht
      apply mul_left_cancel₀ hc
      rw [Finset.mul_sum]
      have hcj (j : Fin Q.natDegree) : Q.coeff Q.natDegree *
          (c j * eulerIterate f j t) = -Q.coeff j * eulerIterate f j t := by
        dsimp [c]
        field_simp [Polynomial.leadingCoeff_ne_zero.mpr hQ]
      simp_rw [hcj, neg_mul, Finset.sum_neg_distrib]
      rw [Fin.sum_univ_eq_sum_range (fun k => Q.coeff k * eulerIterate f k t) Q.natDegree]
      linarith
    let g : Fin Q.natDegree → ℝ → ℝ := fun i => eulerIterate f i.val
    have hsys (i : Fin Q.natDegree) (t : ℝ) :
        t * deriv (g i) t = ∑ j, a i j * g j t := by
      change eulerIterate f (i.val + 1) t = _
      by_cases hi : i.val + 1 < Q.natDegree
      · simp [a, hi, g, ite_mul]
      · have hlast : i.val + 1 = Q.natDegree := by omega
        simpa only [a, dite_eq_right hi, g, hlast] using htop t
    exact hnil g (fun i => eulerIterate_smooth f hf i.val) hsys ⟨0, hdpos⟩

end Wong.EulerSmooth
