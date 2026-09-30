import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Smooth Euler systems are polynomial

A bounded linear Euler system `t • V'(t) = A (V(t))` has no smooth
nonpolynomial solutions. Ordinary differentiation shifts A by minus an
integer. Beyond the operator norm, the shifted system is dissipative;
its nonnegative energy decreases away from zero on both half-lines.
This excludes all nonzero high derivatives without assuming flatness,
using a logarithmic coordinate, or invoking an ODE classification.
-/

noncomputable section
namespace Wong.EulerSystem
open scoped ContDiff
open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Smoothness is preserved by every ordinary iterated derivative. -/
theorem smooth_iteratedDeriv (V : ℝ → H) (hV : ContDiff ℝ ∞ V) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n V) := by
  rw [iteratedDeriv_eq_iterate]
  exact hV.iterate_deriv n

/-- Differentiating an Euler system n times shifts its coefficient by n. -/
theorem iteratedDeriv_euler_system (A : H →L[ℝ] H) (V : ℝ → H)
    (hV : ContDiff ℝ ∞ V) (he : ∀ t, t • deriv V t = A (V t)) (n : ℕ) :
    ∀ t, t • deriv (iteratedDeriv n V) t =
      A (iteratedDeriv n V t) - (n : ℝ) • iteratedDeriv n V t := by
  induction n with
  | zero => simpa using he
  | succ n ih =>
    intro t
    let W := iteratedDeriv n V
    have hW : ContDiff ℝ ∞ W := smooth_iteratedDeriv V hV n
    have hWd : ContDiff ℝ ∞ (deriv W) := (contDiff_infty_iff_deriv.mp hW).2
    have hleft : HasDerivAt (fun s : ℝ => s • deriv W s)
        (deriv W t + t • deriv (deriv W) t) t := by
      simpa only [Pi.smul_def', id_eq, one_smul, add_comm] using (hasDerivAt_id t).smul
        ((hWd.differentiable (by simp)) t).hasDerivAt
    have hright : HasDerivAt (fun s : ℝ => A (W s) - (n : ℝ) • W s)
        (A (deriv W t) - (n : ℝ) • deriv W t) t := by
      exact (A.hasFDerivAt.comp_hasDerivAt t
        ((hW.differentiable (by simp)) t).hasDerivAt).sub
          (((hW.differentiable (by simp)) t).hasDerivAt.const_smul (n : ℝ))
    have hfun : (fun s : ℝ => s • deriv W s) =
        (fun s : ℝ => A (W s) - (n : ℝ) • W s) := funext ih
    rw [hfun] at hleft
    have hd := hleft.unique hright
    rw [iteratedDeriv_succ]
    change t • deriv (deriv W) t = A (deriv W t) - ((n + 1 : ℕ) : ℝ) • deriv W t
    calc
      t • deriv (deriv W) t = (deriv W t + t • deriv (deriv W) t) - deriv W t := by abel
      _ = (A (deriv W t) - (n : ℝ) • deriv W t) - deriv W t := by rw [hd]
      _ = A (deriv W t) - ((n + 1 : ℕ) : ℝ) • deriv W t := by
        rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
        abel

/-- A shift beyond the operator norm leaves only the zero smooth solution.
This is a proved global uniqueness statement, including the singular point. -/
theorem shifted_euler_system_eq_zero (A : H →L[ℝ] H) (c : ℝ) (hc : ‖A‖ < c)
    (W : ℝ → H) (hW : Differentiable ℝ W)
    (he : ∀ t, t • deriv W t = A (W t) - c • W t) : W = 0 := by
  let e : ℝ → ℝ := fun t => inner ℝ (W t) (W t)
  have hnonneg (t : ℝ) : 0 ≤ e t := real_inner_self_nonneg
  have hdiff : Differentiable ℝ e := hW.inner ℝ hW
  have hder (t : ℝ) : deriv e t = 2 * inner ℝ (W t) (deriv W t) := by
    rw [deriv_inner_apply ℝ (hW t) (hW t), real_inner_comm (deriv W t) (W t)]
    ring
  have hbound (t : ℝ) : t * deriv e t ≤ 2 * (‖A‖ - c) * e t := by
    rw [hder]
    have hid : t * (2 * inner ℝ (W t) (deriv W t)) =
        2 * (inner ℝ (W t) (A (W t)) - c * e t) := by
      calc
        t * (2 * inner ℝ (W t) (deriv W t)) =
            2 * inner ℝ (W t) (t • deriv W t) := by rw [inner_smul_right]; ring
        _ = 2 * (inner ℝ (W t) (A (W t)) - c * e t) := by
          rw [he, inner_sub_right, inner_smul_right]
    rw [hid]
    have hinner : inner ℝ (W t) (A (W t)) ≤ ‖A‖ * e t := by
      have hi := real_inner_le_norm (W t) (A (W t))
      have ha := A.le_opNorm (W t)
      have hm := mul_le_mul_of_nonneg_left ha (norm_nonneg (W t))
      have hn : e t = ‖W t‖ ^ 2 := real_inner_self_eq_norm_sq (W t)
      rw [hn]
      nlinarith
    nlinarith
  have he0 : e 0 = 0 := by
    have hb := hbound 0
    have hn := hnonneg 0
    nlinarith
  have hanti : AntitoneOn e (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn
    intro t ht
    have htpos : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    have hb := hbound t
    have hn := hnonneg t
    have hr : 2 * (‖A‖ - c) * e t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hn
    nlinarith
  have hmono : MonotoneOn e (Iic 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn
    intro t ht
    have htneg : t < 0 := by simpa only [interior_Iic, mem_Iio] using ht
    have hb := hbound t
    have hn := hnonneg t
    have hr : 2 * (‖A‖ - c) * e t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hn
    nlinarith
  funext t
  have heq : e t = 0 := by
    apply le_antisymm _ (hnonneg t)
    rcases le_total 0 t with ht | ht
    · simpa only [he0] using hanti (show 0 ∈ Ici (0 : ℝ) by simp) ht ht
    · simpa only [he0] using hmono ht (show 0 ∈ Iic (0 : ℝ) by simp) ht
  exact (inner_self_eq_zero.mp heq)

/-- A genuine globally smooth bounded-linear Euler system has a vanishing
ordinary derivative of finite positive order. No flatness condition is assumed. -/
theorem exists_iteratedDeriv_eq_zero (A : H →L[ℝ] H) (V : ℝ → H)
    (hV : ContDiff ℝ ∞ V) (he : ∀ t, t • deriv V t = A (V t)) :
    ∃ m : ℕ, 0 < m ∧ iteratedDeriv m V = 0 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (‖A‖ + 1)
  have hm0 : 0 < m := by
    have hn := norm_nonneg A
    exact_mod_cast (show (0 : ℝ) < m by linarith)
  refine ⟨m, hm0, shifted_euler_system_eq_zero A (m : ℝ) (by linarith) _
    ((smooth_iteratedDeriv V hV m).differentiable (by simp)) ?_⟩
  exact iteratedDeriv_euler_system A V hV he m

/-- The vanishing order depends only on the bounded linear Euler system,
not on its particular globally smooth solution. -/
theorem uniform_iteratedDeriv_eq_zero (A : H →L[ℝ] H) :
    ∃ m : ℕ, 0 < m ∧ ∀ V : ℝ → H, ContDiff ℝ ∞ V →
      (∀ t, t • deriv V t = A (V t)) → iteratedDeriv m V = 0 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (‖A‖ + 1)
  have hm0 : 0 < m := by
    have hn := norm_nonneg A
    exact_mod_cast (show (0 : ℝ) < m by linarith)
  refine ⟨m, hm0, ?_⟩
  intro V hV he
  exact shifted_euler_system_eq_zero A (m : ℝ) (by linarith) _
    ((smooth_iteratedDeriv V hV m).differentiable (by simp))
    (iteratedDeriv_euler_system A V hV he m)

end Wong.EulerSystem
