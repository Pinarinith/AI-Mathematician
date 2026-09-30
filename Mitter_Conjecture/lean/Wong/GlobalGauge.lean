import Wong.Gauge
import Wong.CovariantWords
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Global smooth gauge potentials on actual real three-space

The Poincaré lemma is a proved Mathlib theorem, applied to an actual
continuous-linear-valued one-form on the convex open set `Set.univ`.
Smoothness of its primitive is recovered from its specified smooth
Fréchet derivative. No potential-existence oracle is added.
-/

noncomputable section
namespace Wong.SmoothModel
open scoped ContDiff

def smoothCovector (a : Fin 3 → Smooth) (x : State) : State →L[ℝ] ℝ :=
  ∑ i, (a i).1 x • (ContinuousLinearMap.proj i : State →L[ℝ] ℝ)

theorem contDiff_smoothCovector (a : Fin 3 → Smooth) :
    ContDiff ℝ ∞ (smoothCovector a) := by
  apply ContDiff.sum
  intro i _
  exact (smooth (a i)).smul contDiff_const

theorem smoothCovector_coordinate (a : Fin 3 → Smooth) (i : Fin 3) (x : State) :
    smoothCovector a x (coordinateVector i) = (a i).1 x := by
  simp [smoothCovector, coordinateVector, Pi.single_apply, mul_ite]

theorem fderiv_smoothCovector_coordinate (a : Fin 3 → Smooth) (x v : State)
    (i : Fin 3) :
    fderiv ℝ (smoothCovector a) x v (coordinateVector i) = fderiv ℝ (a i).1 x v := by
  have he : (fun y => smoothCovector a y (coordinateVector i)) = (a i).1 :=
    funext (smoothCovector_coordinate a i)
  have hd := fderiv_clm_apply (x := x)
    (((contDiff_smoothCovector a).differentiable (by simp)).differentiableAt)
    (differentiableAt_const (coordinateVector i))
  have hv := congrArg (fun T : State →L[ℝ] ℝ => T v) hd
  simpa only [he, fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using hv.symm

theorem fderiv_smoothCovector_symmetric (a : Fin 3 → Smooth)
    (hclosed : ∀ i j, partialDerivative i (a j) = partialDerivative j (a i))
    (x v w : State) :
    fderiv ℝ (smoothCovector a) x v w = fderiv ℝ (smoothCovector a) x w v := by
  have hexp (z : State) : z = ∑ i, z i • coordinateVector i := by
    funext j
    simp [coordinateVector, Pi.single_apply]
  have hb (i j : Fin 3) :
      fderiv ℝ (smoothCovector a) x (coordinateVector i) (coordinateVector j) =
      fderiv ℝ (smoothCovector a) x (coordinateVector j) (coordinateVector i) := by
    rw [fderiv_smoothCovector_coordinate, fderiv_smoothCovector_coordinate]
    exact congrArg (fun u : Smooth => u.1 x) (hclosed i j)
  calc
    _ = ∑ j, ∑ i, w j * (v i *
        fderiv ℝ (smoothCovector a) x (coordinateVector i) (coordinateVector j)) := by
      conv_lhs => rw [hexp v, hexp w]
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        smul_eq_mul, Finset.mul_sum]
    _ = ∑ i, ∑ j, v i * (w j *
        fderiv ℝ (smoothCovector a) x (coordinateVector j) (coordinateVector i)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hb i j]
      ring
    _ = _ := by
      conv_rhs => rw [hexp w, hexp v]
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        smul_eq_mul, Finset.mul_sum]

theorem exists_smooth_potential_of_closed (a : Fin 3 → Smooth)
    (hclosed : ∀ i j, partialDerivative i (a j) = partialDerivative j (a i)) :
    ∃ Λ : Smooth, ∀ i, partialDerivative i Λ = a i := by
  obtain ⟨F, hF⟩ := Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric
    (convex_univ : Convex ℝ (Set.univ : Set State)) isOpen_univ
      ((contDiff_smoothCovector a).differentiable (by simp)).differentiableOn
      (fun x _ v w => fderiv_smoothCovector_symmetric a hclosed x v w)
  have hf (x : State) : HasFDerivAt F (smoothCovector a x) x := hF x (Set.mem_univ x)
  have hdf : fderiv ℝ F = smoothCovector a := funext (fun x => (hf x).fderiv)
  have hcont : ContDiff ℝ ∞ F := contDiff_infty_iff_fderiv.mpr
    ⟨fun x => (hf x).differentiableAt, by rw [hdf]; exact contDiff_smoothCovector a⟩
  refine ⟨⟨F, hcont⟩, ?_⟩
  intro i
  apply Subtype.ext
  funext x
  change fderiv ℝ F x (coordinateVector i) = (a i).1 x
  rw [(hf x).fderiv, smoothCovector_coordinate]

/-- Equality of the actual Wong tensors gives a genuine global gauge,
not merely a local or formal polynomial potential. -/
theorem exists_gaugeDrift_of_wong_eq (f g : Fin 3 → Smooth)
    (hcurvature : ∀ i j, wong f i j = wong g i j) :
    ∃ Λ : Smooth, gaugeDrift Λ f = g := by
  let a : Fin 3 → Smooth := fun i => g i - f i
  have hclosed : ∀ i j, partialDerivative i (a j) = partialDerivative j (a i) := by
    intro i j
    have he := hcurvature i j
    simp only [wong] at he
    dsimp [a]
    simp only [map_sub]
    apply sub_eq_sub_iff_add_eq_add.mpr
    exact (sub_eq_sub_iff_add_eq_add.mp he).symm.trans (add_comm _ _)
  obtain ⟨Λ, hΛ⟩ := exists_smooth_potential_of_closed a hclosed
  refine ⟨Λ, ?_⟩
  funext i
  simp only [gaugeDrift, hΛ i, a]
  abel

theorem gaugeConjugation_filteringOperator (f : Fin 3 → Smooth) (V Λ : Smooth) :
    gaugeConjugation Λ (filteringOperator f V) = filteringOperator (gaugeDrift Λ f) V := by
  simp only [filteringOperator, map_sub, map_smul, map_sum, map_mul,
    gaugeConjugation_D, gaugeConjugation_multiplication]

end Wong.SmoothModel
