import Wong.SmoothBrackets
import Wong.Affine
import Mathlib.Analysis.Calculus.MeanValue

/-! Constancy criteria for the actual smooth Wong matrix. -/

noncomputable section
namespace Wong.SmoothModel

theorem fderiv_eq_zero_of_partials_eq_zero (u : Smooth)
    (hu : ∀ i, partialDerivative i u = 0) (x : State) : fderiv ℝ u.1 x = 0 := by
  ext v
  have hv : v = ∑ i : Fin 3, v i • coordinateVector i := by
    funext j
    simp [coordinateVector, Pi.single_apply, Finset.sum_apply, mul_ite]
  rw [hv, map_sum]
  change (∑ i : Fin 3, fderiv ℝ u.1 x (v i • coordinateVector i)) = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  have hi := congrArg (fun w : Smooth => w.1 x) (hu i)
  change fderiv ℝ u.1 x (coordinateVector i) = 0 at hi
  rw [hi, smul_zero]

theorem smooth_constant_iff_partials_zero (u : Smooth) :
    (∃ c : ℝ, ∀ x : State, u.1 x = c) ↔ ∀ i, partialDerivative i u = 0 := by
  constructor
  · rintro ⟨c, hc⟩ i
    have hfun : u.1 = fun _ : State => c := funext hc
    apply Subtype.ext
    funext x
    change fderiv ℝ u.1 x (coordinateVector i) = 0
    rw [hfun]
    simp
  · intro hu
    refine ⟨u.1 0, ?_⟩
    intro x
    exact is_const_of_fderiv_eq_zero ((smooth u).differentiable (by simp))
      (fderiv_eq_zero_of_partials_eq_zero u hu) x 0

/-- A derivative formulation of precisely the requested conclusion. -/
theorem wongConstant_iff_partials_zero (f : Fin 3 → Smooth) :
    WongConstant f ↔ ∀ i j k, partialDerivative k (wong f i j) = 0 := by
  constructor
  · rintro ⟨Ω, hΩ⟩ i j
    exact (smooth_constant_iff_partials_zero _).mp ⟨Ω i j, hΩ i j⟩
  · intro h
    refine ⟨fun i j => (wong f i j).1 0, ?_⟩
    intro i j x
    obtain ⟨c, hc⟩ := (smooth_constant_iff_partials_zero _).mpr (h i j)
    exact (hc x).trans (hc 0).symm

@[simp] theorem wong_self (f : Fin 3 → Smooth) (i : Fin 3) : wong f i i = 0 := by
  simp [wong]

theorem wong_skew (f : Fin 3 → Smooth) (i j : Fin 3) :
    wong f j i = -wong f i j := by
  simp [wong, neg_sub]

/-- A supplied actual affine representation is constant exactly when its
eight slopes vanish. The representation and vanishing are not assumed to
follow from finite dimensionality in this lemma. -/
theorem wongConstant_iff_affine_zero_slopes (f : Fin 3 → Smooth)
    (p : Wong.AffineParameters)
    (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    WongConstant f ↔ p.ZeroSlopes := by
  rw [← Wong.affine_constancy_iff_zero_slopes]
  constructor
  · rintro ⟨Ω, hΩ⟩ x y
    ext i j
    rw [← hform i j x, ← hform i j y, hΩ, hΩ]
  · intro h
    refine ⟨p.matrix 0, ?_⟩
    intro i j x
    rw [hform, h x 0]

end Wong.SmoothModel
