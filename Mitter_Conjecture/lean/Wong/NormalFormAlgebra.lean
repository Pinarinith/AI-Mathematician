import Wong.NormalForm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/-!
# Composition and Lie closure of genuine smooth normal forms

Leibniz is implemented by a coefficient derivative plus a multi-index shift.
Composition is built recursively from those operations, and its action is
proved to be actual operator composition. Thus the original estimation
algebra really consists of the faithful normal forms from `NormalForm`.
-/

noncomputable section
namespace Wong.SmoothModel

def normalLeftPartial (i : Fin 3) : NormalForm →ₗ[ℝ] NormalForm :=
  Finsupp.mapRange.linearMap (partialDerivative i) +
    Finsupp.lmapDomain Smooth ℝ (fun α => α + Finsupp.single i 1)

def normalLeftMultiplier (u : Smooth) : NormalForm →ₗ[ℝ] NormalForm :=
  Finsupp.mapRange.linearMap (multiplication u)

@[simp] theorem normalLeftPartial_single (i : Fin 3) (α : MultiIndex) (u : Smooth) :
    normalLeftPartial i (Finsupp.single α u) =
      Finsupp.single α (partialDerivative i u) + Finsupp.single (α + Finsupp.single i 1) u := by
  change Finsupp.mapRange (partialDerivative i) (map_zero _) (Finsupp.single α u) +
    Finsupp.mapDomain (fun β => β + Finsupp.single i 1) (Finsupp.single α u) = _
  rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]

@[simp] theorem normalLeftMultiplier_single (u v : Smooth) (α : MultiIndex) :
    normalLeftMultiplier u (Finsupp.single α v) = Finsupp.single α (smoothMul u v) := by
  change Finsupp.mapRange (multiplication u) (map_zero _) (Finsupp.single α v) = _
  rw [Finsupp.mapRange_single]
  rfl

theorem multiPartial_shift (α : MultiIndex) (i : Fin 3) :
    multiPartial (α + Finsupp.single i 1) = partialDerivative i * multiPartial α := by
  have h10 : Commute (partialDerivative 1) (partialDerivative 0) := partialDerivative_commute 1 0
  have h20 : Commute (partialDerivative 2) (partialDerivative 0) := partialDerivative_commute 2 0
  have h21 : Commute (partialDerivative 2) (partialDerivative 1) := partialDerivative_commute 2 1
  fin_cases i
  · simp [multiPartial, pow_succ', mul_assoc]
  · simp only [multiPartial, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    rw [pow_succ']
    calc
      _ = (partialDerivative 0 ^ α 0 * partialDerivative 1) *
          (partialDerivative 1 ^ α 1 * partialDerivative 2 ^ α 2) := by simp [mul_assoc]
      _ = (partialDerivative 1 * partialDerivative 0 ^ α 0) *
          (partialDerivative 1 ^ α 1 * partialDerivative 2 ^ α 2) := by rw [(h10.pow_right (α 0)).eq]
      _ = _ := by simp [mul_assoc]
  · simp only [multiPartial, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    rw [pow_succ']
    have hc := (h20.pow_right (α 0)).mul_right (h21.pow_right (α 1))
    calc
      _ = (partialDerivative 0 ^ α 0 * partialDerivative 1 ^ α 1) *
          partialDerivative 2 * partialDerivative 2 ^ α 2 := by simp [mul_assoc]
      _ = (partialDerivative 2 * (partialDerivative 0 ^ α 0 * partialDerivative 1 ^ α 1)) *
          partialDerivative 2 ^ α 2 := by rw [hc.eq]
      _ = _ := by simp [mul_assoc]

theorem partial_mul_multiplication (i : Fin 3) (u : Smooth) :
    partialDerivative i * multiplication u =
      multiplication (partialDerivative i u) + multiplication u * partialDerivative i := by
  have hh := lie_partial_multiplication i u
  change partialDerivative i * multiplication u - multiplication u * partialDerivative i =
    multiplication (partialDerivative i u) at hh
  exact sub_eq_iff_eq_add.mp hh

theorem normalAction_leftPartial (i : Fin 3) (p : NormalForm) :
    normalAction (normalLeftPartial i p) = partialDerivative i * normalAction p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq, mul_add]
  | single α u =>
    rw [normalLeftPartial_single, map_add, normalAction_single, normalAction_single,
      normalAction_single, multiPartial_shift,
      ← mul_assoc (partialDerivative i) (multiplication u), partial_mul_multiplication]
    noncomm_ring

theorem normalAction_leftMultiplier (u : Smooth) (p : NormalForm) :
    normalAction (normalLeftMultiplier u p) = multiplication u * normalAction p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq, mul_add]
  | single α v =>
    simp [← multiplication_mul, mul_assoc]

theorem normalAction_leftPartial_power (i : Fin 3) (n : ℕ) (p : NormalForm) :
    normalAction ((normalLeftPartial i ^ n) p) = partialDerivative i ^ n * normalAction p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : (normalLeftPartial i ^ (n + 1)) p =
        normalLeftPartial i ((normalLeftPartial i ^ n) p) := by rw [pow_succ']; rfl
    rw [hs, normalAction_leftPartial, ih, pow_succ']
    simp [mul_assoc]

def normalLeftMultiPartial (α : MultiIndex) : NormalForm →ₗ[ℝ] NormalForm :=
  normalLeftPartial 0 ^ α 0 * normalLeftPartial 1 ^ α 1 * normalLeftPartial 2 ^ α 2

theorem normalAction_leftMultiPartial (α : MultiIndex) (p : NormalForm) :
    normalAction (normalLeftMultiPartial α p) = multiPartial α * normalAction p := by
  change normalAction ((normalLeftPartial 0 ^ α 0)
    ((normalLeftPartial 1 ^ α 1) ((normalLeftPartial 2 ^ α 2) p))) = _
  rw [normalAction_leftPartial_power, normalAction_leftPartial_power,
    normalAction_leftPartial_power]
  simp [multiPartial, mul_assoc]

def normalCompose (p q : NormalForm) : NormalForm :=
  p.sum fun α u => normalLeftMultiplier u (normalLeftMultiPartial α q)

theorem normalAction_compose (p q : NormalForm) :
    normalAction (normalCompose p q) = normalAction p * normalAction q := by
  classical
  simp only [normalCompose, Finsupp.sum, map_sum, normalAction_leftMultiplier,
    normalAction_leftMultiPartial]
  have hp : normalAction p = p.sum (fun α u => multiplication u * multiPartial α) := rfl
  rw [hp]
  simp only [Finsupp.sum, Finset.sum_mul, mul_assoc]

theorem normalCompose_assoc (p q r : NormalForm) :
    normalCompose (normalCompose p q) r = normalCompose p (normalCompose q r) := by
  apply normalAction_injective
  simp only [normalAction_compose, mul_assoc]

def normalBracket (p q : NormalForm) : NormalForm := normalCompose p q - normalCompose q p

theorem normalAction_bracket (p q : NormalForm) :
    normalAction (normalBracket p q) = ⁅normalAction p, normalAction q⁆ := by
  rw [normalBracket, map_sub normalAction, normalAction_compose, normalAction_compose, operator_lie_def]

@[simp] theorem multiPartial_zero : multiPartial 0 = (1 : Operator) := by simp [multiPartial]

@[simp] theorem normalAction_scalar (u : Smooth) :
    normalAction (Finsupp.single 0 u) = multiplication u := by simp

@[simp] theorem normalAction_partial (i : Fin 3) :
    normalAction (Finsupp.single (Finsupp.single i 1) smoothOne) = partialDerivative i := by
  rw [normalAction_single, multiplication_smoothOne, one_mul]
  simpa using multiPartial_shift 0 i

def normalD (f : Fin 3 → Smooth) (i : Fin 3) : NormalForm :=
  Finsupp.single (Finsupp.single i 1) smoothOne - Finsupp.single 0 (f i)

@[simp] theorem normalAction_normalD (f : Fin 3 → Smooth) (i : Fin 3) :
    normalAction (normalD f i) = D f i := by rw [normalD, map_sub normalAction, normalAction_partial, normalAction_scalar, D]

def normalL0 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) : NormalForm :=
  (1 / 2 : ℝ) • (∑ i, normalCompose (normalD f i) (normalD f i)) -
    (1 / 2 : ℝ) • Finsupp.single 0 (eta f h)

@[simp] theorem normalAction_normalL0 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    normalAction (normalL0 f h) = L0 f h := by
  rw [normalL0, map_sub normalAction, map_smul, map_smul, map_sum, normalAction_scalar]
  simp only [normalAction_compose, normalAction_normalD, L0]

/-- Actual actions of finite normal forms form a Lie subalgebra. -/
def normalFormOperators : LieSubalgebra ℝ Operator where
  carrier := Set.range normalAction
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro A B ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, map_add _ _ _⟩
  smul_mem' := by
    rintro c A ⟨p, rfl⟩
    exact ⟨c • p, map_smul _ _ _⟩
  lie_mem' := by
    rintro A B ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨normalBracket p q, normalAction_bracket p q⟩

theorem estimationAlgebra_le_normalFormOperators {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    estimationAlgebra f h ≤ normalFormOperators := by
  apply LieSubalgebra.lieSpan_le.mpr
  intro A hA
  rcases hA with hA | ⟨j, rfl⟩
  · rcases hA with rfl
    exact ⟨normalL0 f h, normalAction_normalL0 f h⟩
  · exact ⟨Finsupp.single 0 (h j), normalAction_scalar _⟩

/-- Every element of the original estimation algebra has one unique finite
normal form, proved from the actual smooth actions and Lie generators. -/
theorem estimationAlgebra_unique_normalForm {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (A : Operator) (hA : A ∈ estimationAlgebra f h) :
    ∃! p : NormalForm, normalAction p = A := by
  obtain ⟨p, hp⟩ := estimationAlgebra_le_normalFormOperators f h hA
  exact ⟨p, hp, fun q hq => normalAction_injective (hq.trans hp.symm)⟩

end Wong.SmoothModel
