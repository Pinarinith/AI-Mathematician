import Wong.PureHiddenSymbols

/-!
# The genuine high-degree hidden Lie ladder

All normal forms below act on the original global smooth function space.
Principal terms are transported through the proved actual bracket formula.
-/
noncomputable section
namespace Wong.SmoothModel
set_option maxHeartbeats 1600000

def ladderHiddenCoordinate : Smooth := linearFunction (coordinateVector 2)

@[simp] theorem partial_ladderHiddenCoordinate :
    partialDerivative 2 ladderHiddenCoordinate = (1 : Smooth) := by
  simp [ladderHiddenCoordinate, partialDerivative_linearFunction, coordinateVector]

theorem partial_hidden_coordinate_pow_succ (n : ℕ) :
    partialDerivative 2 (ladderHiddenCoordinate ^ (n + 1)) =
      (n + 1 : ℝ) • ladderHiddenCoordinate ^ n := by
  have he := (smoothPartialDerivation 2).leibniz_pow ladderHiddenCoordinate (n + 1)
  simp only [smoothPartialDerivation_apply, partial_ladderHiddenCoordinate,
    Nat.add_sub_cancel, smul_eq_mul, mul_one] at he
  rw [he]
  apply Subtype.ext
  funext x
  simp [smooth_coe_natCast, nsmul_eq_mul]

theorem hidden_derivative_power_self (n : ℕ) :
    (partialDerivative 2 ^ n) (ladderHiddenCoordinate ^ n) = (Nat.factorial n : ℝ) • (1 : Smooth) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, partial_hidden_coordinate_pow_succ, map_smul, ih,
      smul_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

theorem pure_hidden_principal_not_lower (p : NormalForm) (n k : ℕ) (u : Smooth)
    (hp : HasPureHiddenPrincipal n u p) (hu : u ≠ 0) (hkn : k < n) :
    normalAction p ∉ orderSpace k := by
  intro horder
  have hl := normalDegreeLE_of_action_order p k horder
  have hz := normalSymbol_zero_of_lower_order p k n hl hkn
  rw [hp.2] at hz
  have hcoeff := congrArg (fun q : SmoothSymbol => q.coeff (Finsupp.single 2 n)) hz
  apply hu
  simpa [pureHiddenSymbol] using hcoeff

def hiddenHeatNormal : NormalForm := Finsupp.single (Finsupp.single 2 2) (1 : Smooth)

@[simp] theorem normalAction_hiddenHeat :
    normalAction hiddenHeatNormal = partialDerivative 2 ^ 2 := by
  rw [show hiddenHeatNormal = normalHiddenHead 2 1 by
    simp only [hiddenHeatNormal, normalHiddenHead, one_smul, smoothOne_eq_one]]
  simp only [normalAction_hiddenHead, one_smul]

theorem hiddenHeat_principal : HasPureHiddenPrincipal 2 1 hiddenHeatNormal :=
  pure_hidden_principal_single 2 1

theorem hiddenHeat_bracket_principal (p : NormalForm) (n : ℕ) (u : Smooth)
    (hp : HasPureHiddenPrincipal (n + 1) u p) :
    HasPureHiddenPrincipal (n + 2) ((2 : ℝ) • partialDerivative 2 u)
      (normalBracket hiddenHeatNormal p) := by
  have hh := pure_hidden_principal_bracket hiddenHeatNormal p 1 n 1 u hiddenHeat_principal hp
  have hcoeff : (1 : Smooth) * (1 + 1 : ℕ) * partialDerivative 2 u -
      u * (n + 1 : ℕ) * partialDerivative 2 1 = (2 : ℝ) • partialDerivative 2 u := by
    have hone : partialDerivative 2 (1 : Smooth) = 0 := by
      simpa using partialDerivative_const 2 1
    rw [hone, mul_zero, sub_zero, one_mul]
    change (2 : Smooth) * partialDerivative 2 u = (2 : ℝ) • partialDerivative 2 u
    rw [two_mul, two_smul]
  simpa only [show 1 + n + 1 = n + 2 by omega, hcoeff] using hh

def hiddenHeatIterate (p : NormalForm) : ℕ → NormalForm
  | 0 => p
  | r + 1 => normalBracket hiddenHeatNormal (hiddenHeatIterate p r)

theorem hiddenHeatIterate_mem (E : LieSubalgebra ℝ Operator)
    (hheat : partialDerivative 2 ^ 2 ∈ E) (p : NormalForm) (hp : normalAction p ∈ E) :
    ∀r, normalAction (hiddenHeatIterate p r) ∈ E := by
  intro r
  induction r with
  | zero => exact hp
  | succ r ih =>
    simp only [hiddenHeatIterate, normalAction_bracket, normalAction_hiddenHeat]
    exact E.lie_mem hheat ih

theorem hiddenHeatIterate_principal (p : NormalForm) (n : ℕ) (u : Smooth)
    (hp : HasPureHiddenPrincipal (n + 1) u p) (r : ℕ) :
    HasPureHiddenPrincipal (n + r + 1)
      ((2 : ℝ) ^ r • (partialDerivative 2 ^ r) u) (hiddenHeatIterate p r) := by
  induction r with
  | zero => simpa [hiddenHeatIterate] using hp
  | succ r ih =>
    have hh := hiddenHeat_bracket_principal (hiddenHeatIterate p r) (n + r)
      ((2 : ℝ) ^ r • (partialDerivative 2 ^ r) u) ih
    simpa only [hiddenHeatIterate, map_smul, smul_smul, pow_succ', Module.End.mul_apply,
      show n + r + 2 = n + (r + 1) + 1 by omega] using hh

def highEulerNormal (a : ℝ) (d : ℕ) (q : Smooth) : NormalForm :=
  Finsupp.single (Finsupp.single 2 1) (-a • ladderHiddenCoordinate ^ (d + 2)) +
    Finsupp.single 0 q

@[simp] theorem normalAction_highEulerNormal (a : ℝ) (d : ℕ) (q : Smooth) :
    normalAction (highEulerNormal a d q) =
      multiplication (-a • ladderHiddenCoordinate ^ (d + 2)) * partialDerivative 2 +
        multiplication q := by
  rw [highEulerNormal, map_add, normalAction_single, normalAction_single]
  have hfirst : multiPartial (Finsupp.single 2 1) = partialDerivative 2 := by
    simp [multiPartial]
  have hzero : multiPartial 0 = (1 : Operator) := by simp [multiPartial]
  rw [hfirst, hzero, mul_one]

theorem highEulerNormal_principal (a : ℝ) (d : ℕ) (q : Smooth) :
    HasPureHiddenPrincipal 1 (-a • ladderHiddenCoordinate ^ (d + 2))
      (highEulerNormal a d q) := by
  apply pure_hidden_principal_add_lower _ _ 0 _ (pure_hidden_principal_single 1 _)
  intro α hα
  have hne : (0 : MultiIndex) ≠ α := by
    intro he
    rw [← he, map_zero] at hα
    omega
  simp [hne]

theorem principal_constant_double_bracket (T P : NormalForm) (m : ℕ) (b : Smooth)
    (hT : HasPureHiddenPrincipal 1 b T) (hP : HasPureHiddenPrincipal (m + 2) 1 P) :
    HasPureHiddenPrincipal (2 * m + 3)
      (-((m + 2 : ℝ) ^ 2) • partialDerivative 2 (partialDerivative 2 b))
      (normalBracket P (normalBracket T P)) := by
  have hone : partialDerivative 2 (1 : Smooth) = 0 := by
    simpa using partialDerivative_const 2 1
  have hfirst := pure_hidden_principal_bracket T P 0 (m + 1) b 1 hT hP
  have hfirstcoeff : b * (0 + 1 : ℕ) * partialDerivative 2 1 -
      (1 : Smooth) * (m + 1 + 1 : ℕ) * partialDerivative 2 b =
        -(m + 2 : ℝ) • partialDerivative 2 b := by
    rw [hone, mul_zero, zero_sub, one_mul]
    apply Subtype.ext
    funext x
    simp [smooth_coe_natCast]
    ring
  have hfirst' : HasPureHiddenPrincipal (m + 2)
      (-(m + 2 : ℝ) • partialDerivative 2 b) (normalBracket T P) := by
    simpa only [hfirstcoeff, zero_add, show m + 1 + 1 = m + 2 by omega] using hfirst
  have hsecond := pure_hidden_principal_bracket P (normalBracket T P)
    (m + 1) (m + 1) 1 (-(m + 2 : ℝ) • partialDerivative 2 b) hP hfirst'
  have hsecondcoeff : (1 : Smooth) * (m + 1 + 1 : ℕ) *
      partialDerivative 2 (-(m + 2 : ℝ) • partialDerivative 2 b) -
      (-(m + 2 : ℝ) • partialDerivative 2 b) * (m + 1 + 1 : ℕ) *
        partialDerivative 2 1 =
      (-((m + 2 : ℝ) ^ 2)) • partialDerivative 2 (partialDerivative 2 b) := by
    rw [hone, mul_zero, sub_zero, one_mul, map_smul]
    apply Subtype.ext
    funext x
    simp [smooth_coe_natCast]
    ring
  simpa only [hsecondcoeff, show m + 1 + (m + 1) + 1 = 2 * m + 3 by omega] using hsecond

theorem highEuler_double_bracket_principal (a : ℝ) (d m : ℕ) (q : Smooth) (P : NormalForm)
    (hP : HasPureHiddenPrincipal (m + 2) 1 P) :
    HasPureHiddenPrincipal (2 * m + 3)
      (((m + 2 : ℝ) ^ 2 * a * (d + 2 : ℝ) * (d + 1 : ℝ)) •
        ladderHiddenCoordinate ^ d)
      (normalBracket P (normalBracket (highEulerNormal a d q) P)) := by
  have hh := principal_constant_double_bracket (highEulerNormal a d q) P m
    (-a • ladderHiddenCoordinate ^ (d + 2)) (highEulerNormal_principal a d q) hP
  have hcoeff : -((m + 2 : ℝ) ^ 2) •
      partialDerivative 2 (partialDerivative 2 (-a • ladderHiddenCoordinate ^ (d + 2))) =
      (((m + 2 : ℝ) ^ 2 * a * (d + 2 : ℝ) * (d + 1 : ℝ)) •
        ladderHiddenCoordinate ^ d) := by
    rw [map_smul, show d + 2 = (d + 1) + 1 by omega, partial_hidden_coordinate_pow_succ,
      map_smul, map_smul, partial_hidden_coordinate_pow_succ]
    simp only [smul_smul]
    congr 1
    push_cast
    ring
  rwa [hcoeff] at hh

def highEulerLadderScalar (a : ℝ) (d m : ℕ) : ℝ :=
  (2 : ℝ) ^ d * ((m + 2 : ℝ) ^ 2 * a * (d + 2 : ℝ) * (d + 1 : ℝ)) * (Nat.factorial d : ℝ)

theorem highEulerLadderScalar_ne_zero (a : ℝ) (ha : a ≠ 0) (d m : ℕ) :
    highEulerLadderScalar a d m ≠ 0 := by
  unfold highEulerLadderScalar
  apply mul_ne_zero
  · apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by positivity)) ha)
      (by positivity)) (by positivity)
  · exact_mod_cast Nat.factorial_ne_zero d

theorem highEuler_ladder_step_principal (a : ℝ) (d m : ℕ) (q : Smooth) (P : NormalForm)
    (hP : HasPureHiddenPrincipal (m + 2) 1 P) :
    HasPureHiddenPrincipal (2 * m + d + 3) (highEulerLadderScalar a d m • (1 : Smooth))
      (hiddenHeatIterate (normalBracket P (normalBracket (highEulerNormal a d q) P)) d) := by
  have hh := hiddenHeatIterate_principal
    (normalBracket P (normalBracket (highEulerNormal a d q) P)) (2 * m + 2)
    (((m + 2 : ℝ) ^ 2 * a * (d + 2 : ℝ) * (d + 1 : ℝ)) • ladderHiddenCoordinate ^ d)
    (highEuler_double_bracket_principal a d m q P hP) d
  simpa only [map_smul, hidden_derivative_power_self, smul_smul, highEulerLadderScalar,
    show 2 * m + 2 + d + 1 = 2 * m + d + 3 by omega, mul_assoc] using hh

/-- A nonzero hidden polynomial drift of degree at least two, together
with the actual hidden heat operator, contradicts finite dimensionality. -/
theorem highEuler_ladder_obstruction (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (a : ℝ) (d : ℕ) (q : Smooth)
    (hheat : partialDerivative 2 ^ 2 ∈ E)
    (hT : normalAction (highEulerNormal a d q) ∈ E) : a = 0 := by
  by_contra ha
  have hstep (m : ℕ) (P : NormalForm) (hP : HasPureHiddenPrincipal (m + 2) 1 P)
      (hPE : normalAction P ∈ E) :
      ∃Q : NormalForm, HasPureHiddenPrincipal ((2 * m + d + 1) + 2) 1 Q ∧
        normalAction Q ∈ E := by
    let R := hiddenHeatIterate (normalBracket P (normalBracket (highEulerNormal a d q) P)) d
    let c := highEulerLadderScalar a d m
    have hc : c ≠ 0 := highEulerLadderScalar_ne_zero a ha d m
    refine ⟨c⁻¹ • R, ?_, ?_⟩
    · have hh := pure_hidden_principal_smul R (2 * m + d + 3) (c • (1 : Smooth)) c⁻¹
        (highEuler_ladder_step_principal a d m q P hP)
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul,
        show 2 * m + d + 3 = (2 * m + d + 1) + 2 by omega] using hh
    · rw [map_smul]
      apply E.smul_mem
      apply hiddenHeatIterate_mem E hheat
      rw [normalAction_bracket, normalAction_bracket]
      exact E.lie_mem hPE (E.lie_mem hT hPE)
  have hex (r : ℕ) : ∃m : ℕ, r ≤ m ∧ ∃P : NormalForm,
      HasPureHiddenPrincipal (m + 2) 1 P ∧ normalAction P ∈ E := by
    induction r with
    | zero => exact ⟨0, le_rfl, hiddenHeatNormal, hiddenHeat_principal, by
        simpa only [normalAction_hiddenHeat] using hheat⟩
    | succ r ih =>
      obtain ⟨m, hm, P, hP, hPE⟩ := ih
      obtain ⟨Q, hQ, hQE⟩ := hstep m P hP hPE
      exact ⟨2 * m + d + 1, by omega, Q, hQ, hQE⟩
  obtain ⟨N, hN⟩ := finiteDimensional_uniform_order_bound E.toSubmodule (fun P hP => hfinite hP)
  obtain ⟨m, hm, P, hP, hPE⟩ := hex N
  apply pure_hidden_principal_not_lower P (m + 2) N 1 hP _ (by omega) (hN hPE)
  intro he
  have hz := congrArg (fun u : Smooth => u.1 (0 : State)) he
  norm_num at hz

theorem actual_highEuler_ladder_obstruction
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (a : ℝ) (d : ℕ) (q : Smooth)
    (hheat : partialDerivative 2 ^ 2 ∈ E)
    (hT : multiplication (-a • ladderHiddenCoordinate ^ (d + 2)) * partialDerivative 2 +
      multiplication q ∈ E) : a = 0 := by
  apply highEuler_ladder_obstruction E hfinite a d q hheat
  simpa only [normalAction_highEulerNormal] using hT

end Wong.SmoothModel
