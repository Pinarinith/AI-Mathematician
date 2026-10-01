import Wong.MomentumAxisLadder
import Wong.QuadraticVisibleRigidity

/-! A quadratic transverse shear is incompatible with finite-dimensionality.
The proof uses actual Lie words and retains every scalar remainder. No
membership of the hidden covariant derivative is needed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Wong.SmoothModel
open MvPolynomial

def hiddenShearTime : Smooth := linearFunction (coordinateVector 2)
def hiddenShearMomentum (a b : ℝ) : SmoothSymbol :=
  realCoefficient a * X 0 + realCoefficient b * X 1

def hiddenShearSymbol (a b : ℝ) : SmoothSymbol :=
  C hiddenShearTime ^ 2 * hiddenShearMomentum a b

@[simp] theorem partial_hiddenShearTime (i : Fin 3) :
    partialDerivative i hiddenShearTime = if i = 2 then smoothOne else 0 := by
  fin_cases i <;> simp [hiddenShearTime, partialDerivative_linearFunction, coordinateVector]

@[simp] theorem coefficientDerivative_hiddenShearTime (i : Fin 3) :
    symbolCoefficientDerivative i (C hiddenShearTime) = if i = 2 then 1 else 0 := by
  rw [symbolCoefficientDerivative_C, partial_hiddenShearTime]
  split_ifs <;> simp [smoothOne_eq_one]

@[simp] theorem coefficientDerivative_hiddenShearMomentum (i : Fin 3) (a b : ℝ) :
    symbolCoefficientDerivative i (hiddenShearMomentum a b) = 0 := by
  simp [hiddenShearMomentum, symbolCoefficientDerivative_mul]

@[simp] theorem pderiv_hiddenShearMomentum (i : Fin 3) (a b : ℝ) :
    pderiv i (hiddenShearMomentum a b) =
      if i=0 then realCoefficient a else if i=1 then realCoefficient b else 0 := by
  fin_cases i <;> simp [hiddenShearMomentum]

@[simp] theorem projectMomentumAxis_realCoefficient (r : Fin 3) (a : ℝ) :
    projectMomentumAxis r (realCoefficient a) = realCoefficient a := by
  rw [realCoefficient_apply, projectMomentumAxis_C]

@[simp] theorem coefficientDerivative_two_shear (i : Fin 3) :
    symbolCoefficientDerivative i (2 : SmoothSymbol)=0 := by
  simpa only [map_ofNat] using symbolCoefficientDerivative_realCoefficient i 2

@[simp] theorem coefficientDerivative_four_shear (i : Fin 3) :
    symbolCoefficientDerivative i (4 : SmoothSymbol)=0 := by
  simpa only [map_ofNat] using symbolCoefficientDerivative_realCoefficient i 4

@[simp] theorem coefficientDerivative_eight_shear (i : Fin 3) :
    symbolCoefficientDerivative i (8 : SmoothSymbol)=0 := by
  simpa only [map_ofNat] using symbolCoefficientDerivative_realCoefficient i 8

@[simp] theorem pderiv_two_shear (i : Fin 3) :
    pderiv i (2 : SmoothSymbol)=0 := by
  simpa only [map_ofNat] using pderiv_realCoefficient i 2

/-- The exact principal symbol of the first heat bracket. -/
theorem hiddenShear_heat (a b : ℝ) :
    symbolPoisson axisEuclideanKinetic (hiddenShearSymbol a b) =
      2 * C hiddenShearTime * X 2 * hiddenShearMomentum a b := by
  rw [poisson_axisEuclideanKinetic]
  simp [hiddenShearSymbol, pow_two, symbolCoefficientDerivative_mul, Fin.sum_univ_three]
  ring

/-- The second real bracket has a nonzero positive quadratic symbol. -/
theorem hiddenShear_double (a b : ℝ) :
    symbolPoisson (symbolPoisson axisEuclideanKinetic (hiddenShearSymbol a b))
      (hiddenShearSymbol a b) =
      4 * C hiddenShearTime ^ 2 * hiddenShearMomentum a b ^ 2 := by
  rw [hiddenShear_heat]
  simp [symbolPoisson, symbolFirstCorrection, hiddenShearSymbol,
    pow_two, symbolCoefficientDerivative_mul, Fin.sum_univ_three]
  ring

/-- Its next heat bracket supplies the complete momentum jets for the ladder. -/
theorem hiddenShear_third (a b : ℝ) :
    symbolPoisson axisEuclideanKinetic
      (4 * C hiddenShearTime ^ 2 * hiddenShearMomentum a b ^ 2) =
      8 * C hiddenShearTime * X 2 * hiddenShearMomentum a b ^ 2 := by
  rw [poisson_axisEuclideanKinetic]
  simp [pow_two, symbolCoefficientDerivative_mul, Fin.sum_univ_three]
  ring

theorem shear_C_smul (c : ℝ) (u : Smooth) :
    (C (c • u) : SmoothSymbol) = realCoefficient c * C u := by
  rw [realCoefficient_apply, ← map_mul]
  congr 1
  apply Subtype.ext
  funext z
  simp [smoothOne, smoothMul_eq_mul]

theorem shear_C_time_square (c : ℝ) :
    (C (c • (hiddenShearTime * hiddenShearTime)) : SmoothSymbol) =
      realCoefficient c * C hiddenShearTime ^ 2 := by
  rw [shear_C_smul, map_mul, pow_two]

theorem hiddenShear_project_jets (a b : ℝ) (r : Fin 3) (hr : r ≠ 2) :
    projectMomentumAxis r
      (8 * C hiddenShearTime * X 2 * hiddenShearMomentum a b ^ 2) = 0 ∧
    (∀ i : Fin 3, projectMomentumAxis r
      (pderiv i (8 * C hiddenShearTime * X 2 * hiddenShearMomentum a b ^ 2)) =
      C ((if i=2 then 8 * (![a,b,0] : Fin 3 → ℝ) r ^ 2 else 0) • hiddenShearTime) * X r ^ 2) ∧
    projectMomentumAxis r
      (4 * C hiddenShearTime ^ 2 * hiddenShearMomentum a b ^ 2) =
      C ((4 * (![a,b,0] : Fin 3 → ℝ) r ^ 2) •
        (hiddenShearTime * hiddenShearTime)) * X r ^ 2 := by
  fin_cases r
  · refine ⟨?_, ?_, ?_⟩
    · simp [hiddenShearMomentum]
    · intro i
      fin_cases i <;> simp [hiddenShearMomentum, shear_C_smul,
        map_mul, map_pow, map_ofNat, pow_two] <;> ring
    · simp [hiddenShearMomentum, shear_C_time_square, map_mul, map_pow, map_ofNat]
      ring
  · refine ⟨?_, ?_, ?_⟩
    · simp [hiddenShearMomentum]
    · intro i
      fin_cases i <;> simp [hiddenShearMomentum, shear_C_smul,
        map_mul, map_pow, map_ofNat, pow_two] <;> ring
    · simp [hiddenShearMomentum, shear_C_time_square, map_mul, map_pow, map_ofNat]
      ring
  · exact False.elim (hr rfl)

theorem hiddenShear_transport_eigen (c : ℝ) :
    (∑ i : Fin 3,
      ((if i=2 then 8*c^2 else 0) • hiddenShearTime) *
        partialDerivative i ((4*c^2) • (hiddenShearTime * hiddenShearTime))) =
      (16*c^2) • ((4*c^2) • (hiddenShearTime * hiddenShearTime)) := by
  simp only [map_smul, ← smoothMul_eq_mul, partialDerivative_smoothMul,
    partial_hiddenShearTime, Fin.sum_univ_three]
  apply Subtype.ext
  funext z
  simp [smoothMul, smoothOne]
  ring

theorem hiddenShear_time_square_ne_zero (c : ℝ) (hc : c ≠ 0) :
    (4*c^2) • (hiddenShearTime * hiddenShearTime) ≠ (0 : Smooth) := by
  intro he
  have hz := congrArg (fun u : Smooth => u.1 (coordinateVector 2)) he
  have hc2 : 4*c^2=0 := by
    simpa [hiddenShearTime, linearFunction, coordinateVector, Fin.sum_univ_three, smoothMul_eq_mul] using hz
  exact hc (by nlinarith [sq_nonneg c])

/-- Any actual first-order member with this quadratic transverse shear
principal symbol has both shear coefficients zero. Its scalar is unrestricted. -/
theorem actual_hidden_quadratic_transverse_shear_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (A : NormalForm) (hA : NormalDegreeLE 1 A)
    (hAE : normalAction A ∈ estimationAlgebra f h)
    (a b : ℝ) (hAs : normalSymbol 1 A = hiddenShearSymbol a b) :
    a=0 ∧ b=0 := by
  let L := normalL0 f h
  let B := normalBracket L A
  let Q := normalBracket B A
  let K := normalBracket L Q
  have hL : NormalDegreeLE 2 L := normalDegreeLE_of_action_order _ _ (by
    rw [normalAction_normalL0]; exact L0_mem_orderSpace_two f h)
  have hbr {p q : NormalForm} {n l : ℕ}
      (hp : NormalDegreeLE n p) (hq : NormalDegreeLE l q) :
      NormalDegreeLE (n+l-1) (normalBracket p q) := by
    apply normalDegreeLE_of_action_order
    rw [normalAction_bracket]
    exact lie_mem_orderSpace_sharp (action_order_of_normalDegreeLE p n hp)
      (action_order_of_normalDegreeLE q l hq)
  have hB : NormalDegreeLE 2 B := hbr hL hA
  have hQ : NormalDegreeLE 2 Q := hbr hB hA
  have hK : NormalDegreeLE 3 K := hbr hL hQ
  have hLE : normalAction L ∈ estimationAlgebra f h := by
    rw [normalAction_normalL0]
    exact LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hBE : normalAction B ∈ estimationAlgebra f h := by
    rw [normalAction_bracket]; exact (estimationAlgebra f h).lie_mem hLE hAE
  have hQE : normalAction Q ∈ estimationAlgebra f h := by
    rw [normalAction_bracket]; exact (estimationAlgebra f h).lie_mem hBE hAE
  have hKE : normalAction K ∈ estimationAlgebra f h := by
    rw [normalAction_bracket]; exact (estimationAlgebra f h).lie_mem hLE hQE
  have hBs : normalSymbol 2 B = symbolPoisson axisEuclideanKinetic (hiddenShearSymbol a b) := by
    rw [show 2=1+0+1 from rfl, normalSymbol_bracket L A 1 0 hL hA,
      normalSymbol_normalL0, hAs]
    rfl
  have hQs : normalSymbol 2 Q = 4*C hiddenShearTime^2*hiddenShearMomentum a b^2 := by
    change normalSymbol (1+0+1) Q = _
    rw [normalSymbol_bracket B A 1 0 hB hA,hBs,hAs,hiddenShear_double]
  have hKs : normalSymbol 3 K = 8*C hiddenShearTime*X 2*hiddenShearMomentum a b^2 := by
    change normalSymbol (1+1+1) K = _
    rw [normalSymbol_bracket L Q 1 1 hL hQ,normalSymbol_normalL0,hQs]
    exact hiddenShear_third a b
  have hzero (r : Fin 3) (hr : r≠2) : (![a,b,0] : Fin 3 → ℝ) r=0 := by
    by_contra hc
    let c := (![a,b,0] : Fin 3 → ℝ) r
    have hj := hiddenShear_project_jets a b r hr
    apply actual_momentumAxis_eigen_ladder_obstruction (estimationAlgebra f h)
      r K Q 2 1 (by decide) hKE hQE hK hQ 0 (16*c^2)
      (by dsimp [c]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hc))
      (fun i => (if i=2 then 8*c^2 else 0) • hiddenShearTime)
      ((4*c^2) • (hiddenShearTime*hiddenShearTime))
      (hiddenShear_time_square_ne_zero c hc)
    · simpa only [hKs, zero_smul, map_zero, zero_mul] using hj.1
    · intro i
      simpa only [hKs] using hj.2.1 i
    · simpa only [hQs] using hj.2.2
    · exact hiddenShear_transport_eigen c
  exact ⟨hzero 0 (by decide), hzero 1 (by decide)⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_hidden_quadratic_transverse_shear_zero



/-! An actual order-growth ladder from a hidden Euler principal symbol.
All unrecorded transverse symbols and all scalar remainders are retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Wong.SmoothModel
open MvPolynomial

@[simp] theorem projectHiddenAxis_realCoefficient (c : ℝ) :
    projectHiddenAxis (realCoefficient c) = realCoefficient c := by
  rw [realCoefficient_apply, projectHiddenAxis_C]

theorem projectHiddenAxis_pderiv_two (p : SmoothSymbol) :
    projectHiddenAxis (pderiv 2 p) = pderiv 2 (projectHiddenAxis p) := by
  induction p using MvPolynomial.induction_on with
  | C u => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases hj : j=2
    · simp [map_mul, pderiv_mul, hp, hj]
    · simp [map_mul, pderiv_mul, hp, hj]

/-- Only the hidden coefficient derivative of the retained K symbol is
nonzero. Hence no transverse momentum jet of Q can contribute. -/
theorem hiddenEuler_poisson (k q : SmoothSymbol) (n l : ℕ) (c : ℝ)
    (hk : projectHiddenAxis k = C (linearFunction (coordinateVector 2)) * X 2^(n+1))
    (hq : projectHiddenAxis q = realCoefficient c * X 2^(l+1)) :
    projectHiddenAxis (symbolPoisson k q) =
      realCoefficient (-((l+1 : ℕ) : ℝ)*c) * X 2^(n+l+1) := by
  have hDq (i : Fin 3) : projectHiddenAxis (symbolCoefficientDerivative i q)=0 := by
    rw [projectHiddenAxis_coefficientDerivative, hq]
    simp [symbolCoefficientDerivative_mul]
  have hDk (i : Fin 3) : projectHiddenAxis (symbolCoefficientDerivative i k) =
      if i=2 then X 2^(n+1) else 0 := by
    rw [projectHiddenAxis_coefficientDerivative, hk, coefficientDerivative_hiddenAxisMonomial,
      partialDerivative_linearFunction]
    fin_cases i <;> simp [coordinateVector, smoothOne_eq_one]
  have hPq : projectHiddenAxis (pderiv 2 q) =
      ((l+1 : ℕ) : SmoothSymbol) * realCoefficient c * X 2^l := by
    rw [projectHiddenAxis_pderiv_two, hq]
    simp [pderiv_mul, pderiv_pow, Nat.add_sub_cancel]
    ring
  simp only [symbolPoisson, symbolFirstCorrection, map_sub, map_add, map_mul,
    hDq, mul_zero, Finset.sum_const_zero, zero_sub,
    Fin.sum_univ_three, hDk]
  simp only [show (0 : Fin 3) ≠ 2 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    ite_false, ite_true, zero_mul, zero_add, hPq]
  simp only [map_mul, map_neg, map_natCast]
  have hexp : n+l+1=(n+1)+l := by omega
  rw [hexp, pow_add]
  ring

def hiddenEulerCoefficient (n l : ℕ) : ℕ → ℝ
  | 0 => 1
  | r+1 => -((l+r*n+1 : ℕ) : ℝ)*hiddenEulerCoefficient n l r

theorem hiddenEulerCoefficient_ne_zero (n l r : ℕ) : hiddenEulerCoefficient n l r≠0 := by
  induction r with
  | zero => norm_num [hiddenEulerCoefficient]
  | succ r ih =>
    rw [hiddenEulerCoefficient]
    apply mul_ne_zero _ ih
    apply neg_ne_zero.mpr
    exact_mod_cast (show l+r*n+1≠0 by omega)

theorem hiddenEulerWords_symbol (K Q : NormalForm) (n l : ℕ)
    (hK : NormalDegreeLE (n+1) K) (hQ : NormalDegreeLE (l+1) Q)
    (hk : projectHiddenAxis (normalSymbol (n+1) K) =
      C (linearFunction (coordinateVector 2))*X 2^(n+1))
    (hq : projectHiddenAxis (normalSymbol (l+1) Q) = X 2^(l+1)) (r : ℕ) :
    projectHiddenAxis (normalSymbol (l+r*n+1) (hiddenAxisWords K Q r)) =
      realCoefficient (hiddenEulerCoefficient n l r)*X 2^(l+r*n+1) := by
  induction r with
  | zero => simpa [hiddenAxisWords, hiddenEulerCoefficient] using hq
  | succ r ih =>
    have hh := hiddenEuler_poisson (normalSymbol (n+1) K)
      (normalSymbol (l+r*n+1) (hiddenAxisWords K Q r)) n (l+r*n)
      (hiddenEulerCoefficient n l r) hk ih
    rw [← normalSymbol_bracket K (hiddenAxisWords K Q r) n (l+r*n)
      hK (hiddenAxisWords_order K Q n l hK hQ r)] at hh
    have hi : n+(l+r*n)+1=l+(r+1)*n+1 := by
      simp only [Nat.add_mul, one_mul]
      omega
    simpa only [hiddenAxisWords, hiddenEulerCoefficient, hi] using hh

/-- The true Lie algebra cannot contain these two actual principal symbols.
This is the repaired B1 hidden ladder after the visible slopes have been
independently eliminated; no modulo-order member is introduced. -/
theorem actual_hiddenEuler_order_ladder_obstruction
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (K Q : NormalForm) (n l : ℕ) (hn : 0<n)
    (hKE : normalAction K∈E) (hQE : normalAction Q∈E)
    (hK : NormalDegreeLE (n+1) K) (hQ : NormalDegreeLE (l+1) Q)
    (hk : projectHiddenAxis (normalSymbol (n+1) K) =
      C (linearFunction (coordinateVector 2))*X 2^(n+1))
    (hq : projectHiddenAxis (normalSymbol (l+1) Q) = X 2^(l+1)) : False := by
  obtain ⟨N,hN⟩ := actual_uniform_normal_weight_bound E.toSubmodule (fun α => α.degree)
  have hb : NormalDegreeLE N (hiddenAxisWords K Q N) :=
    hN _ (hiddenAxisWords_mem E K Q hKE hQE N)
  have hNn : N≤N*n := Nat.le_mul_of_pos_right N hn
  have hz := normalSymbol_eq_zero_above_order (hiddenAxisWords K Q N) N (l+N*n+1)
    hb (by omega)
  have hh := hiddenEulerWords_symbol K Q n l hK hQ hk hq N
  rw [hz, map_zero, realCoefficient_apply] at hh
  have hc : hiddenEulerCoefficient n l N • smoothOne ≠ (0 : Smooth) :=
    smul_ne_zero (hiddenEulerCoefficient_ne_zero n l N) (by
      intro he
      have he0 := congrArg (fun u : Smooth => u.1 (0 : State)) he
      simpa [smoothOne] using he0)
  exact hiddenAxisMonomial_ne_zero _ _ hc hh.symm

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_hiddenEuler_order_ladder_obstruction
