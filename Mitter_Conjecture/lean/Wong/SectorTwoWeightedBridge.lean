import Wong.WeightedCanonicalBridge
import Wong.SectorTwoSymbolLift

/-! Consolidated actual canonical sector-II weighted calculus and low-degree
ladder. The three API compatibility wrappers import this single module. -/





/-! Chain rules for the faithful four-variable sector-II lift, proved on
constants and variables and extended by the actual Leibniz identities. -/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

@[simp] theorem sectorTwoSymbolLift_X0 :
    sectorTwoSymbolLift (X 0) = C (linearFunction (coordinateVector 0)) :=
  sectorTwoSymbolLift_X 0

@[simp] theorem sectorTwoSymbolLift_X1 :
    sectorTwoSymbolLift (X 1) = C (linearFunction (coordinateVector 2)) :=
  sectorTwoSymbolLift_X 1

@[simp] theorem sectorTwoSymbolLift_X2 : sectorTwoSymbolLift (X 2) = (X 0 : SmoothSymbol) :=
  sectorTwoSymbolLift_X 2

@[simp] theorem sectorTwoSymbolLift_X3 : sectorTwoSymbolLift (X 3) = (X 2 : SmoothSymbol) :=
  sectorTwoSymbolLift_X 3

theorem sectorTwoSymbolLift_derivative
    (D : SmoothSymbol →ₗ[ℝ] SmoothSymbol)
    (hC : ∀c : ℝ,D (C (c • smoothOne))=0)
    (hmul : ∀p q,D (p*q)=D p*q+p*D q)
    (j : Fin 4)
    (hX : ∀i : Fin 4,D (sectorTwoSymbolLift (X i))=sectorTwoSymbolLift (pderiv j (X i)))
    (p : Wong.SectorTwo.Symbols) :
    D (sectorTwoSymbolLift p)=sectorTwoSymbolLift (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [sectorTwoSymbolLift_C, hC, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, hmul, pderiv_mul, map_add, map_mul, map_mul, hp, hX]

theorem sectorTwoSymbolLift_derivative_zero
    (D : SmoothSymbol →ₗ[ℝ] SmoothSymbol)
    (hC : ∀c : ℝ,D (C (c • smoothOne))=0)
    (hmul : ∀p q,D (p*q)=D p*q+p*D q)
    (hX : ∀i : Fin 4,D (sectorTwoSymbolLift (X i))=0)
    (p : Wong.SectorTwo.Symbols) : D (sectorTwoSymbolLift p)=0 := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [sectorTwoSymbolLift_C, hC]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p i hp => rw [map_mul, hmul, hp, hX, zero_mul, mul_zero, add_zero]

theorem sectorTwoSymbolLift_position_zero (p : Wong.SectorTwo.Symbols) :
    symbolCoefficientDerivative 0 (sectorTwoSymbolLift p)=sectorTwoSymbolLift (pderiv 0 p) := by
  apply sectorTwoSymbolLift_derivative (symbolCoefficientDerivative 0)
    (fun c => by rw [symbolCoefficientDerivative_C, partialDerivative_const, map_zero])
    (symbolCoefficientDerivative_mul 0) 0 _ p
  intro i
  fin_cases i <;> simp [sectorTwoSymbolLift_X0, sectorTwoSymbolLift_X1, sectorTwoSymbolLift_X2, sectorTwoSymbolLift_X3, symbolCoefficientDerivative_C,
    partialDerivative_linearFunction, coordinateVector, smoothOne_eq_one]

theorem sectorTwoSymbolLift_position_one (p : Wong.SectorTwo.Symbols) :
    symbolCoefficientDerivative 1 (sectorTwoSymbolLift p)=0 := by
  apply sectorTwoSymbolLift_derivative_zero (symbolCoefficientDerivative 1)
    (fun c => by rw [symbolCoefficientDerivative_C, partialDerivative_const, map_zero])
    (symbolCoefficientDerivative_mul 1) _ p
  intro i
  fin_cases i <;> simp [sectorTwoSymbolLift_X0, sectorTwoSymbolLift_X1, sectorTwoSymbolLift_X2, sectorTwoSymbolLift_X3, symbolCoefficientDerivative_C,
    partialDerivative_linearFunction, coordinateVector]

theorem sectorTwoSymbolLift_position_two (p : Wong.SectorTwo.Symbols) :
    symbolCoefficientDerivative 2 (sectorTwoSymbolLift p)=sectorTwoSymbolLift (pderiv 1 p) := by
  apply sectorTwoSymbolLift_derivative (symbolCoefficientDerivative 2)
    (fun c => by rw [symbolCoefficientDerivative_C, partialDerivative_const, map_zero])
    (symbolCoefficientDerivative_mul 2) 1 _ p
  intro i
  fin_cases i <;> simp [sectorTwoSymbolLift_X0, sectorTwoSymbolLift_X1, sectorTwoSymbolLift_X2, sectorTwoSymbolLift_X3, symbolCoefficientDerivative_C,
    partialDerivative_linearFunction, coordinateVector, smoothOne_eq_one]

theorem sectorTwoSymbolLift_momentum_zero (p : Wong.SectorTwo.Symbols) :
    pderiv 0 (sectorTwoSymbolLift p)=sectorTwoSymbolLift (pderiv 2 p) := by
  apply sectorTwoSymbolLift_derivative ((pderiv (0 : Fin 3) : Derivation Smooth SmoothSymbol SmoothSymbol).toLinearMap.restrictScalars ℝ)
    (fun c => by simp) (fun p q => by exact pderiv_mul) 2 _ p
  intro i
  fin_cases i <;> simp [sectorTwoSymbolLift_X0, sectorTwoSymbolLift_X1, sectorTwoSymbolLift_X2, sectorTwoSymbolLift_X3]

theorem sectorTwoSymbolLift_momentum_one (p : Wong.SectorTwo.Symbols) :
    pderiv 1 (sectorTwoSymbolLift p)=0 := by
  apply sectorTwoSymbolLift_derivative_zero ((pderiv (1 : Fin 3) : Derivation Smooth SmoothSymbol SmoothSymbol).toLinearMap.restrictScalars ℝ)
    (fun c => by simp) (fun p q => by exact pderiv_mul) _ p
  intro i
  fin_cases i <;> simp [sectorTwoSymbolLift_X0, sectorTwoSymbolLift_X1, sectorTwoSymbolLift_X2, sectorTwoSymbolLift_X3]

theorem sectorTwoSymbolLift_momentum_two (p : Wong.SectorTwo.Symbols) :
    pderiv 2 (sectorTwoSymbolLift p)=sectorTwoSymbolLift (pderiv 3 p) := by
  apply sectorTwoSymbolLift_derivative ((pderiv (2 : Fin 3) : Derivation Smooth SmoothSymbol SmoothSymbol).toLinearMap.restrictScalars ℝ)
    (fun c => by simp) (fun p q => by exact pderiv_mul) 3 _ p
  intro i
  fin_cases i <;> simp [sectorTwoSymbolLift_X0, sectorTwoSymbolLift_X1, sectorTwoSymbolLift_X2, sectorTwoSymbolLift_X3]

/-- The actual quadratic hidden coordinate profile. -/
def quadraticHiddenProfile (a : ℝ) : Smooth :=
  a • (linearFunction (coordinateVector 2) * linearFunction (coordinateVector 2))

theorem partialDerivative_quadraticHiddenProfile (a : ℝ) :
    partialDerivative 2 (quadraticHiddenProfile a) =
      (2*a) • linearFunction (coordinateVector 2) := by
  rw [quadraticHiddenProfile, map_smul]
  change a • partialDerivative 2
    (smoothMul (linearFunction (coordinateVector 2)) (linearFunction (coordinateVector 2))) = _
  rw [partialDerivative_smoothMul, partialDerivative_linearFunction]
  simp only [coordinateVector, Pi.single_eq_same, one_smul, smoothMul_eq_mul, smoothOne_eq_one,
    one_mul, mul_one, smul_add]
  module

/-- The highest weighted transport is precisely the published four-variable
derivation. This is proved from the real smooth coordinate derivatives. -/
theorem sectorTwoSymbolLift_dynamics (a k : ℝ) (F : Smooth)
    (hF0 : partialDerivative 0 F=k • linearFunction (coordinateVector 0))
    (hF2 : partialDerivative 2 F=0) (p : Wong.SectorTwo.Symbols) :
    canonicalWeightedTransport F (quadraticHiddenProfile a) (sectorTwoSymbolLift p) =
      sectorTwoSymbolLift (Wong.SectorTwo.dynamics a k p) := by
  rw [canonicalWeightedTransport, kineticWeightedTransport, verticalWeightedTransport,
    hiddenWeightedTransport, Fin.sum_univ_three, Fin.sum_univ_three,
    sectorTwoSymbolLift_position_zero, sectorTwoSymbolLift_position_one,
    sectorTwoSymbolLift_position_two, sectorTwoSymbolLift_momentum_zero,
    sectorTwoSymbolLift_momentum_one, sectorTwoSymbolLift_momentum_two, hF0, hF2,
    partialDerivative_quadraticHiddenProfile]
  simp only [map_zero, mul_zero, zero_mul, add_zero]
  rw [Wong.SectorTwo.dynamics_apply]
  simp only [map_add, map_sub, map_mul, map_pow, sectorTwoSymbolLift_C, sectorTwoSymbolLift_X0, sectorTwoSymbolLift_X1, sectorTwoSymbolLift_X2, sectorTwoSymbolLift_X3]
  simp only [quadraticHiddenProfile, Algebra.smul_def, map_mul, smoothOne_eq_one, mul_one,
    map_ofNat, map_one]
  ring

end Wong.SmoothModel


/-!
# The actual sector-II weighted ladder for quadratic hidden profiles

The recursive words are genuine commutators of the canonical smooth operator
and ∂₀. Their errors relative to the proved polynomial derivation are bounded
in the actual derivative-nilpotence filtration. Finite dimensionality then
contradicts the independently proved nonzero highest weighted components.
-/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

def sectorTwoCanonicalWords (l : SmoothSymbol) : ℕ → SmoothSymbol
  | 0 => X 0
  | n+1 => symbolBracket l (sectorTwoCanonicalWords l n)

theorem sectorTwoCanonicalWords_mem (E : LieSubalgebra ℝ Operator)
    (l : SmoothSymbol) (hl : normalQuantize l∈E) (hx : partialDerivative 0∈E) (n : ℕ) :
    normalQuantize (sectorTwoCanonicalWords l n)∈E := by
  induction n with
  | zero => simpa only [sectorTwoCanonicalWords, normalQuantize_X] using hx
  | succ n ih =>
    rw [sectorTwoCanonicalWords, normalQuantize_symbolBracket]
    exact E.lie_mem hl ih

theorem sectorTwoCanonicalWords_order (g F ε V r : Smooth)
    (hg : HiddenDegreeLE 0 g) (hF : HiddenDegreeLE 0 F)
    (hε : HiddenDegreeLE 2 ε) (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (hV : HiddenDegreeLE 1 V) (hr : HiddenDegreeLE 2 r)
    (hrvis : ∀i : Fin 3,i≠2 → partialDerivative i r=0) (n : ℕ) :
    WeightedSymbolOrderLE (n+1)
      (sectorTwoCanonicalWords (canonicalWeightedSymbol g F ε V r) n) := by
  induction n with
  | zero =>
    simpa [sectorTwoCanonicalWords, momentumCoordinateWeight] using WeightedSymbolOrderLE.X 0
  | succ n ih =>
    have hh := canonicalWeightedSymbol_bracket_order g F ε V r 2 (by norm_num)
      hg hF hε hεvis hV hr hrvis _ (n+1) ih
    simp only [Nat.cast_add, Nat.cast_one]
    exact hh.mono (by omega)

/-- Replacing ε by its actual quadratic part changes the highest action by
at most W_n when the difference has genuine hidden degree at most one. -/
theorem canonicalWeightedTransport_profile_error (F ε ε₀ : Smooth)
    (hε : HiddenDegreeLE 1 (ε-ε₀)) (p : SmoothSymbol) (n : ℤ)
    (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE n
      (canonicalWeightedTransport F ε p-canonicalWeightedTransport F ε₀ p) := by
  have he : canonicalWeightedTransport F ε p-canonicalWeightedTransport F ε₀ p =
      -hiddenWeightedTransport (ε-ε₀) p := by
    rw [hiddenWeightedTransport_sub]
    unfold canonicalWeightedTransport
    ring
  rw [he]
  simpa using (weighted_hidden_transport_order (ε-ε₀) 1 hε p n hp).neg

/-- The exact nth actual Lie word has the genuine polynomial nth top term,
with a strictly smaller weighted remainder. -/
theorem sectorTwoCanonicalWords_top (g F ε V r : Smooth) (a k : ℝ)
    (hg : HiddenDegreeLE 0 g) (hF : HiddenDegreeLE 0 F)
    (hε : HiddenDegreeLE 2 ε) (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (hV : HiddenDegreeLE 1 V) (hr : HiddenDegreeLE 2 r)
    (hrvis : ∀i : Fin 3,i≠2 → partialDerivative i r=0)
    (hF0 : partialDerivative 0 F=k • linearFunction (coordinateVector 0))
    (hF2 : partialDerivative 2 F=0)
    (hεtop : HiddenDegreeLE 1 (ε-quadraticHiddenProfile a)) (n : ℕ) :
    WeightedSymbolOrderLE n
      (sectorTwoCanonicalWords (canonicalWeightedSymbol g F ε V r) n -
        sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[n] (X 2))) := by
  induction n with
  | zero =>
    simp only [sectorTwoCanonicalWords, Function.iterate_zero, id_eq, sectorTwoSymbolLift_X2, sub_self]
    exact WeightedSymbolOrderLE.zero _
  | succ n ih =>
    let q := sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[n] (X 2))
    have hq : WeightedSymbolOrderLE (n+1) q := sectorTwoSymbolLift_momentum_order a k n
    have h₁ := canonicalWeightedSymbol_bracket_order g F ε V r 2 (by norm_num)
      hg hF hε hεvis hV hr hrvis _ n ih
    have h₂ := canonicalWeightedSymbol_transport_error g F ε V r
      hg hF hε hεvis hV hr hrvis q (n+1) hq
    have h₃ := canonicalWeightedTransport_profile_error F ε (quadraticHiddenProfile a)
      hεtop q (n+1) hq
    have he :
        sectorTwoCanonicalWords (canonicalWeightedSymbol g F ε V r) (n+1) -
          sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[n+1] (X 2)) =
        symbolBracket (canonicalWeightedSymbol g F ε V r)
          (sectorTwoCanonicalWords (canonicalWeightedSymbol g F ε V r) n-q) +
        (symbolBracket (canonicalWeightedSymbol g F ε V r) q-canonicalWeightedTransport F ε q) +
        (canonicalWeightedTransport F ε q-canonicalWeightedTransport F (quadraticHiddenProfile a) q) := by
      rw [sectorTwoCanonicalWords, Function.iterate_succ_apply',
        symbolBracket_sub_right, sectorTwoSymbolLift_dynamics a k F hF0 hF2]
      dsimp only [q]
      abel
    rw [he]
    have hh : WeightedSymbolOrderLE (n+1) _ :=
      ((h₁.mono (by omega)).add h₂).add h₃
    simpa only [Nat.cast_add, Nat.cast_one] using hh

/-- A finite-dimensional actual Lie algebra cannot contain this canonical
sector-II operator and ∂₀ when k≠0 and the hidden profiles have degree≤2. -/
theorem sectorTwo_quadratic_actual_obstruction (E : LieSubalgebra ℝ Operator)
    [FiniteDimensional ℝ E] (g F ε V r : Smooth) (a k : ℝ) (hk : k≠0)
    (hL : canonicalWeightedOperator g F ε V r∈E) (hx : partialDerivative 0∈E)
    (hg : HiddenDegreeLE 0 g) (hF : HiddenDegreeLE 0 F)
    (hε : HiddenDegreeLE 2 ε) (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (hV : HiddenDegreeLE 1 V) (hr : HiddenDegreeLE 2 r)
    (hrvis : ∀i : Fin 3,i≠2 → partialDerivative i r=0)
    (hF0 : partialDerivative 0 F=k • linearFunction (coordinateVector 0))
    (hF2 : partialDerivative 2 F=0)
    (hεtop : HiddenDegreeLE 1 (ε-quadraticHiddenProfile a)) : False := by
  obtain ⟨N,hN⟩ := actual_uniform_weighted_symbol_bound E.toSubmodule
  let p := sectorTwoCanonicalWords (canonicalWeightedSymbol g F ε V r) N
  have hpE : normalQuantize p∈E := sectorTwoCanonicalWords_mem E _
    (by simpa only [normalQuantize_canonicalWeightedSymbol] using hL) hx N
  have hpw : WeightedSymbolOrderLE (N+1) p :=
    sectorTwoCanonicalWords_order g F ε V r hg hF hε hεvis hV hr hrvis N
  have hp : WeightedSymbolOrderLE N p := hN p hpE ⟨N+1, by
    simpa only [Nat.cast_add, Nat.cast_one] using hpw⟩
  have htop := sectorTwoCanonicalWords_top g F ε V r a k hg hF hε hεvis hV hr hrvis
    hF0 hF2 hεtop N
  have hlow := hp.sub htop
  have he : p - (p-sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[N] (X 2))) =
      sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[N] (X 2)) := by ring
  have hlow' : WeightedSymbolOrderLE N
      (p-(p-sectorTwoSymbolLift ((Wong.SectorTwo.dynamics a k)^[N] (X 2)))) := hlow
  rw [he] at hlow'
  exact sectorTwoSymbolLift_momentum_not_lower a k hk N hlow' 

end Wong.SmoothModel



/-! The higher hidden-degree sector-II monomial ladder. Every step is an
actual canonical commutator modulo the proved weighted filtration. -/
noncomputable section
namespace Wong.SectorTwo
open MvPolynomial

/-- The unique maximal-raise transport for a hidden profile with degree d≥3. -/
def highHiddenDynamics (a : ℝ) (d : ℕ) (p : Symbols) : Symbols :=
  -C a*X 1^d*pderiv 1 p + C ((d:ℝ)*a)*X 1^(d-1)*X 3*pderiv 3 p

def highMomentumMonomial (c : ℝ) (q : ℕ) : Symbols := C c*X 0*X 1^q*X 3

theorem highHiddenDynamics_monomial (a c : ℝ) (d q : ℕ) (hd : 0<d) :
    highHiddenDynamics a d (highMomentumMonomial c q) =
      highMomentumMonomial (c*a*((d:ℝ)-q)) (q+(d-1)) := by
  cases d with
  | zero => omega
  | succ d =>
    cases q with
    | zero =>
      simp only [highHiddenDynamics, highMomentumMonomial, pderiv_mul, pderiv_pow,
        pderiv_C, pderiv_X]
      simp [pow_add, pow_succ, map_mul, map_sub, Nat.cast_add]
      ring
    | succ q =>
      simp only [highHiddenDynamics, highMomentumMonomial, pderiv_mul, pderiv_pow,
        pderiv_C, pderiv_X]
      simp [pow_add, pow_succ, map_mul, map_sub, Nat.cast_add]
      ring

def highMomentumCoefficient (a k : ℝ) (d : ℕ) : ℕ → ℝ
  | 0 => k
  | n+1 => highMomentumCoefficient a k d n*a*((d:ℝ)-(n*(d-1):ℕ))

theorem highExponent_ne_degree (d n : ℕ) (hd : 3≤d) : n*(d-1)≠d := by
  have hdsub : d-1+1=d := by omega
  intro he
  cases n with
  | zero => simp at he; omega
  | succ n =>
    cases n with
    | zero => simp at he; omega
    | succ n =>
      have hdn : 2≤d-1 := by omega
      have hp : 2*(d-1)≤(n+1+1)*(d-1) := Nat.mul_le_mul_right _ (by omega)
      nlinarith

theorem highMomentumCoefficient_ne_zero (a k : ℝ) (d n : ℕ)
    (ha : a≠0) (hk : k≠0) (hd : 3≤d) : highMomentumCoefficient a k d n≠0 := by
  induction n with
  | zero => exact hk
  | succ n ih =>
    apply mul_ne_zero (mul_ne_zero ih ha)
    exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm (highExponent_ne_degree d n hd))

theorem highMomentumMonomial_ne_zero (c : ℝ) (q : ℕ) (hc : c≠0) :
    highMomentumMonomial c q≠0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hc) (X_ne_zero 0))
    (pow_ne_zero q (X_ne_zero 1))) (X_ne_zero 3)

theorem weightedEuler_highMomentumMonomial (c : ℝ) (q : ℕ) :
    weightedEuler (highMomentumMonomial c q)=(q+2:ℝ) • highMomentumMonomial c q := by
  cases q with
  | zero =>
    simp only [highMomentumMonomial, Derivation.leibniz, Derivation.leibniz_pow, derivation_C]
    simp [weightedEuler, smul_eq_mul, Algebra.smul_def]
    ring
  | succ q =>
    simp only [highMomentumMonomial, Derivation.leibniz, Derivation.leibniz_pow, derivation_C]
    simp [weightedEuler, smul_eq_mul, Algebra.smul_def, pow_succ, Nat.cast_add]
    ring

end Wong.SectorTwo

namespace Wong.SmoothModel
open MvPolynomial

def powerHiddenProfile (a : ℝ) (d : ℕ) : Smooth :=
  a • linearFunction (coordinateVector 2)^d

theorem partialDerivative_powerHiddenProfile (a : ℝ) (d : ℕ) :
    partialDerivative 2 (powerHiddenProfile a d) =
      ((d:ℝ)*a) • linearFunction (coordinateVector 2)^(d-1) := by
  rw [powerHiddenProfile, map_smul]
  change a • smoothPartialDerivation 2 (linearFunction (coordinateVector 2)^d) = _
  rw [Derivation.leibniz_pow]
  simp only [smoothPartialDerivation_apply, partialDerivative_linearFunction, coordinateVector,
    Pi.single_eq_same, one_smul, smoothOne_eq_one, smul_eq_mul, mul_one]
  simp only [Algebra.smul_def, map_mul, map_natCast]
  have hn : (algebraMap ℕ Smooth) d = (d:Smooth) := map_natCast (algebraMap ℕ Smooth) d
  rw [hn]
  ring

theorem sectorTwoSymbolLift_highHiddenDynamics (a : ℝ) (d : ℕ)
    (p : Wong.SectorTwo.Symbols) :
    -hiddenWeightedTransport (powerHiddenProfile a d) (sectorTwoSymbolLift p) =
      sectorTwoSymbolLift (Wong.SectorTwo.highHiddenDynamics a d p) := by
  rw [hiddenWeightedTransport, sectorTwoSymbolLift_position_two,
    sectorTwoSymbolLift_momentum_two, partialDerivative_powerHiddenProfile]
  simp only [Wong.SectorTwo.highHiddenDynamics, map_add, map_neg, map_mul, map_pow,
    sectorTwoSymbolLift_C, sectorTwoSymbolLift_X1, sectorTwoSymbolLift_X3]
  simp only [powerHiddenProfile, Algebra.smul_def, map_mul, map_pow, smoothOne_eq_one, mul_one]
  ring

theorem sectorTwoSymbolLift_highMonomial_order (c : ℝ) (q : ℕ) :
    WeightedSymbolOrderLE (q+2)
      (sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial c q)) := by
  apply weightedSymbolEuler_eigen_order
  rw [sectorTwoSymbolLift_intertwines, Wong.SectorTwo.weightedEuler_highMomentumMonomial, map_smul]
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat]

theorem sectorTwoSymbolLift_highMonomial_not_lower (c : ℝ) (q : ℕ) (hc : c≠0) :
    ¬WeightedSymbolOrderLE (q+1)
      (sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial c q)) := by
  intro hbound
  have he : weightedSymbolEuler (sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial c q)) =
      (q+2:ℝ) • sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial c q) := by
    rw [sectorTwoSymbolLift_intertwines, Wong.SectorTwo.weightedEuler_highMomentumMonomial, map_smul]
  have hz := weightedSymbolEuler_eigen_zero_of_lower_bound ((q:ℤ)+2)
    (sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial c q))
    (by simpa only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using he)
    (hbound.mono (by omega))
  apply Wong.SectorTwo.highMomentumMonomial_ne_zero c q hc
  apply sectorTwoSymbolLift_injective
  simpa only [map_zero] using hz

theorem symbolBracket_X_right (p : SmoothSymbol) (i : Fin 3) :
    symbolBracket p (X i) = -symbolCoefficientDerivative i p := by
  apply normalQuantize_injective
  rw [normalQuantize_symbolBracket, normalQuantize_X, map_neg,
    normalQuantize_coefficientDerivative, lie_skew]

/-- The first actual commutator has the nonzero k x₀ ζ component, independent
of the higher hidden degree of ε. -/
theorem canonicalWeightedSymbol_seed_error (g F ε V r : Smooth) (k : ℝ)
    (hg : HiddenDegreeLE 0 g) (hV : HiddenDegreeLE 1 V)
    (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (hrvis : ∀i : Fin 3,i≠2 → partialDerivative i r=0)
    (hF0 : partialDerivative 0 F=k • linearFunction (coordinateVector 0)) :
    WeightedSymbolOrderLE 1
      (symbolBracket (canonicalWeightedSymbol g F ε V r) (X 0) -
        sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial k 0)) := by
  have heps := hεvis 0 (by decide)
  have heps' : partialDerivative 0 (partialDerivative 2 ε)=0 := by
    have hc := congrArg (fun A : Operator => A ε) (partialDerivative_commute 0 2)
    change partialDerivative 0 (partialDerivative 2 ε)=partialDerivative 2 (partialDerivative 0 ε) at hc
    rw [hc, heps, map_zero]
  have he : symbolBracket (canonicalWeightedSymbol g F ε V r) (X 0) -
        sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial k 0) =
      C (partialDerivative 0 g)*X 1-C (partialDerivative 0 V) := by
    rw [symbolBracket_X_right]
    simp only [canonicalWeightedSymbol, map_sub, map_add, map_smul, map_sum,
      symbolCoefficientDerivative_mul, symbolCoefficientDerivative_C, symbolCoefficientDerivative_X,
      pow_two, zero_mul, mul_zero, add_zero, sub_zero, Finset.sum_const_zero, smul_zero,
      hF0, heps, heps', hrvis 0 (by decide), map_zero, Wong.SectorTwo.highMomentumMonomial,
      map_mul, map_pow, sectorTwoSymbolLift_C, sectorTwoSymbolLift_X0, sectorTwoSymbolLift_X1, sectorTwoSymbolLift_X2, sectorTwoSymbolLift_X3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three, pow_zero, mul_one]
    simp only [Algebra.smul_def, smoothOne_eq_one, mul_one, map_mul]
    ring
  rw [he]
  have hg' := (WeightedSymbolOrderLE.C (partialDerivative 0 g)
    (hg.coordinateDerivative 0)).mul (WeightedSymbolOrderLE.X 1)
  have hV' := WeightedSymbolOrderLE.C (partialDerivative 0 V) (hV.coordinateDerivative 0)
  have hg'' : WeightedSymbolOrderLE 1 (C (partialDerivative 0 g)*X 1) := by
    simpa [momentumCoordinateWeight] using hg'
  exact hg''.sub hV'

/-- The high-degree actual commutators begin at [L,∂₀], whose nonzero
highest component has weighted degree two. -/
theorem sectorTwoHighWords_top (g F ε V r : Smooth) (a k : ℝ) (d : ℕ)
    (hd : 3≤d) (hg : HiddenDegreeLE 0 g) (hF : HiddenDegreeLE 0 F)
    (hε : HiddenDegreeLE d ε) (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (hV : HiddenDegreeLE 1 V) (hr : HiddenDegreeLE d r)
    (hrvis : ∀i : Fin 3,i≠2 → partialDerivative i r=0)
    (hF0 : partialDerivative 0 F=k • linearFunction (coordinateVector 0))
    (hεtop : HiddenDegreeLE ((d:ℤ)-1) (ε-powerHiddenProfile a d)) (n : ℕ) :
    WeightedSymbolOrderLE ((n*(d-1):ℕ)+1)
      (sectorTwoCanonicalWords (canonicalWeightedSymbol g F ε V r) (n+1) -
        sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial
          (Wong.SectorTwo.highMomentumCoefficient a k d n) (n*(d-1)))) := by
  induction n with
  | zero =>
    simpa only [zero_mul, Nat.cast_zero, zero_add, sectorTwoCanonicalWords,
      Wong.SectorTwo.highMomentumCoefficient] using
      canonicalWeightedSymbol_seed_error g F ε V r k hg hV hεvis hrvis hF0
  | succ n ih =>
    let c := Wong.SectorTwo.highMomentumCoefficient a k d n
    let q : ℕ := n*(d-1)
    let p := sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial c q)
    have hp : WeightedSymbolOrderLE (q+2) p := sectorTwoSymbolLift_highMonomial_order c q
    have h₁ := canonicalWeightedSymbol_bracket_order g F ε V r d (by exact_mod_cast (show 2≤d by omega))
      hg hF hε hεvis hV hr hrvis _ (q+1) ih
    have h₂ := canonicalWeightedSymbol_high_transport_error g F ε V r d (by exact_mod_cast hd)
      hg hF hε hεvis hV hr hrvis p (q+2) hp
    have h₃ := (weighted_hidden_transport_order (ε-powerHiddenProfile a d) ((d:ℤ)-1)
      hεtop p (q+2) hp).neg
    have hstep : Wong.SectorTwo.highHiddenDynamics a d (Wong.SectorTwo.highMomentumMonomial c q) =
        Wong.SectorTwo.highMomentumMonomial (Wong.SectorTwo.highMomentumCoefficient a k d (n+1))
          ((n+1)*(d-1)) := by
      rw [Wong.SectorTwo.highHiddenDynamics_monomial a c d q (by omega)]
      simp only [c, q, Wong.SectorTwo.highMomentumCoefficient, Nat.add_mul, one_mul]
    have ht : -hiddenWeightedTransport (powerHiddenProfile a d) p =
        sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial
          (Wong.SectorTwo.highMomentumCoefficient a k d (n+1)) ((n+1)*(d-1))) := by
      rw [sectorTwoSymbolLift_highHiddenDynamics, hstep]
    have he :
        sectorTwoCanonicalWords (canonicalWeightedSymbol g F ε V r) (n+1+1) -
          sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial
            (Wong.SectorTwo.highMomentumCoefficient a k d (n+1)) ((n+1)*(d-1))) =
        symbolBracket (canonicalWeightedSymbol g F ε V r)
          (sectorTwoCanonicalWords (canonicalWeightedSymbol g F ε V r) (n+1)-p) +
        (symbolBracket (canonicalWeightedSymbol g F ε V r) p+hiddenWeightedTransport ε p) -
        hiddenWeightedTransport (ε-powerHiddenProfile a d) p := by
      rw [←ht, sectorTwoCanonicalWords, symbolBracket_sub_right, hiddenWeightedTransport_sub]
      ring
    rw [he]
    have h₁' : WeightedSymbolOrderLE ((q:ℤ)+d) _ := h₁.mono (by omega)
    have h₂' : WeightedSymbolOrderLE ((q:ℤ)+d) _ := h₂.mono (by omega)
    have h₃' : WeightedSymbolOrderLE ((q:ℤ)+d) _ := h₃.mono (by omega)
    have hsum := (h₁'.add h₂').add h₃'
    have hindex : (((n+1)*(d-1):ℕ):ℤ)+1=(q:ℤ)+d := by
      dsimp only [q]
      rw [Nat.add_mul, one_mul, Nat.cast_add]
      have hd' : ((d-1:ℕ):ℤ)=(d:ℤ)-1 := by omega
      rw [hd']
      ring
    simpa only [sub_eq_add_neg, hindex] using hsum

/-- The actual higher-degree sector-II weighted ladder is incompatible with
finite dimensionality. The leading profile coefficient is required nonzero;
its extraction from the actual one-variable polynomial occurs upstream. -/
theorem sectorTwo_high_actual_obstruction (E : LieSubalgebra ℝ Operator)
    [FiniteDimensional ℝ E] (g F ε V r : Smooth) (a k : ℝ) (d : ℕ)
    (ha : a≠0) (hk : k≠0) (hd : 3≤d)
    (hL : canonicalWeightedOperator g F ε V r∈E) (hx : partialDerivative 0∈E)
    (hg : HiddenDegreeLE 0 g) (hF : HiddenDegreeLE 0 F)
    (hε : HiddenDegreeLE d ε) (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (hV : HiddenDegreeLE 1 V) (hr : HiddenDegreeLE d r)
    (hrvis : ∀i : Fin 3,i≠2 → partialDerivative i r=0)
    (hF0 : partialDerivative 0 F=k • linearFunction (coordinateVector 0))
    (hεtop : HiddenDegreeLE ((d:ℤ)-1) (ε-powerHiddenProfile a d)) : False := by
  obtain ⟨N,hN⟩ := actual_uniform_weighted_symbol_bound E.toSubmodule
  let q := N*(d-1)
  let c := Wong.SectorTwo.highMomentumCoefficient a k d N
  let p := sectorTwoCanonicalWords (canonicalWeightedSymbol g F ε V r) (N+1)
  let t := sectorTwoSymbolLift (Wong.SectorTwo.highMomentumMonomial c q)
  have hpE : normalQuantize p∈E := sectorTwoCanonicalWords_mem E _
    (by simpa only [normalQuantize_canonicalWeightedSymbol] using hL) hx (N+1)
  have ht : WeightedSymbolOrderLE (q+2) t := sectorTwoSymbolLift_highMonomial_order c q
  have herr : WeightedSymbolOrderLE (q+1) (p-t) :=
    sectorTwoHighWords_top g F ε V r a k d hd hg hF hε hεvis hV hr hrvis hF0 hεtop N
  have hpw : WeightedSymbolOrderLE (q+2) p := by
    have hh := (herr.mono (show (q:ℤ)+1≤q+2 by omega)).add ht
    simpa only [sub_add_cancel] using hh
  have hpN : WeightedSymbolOrderLE N p := hN p hpE ⟨q+2,by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hpw⟩
  have hqN : N≤q+1 := by
    dsimp only [q]
    have hh : N*1≤N*(d-1) := Nat.mul_le_mul_left N (by omega)
    simpa only [mul_one] using hh.trans (Nat.le_succ _)
  have hpt : WeightedSymbolOrderLE (q+1) p := hpN.mono (by exact_mod_cast hqN)
  have htlow : WeightedSymbolOrderLE (q+1) t := by
    have hh := hpt.sub herr
    simpa only [sub_sub_cancel] using hh
  exact sectorTwoSymbolLift_highMonomial_not_lower c q
    (Wong.SectorTwo.highMomentumCoefficient_ne_zero a k d N ha hk hd) htlow

end Wong.SmoothModel
