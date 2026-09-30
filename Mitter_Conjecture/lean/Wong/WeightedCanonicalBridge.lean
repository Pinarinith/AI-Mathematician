import Wong.WeightedSymbolBridgeCore

/-!
# Actual canonical sector-II commutators in the hidden weighted filtration

All symbols are the faithful normal symbols of actual smooth differential
operators. In particular the bracket below is normal composition, not an
assumed Poisson bracket. The canonical potential retains the actual profiles
provided by the gauge calculation; it is not recomputed from a new drift.
-/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

/-- The exact canonical normal symbol. The smooth coefficients g,F have
hidden degree zero, V has degree at most one, and ε,r depend only on t. -/
def canonicalWeightedSymbol (g F ε V r : Smooth) : SmoothSymbol :=
  (1/2:ℝ) • (∑ i : Fin 3, (X i)^2) - C g * X 1 - C F * X 2 - C ε * X 2 +
    C V - (1/2:ℝ) • C (partialDerivative 2 ε + r)

/-- The actual smooth operator represented by the canonical symbol. -/
def canonicalWeightedOperator (g F ε V r : Smooth) : Operator :=
  (1/2:ℝ) • (∑ i : Fin 3, partialDerivative i * partialDerivative i) -
    multiplication g * partialDerivative 1 - multiplication F * partialDerivative 2 -
    multiplication ε * partialDerivative 2 + multiplication V -
    (1/2:ℝ) • multiplication (partialDerivative 2 ε + r)

theorem normalQuantize_canonicalWeightedSymbol (g F ε V r : Smooth) :
    normalQuantize (canonicalWeightedSymbol g F ε V r) =
      canonicalWeightedOperator g F ε V r := by
  simp only [canonicalWeightedSymbol, canonicalWeightedOperator, map_sub, map_add, map_smul,
    map_sum, pow_two, normalQuantize_mul_X, normalQuantize_X, normalQuantize_C, multiplication_add]

theorem symbolBracket_sum_left {ι : Type*} (s : Finset ι) (p : ι → SmoothSymbol)
    (q : SmoothSymbol) : symbolBracket (∑i∈s,p i) q = ∑i∈s,symbolBracket (p i) q := by
  apply normalQuantize_injective
  simp only [normalQuantize_symbolBracket, map_sum, sum_lie]

/-- The canonical actual adjoint action preserves hidden polynomiality and
raises weighted order by at most d−1 for d≥2. -/
theorem canonicalWeightedSymbol_bracket_order (g F ε V r : Smooth) (d : ℤ)
    (hd : 2≤d) (hg : HiddenDegreeLE 0 g) (hF : HiddenDegreeLE 0 F)
    (hε : HiddenDegreeLE d ε) (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (hV : HiddenDegreeLE 1 V) (hr : HiddenDegreeLE d r)
    (hrvis : ∀i : Fin 3,i≠2 → partialDerivative i r=0)
    (p : SmoothSymbol) (n : ℤ) (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE (n+d-1) (symbolBracket (canonicalWeightedSymbol g F ε V r) p) := by
  rw [canonicalWeightedSymbol, symbolBracket_sub_left, symbolBracket_add_left,
    symbolBracket_sub_left, symbolBracket_sub_left, symbolBracket_sub_left,
    symbolBracket_smul_left, symbolBracket_smul_left, symbolBracket_sum_left]
  have hk : WeightedSymbolOrderLE (n+d-1)
      ((1/2:ℝ) • ∑i : Fin 3,symbolBracket ((X i)^2) p) := by
    apply WeightedSymbolOrderLE.smul
    apply WeightedSymbolOrderLE.sum
    intro i _
    exact (weightedSymbolBracket_X_sq_order i p n hp).mono (by omega)
  have hgb : WeightedSymbolOrderLE (n+d-1) (symbolBracket (C g*X 1) p) := by
    have hq : WeightedSymbolOrderLE 1 (C g*X 1) := by
      simpa [momentumCoordinateWeight] using
        (WeightedSymbolOrderLE.C g hg).mul (WeightedSymbolOrderLE.X 1)
    exact (weightedSymbolBracket_order _ p 1 n hq hp).mono (by omega)
  have hFb : WeightedSymbolOrderLE (n+d-1) (symbolBracket (C F*X 2) p) := by
    have hq : WeightedSymbolOrderLE 2 (C F*X 2) := by
      simpa [momentumCoordinateWeight] using
        (WeightedSymbolOrderLE.C F hF).mul (WeightedSymbolOrderLE.X 2)
    exact (weightedSymbolBracket_order _ p 2 n hq hp).mono (by omega)
  have hεb := weightedSymbolBracket_hidden_drift_order ε d hε hεvis p n hp
  have hVb : WeightedSymbolOrderLE (n+d-1) (symbolBracket (C V) p) :=
    (weightedSymbolBracket_order _ p 1 n (WeightedSymbolOrderLE.C V hV) hp).mono (by omega)
  have hh : HiddenDegreeLE d (partialDerivative 2 ε+r) :=
    (hε.hiddenDerivative.mono (by omega)).add hr
  have hhvis (i : Fin 3) (hi : i≠2) : partialDerivative i (partialDerivative 2 ε+r)=0 := by
    have hc := congrArg (fun A : Operator => A ε) (partialDerivative_commute i 2)
    change partialDerivative i (partialDerivative 2 ε) = partialDerivative 2 (partialDerivative i ε) at hc
    rw [map_add, hc, hεvis i hi, map_zero, hrvis i hi, add_zero]
  have hpot : WeightedSymbolOrderLE (n+d-1)
      ((1/2:ℝ) • symbolBracket (C (partialDerivative 2 ε+r)) p) :=
    ((weightedSymbolBracket_hidden_multiplier_order _ d hh hhvis p n hp).mono (by omega)).smul _
  exact (((hk.sub hgb).sub hFb).sub hεb).add hVb |>.sub hpot

/-- Transport from the actual diffusion, without discarding its lower second derivatives. -/
def kineticWeightedTransport (p : SmoothSymbol) : SmoothSymbol :=
  ∑i : Fin 3,X i*symbolCoefficientDerivative i p

/-- The vertical F-drift contribution to the highest weighted action. -/
def verticalWeightedTransport (F : Smooth) (p : SmoothSymbol) : SmoothSymbol :=
  ∑i : Fin 3,pderiv i p*C (partialDerivative i F)*X 2

/-- The first-order hidden transport retains the real profile ε. -/
def hiddenWeightedTransport (ε : Smooth) (p : SmoothSymbol) : SmoothSymbol :=
  C ε*symbolCoefficientDerivative 2 p - pderiv 2 p*C (partialDerivative 2 ε)*X 2

/-- This explicit action will be identified with the four-variable polynomial
sector-II derivation after ε is split into its quadratic part and lower terms. -/
def canonicalWeightedTransport (F ε : Smooth) (p : SmoothSymbol) : SmoothSymbol :=
  kineticWeightedTransport p + verticalWeightedTransport F p - hiddenWeightedTransport ε p

theorem weighted_kinetic_transport_error (p : SmoothSymbol) (n : ℤ)
    (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE n
      (symbolBracket ((1/2:ℝ) • ∑i : Fin 3,(X i)^2) p - kineticWeightedTransport p) := by
  rw [symbolBracket_smul_left, symbolBracket_sum_left, kineticWeightedTransport,
    Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply WeightedSymbolOrderLE.sum
  intro i _
  have he : (1/2:ℝ) • symbolBracket ((X i)^2) p - X i*symbolCoefficientDerivative i p =
      (1/2:ℝ) • symbolCoefficientDerivative i (symbolCoefficientDerivative i p) := by
    rw [symbolBracket_X_sq_left]
    have ht : 2*X i*symbolCoefficientDerivative i p =
        (2:ℝ) • (X i*symbolCoefficientDerivative i p) := by rw [two_smul]; ring
    rw [ht, smul_add, smul_smul]
    norm_num
  rw [he]
  exact (((hp.coefficientDerivative i).coefficientDerivative i).mono (by omega)).smul _

theorem symbolFirstCorrection_vertical (F : Smooth) (p : SmoothSymbol) :
    symbolFirstCorrection p (C F*X 2) = verticalWeightedTransport F p := by
  simp only [symbolFirstCorrection, verticalWeightedTransport, symbolCoefficientDerivative_mul,
    symbolCoefficientDerivative_C, symbolCoefficientDerivative_X, mul_zero, add_zero, mul_assoc]

/-- Only lower weighted order is lost by replacing the true F-drift bracket
with its transport. The arbitrary smooth visible dependence is retained. -/
theorem weighted_vertical_transport_error (F : Smooth) (hF : HiddenDegreeLE 0 F)
    (p : SmoothSymbol) (n : ℤ) (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE n (symbolBracket (C F*X 2) p + verticalWeightedTransport F p) := by
  have hq : WeightedSymbolOrderLE 2 (C F*X 2) := by
    simpa [momentumCoordinateWeight] using
      (WeightedSymbolOrderLE.C F hF).mul (WeightedSymbolOrderLE.X 2)
  have he : symbolBracket (C F*X 2) p + verticalWeightedTransport F p =
      C F*symbolCoefficientDerivative 2 p - symbolCompositionRemainder p (C F*X 2) := by
    rw [symbolBracket_eq_poisson_remainders, symbolCompositionRemainder_C_X_left,
      symbolPoisson, symbolFirstCorrection_C_mul, symbolFirstCorrection_X_left,
      symbolFirstCorrection_vertical]
    ring
  rw [he]
  apply WeightedSymbolOrderLE.sub
  · exact ((WeightedSymbolOrderLE.C F hF).mul (hp.coefficientDerivative 2)).mono
      (by norm_num [positionDerivativeWeight])
  · simpa using weightedSymbolCompositionRemainder_order p (C F*X 2) n 2 hp hq

/-- The genuine hidden drift bracket differs from the displayed first-order
transport by a remainder at least two weighted levels below n. -/
theorem weighted_hidden_transport_error (ε : Smooth) (hε : HiddenDegreeLE 2 ε)
    (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (p : SmoothSymbol) (n : ℤ) (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE n (symbolBracket (C ε*X 2) p-hiddenWeightedTransport ε p) := by
  have hq : WeightedSymbolOrderLE 4 (C ε*X 2) := by
    simpa [momentumCoordinateWeight] using
      (WeightedSymbolOrderLE.C ε hε).mul (WeightedSymbolOrderLE.X 2)
  have hqv (i : Fin 3) (hi : i≠2) : symbolCoefficientDerivative i (C ε*X 2)=0 := by
    rw [symbolCoefficientDerivative_mul, symbolCoefficientDerivative_C, hεvis i hi,
      map_zero, zero_mul, symbolCoefficientDerivative_X, mul_zero, add_zero]
  have he : symbolBracket (C ε*X 2) p-hiddenWeightedTransport ε p =
      -symbolCompositionRemainder p (C ε*X 2) := by
    rw [symbolBracket_eq_poisson_remainders, symbolCompositionRemainder_C_X_left,
      symbolPoisson, symbolFirstCorrection_C_mul, symbolFirstCorrection_X_left,
      symbolFirstCorrection_hiddenRight p (C ε*X 2) hqv]
    simp only [hiddenWeightedTransport, symbolCoefficientDerivative_mul,
      symbolCoefficientDerivative_C, symbolCoefficientDerivative_X, mul_zero, add_zero]
    ring
  rw [he]
  exact ((weightedSymbolCompositionRemainder_hiddenRight_order p (C ε*X 2) n 4 hp hq hqv).mono
    (by omega)).neg

/-- The hidden transport itself obeys the sharp degree-dependent bound. -/
theorem weighted_hidden_transport_order (ε : Smooth) (d : ℤ) (hε : HiddenDegreeLE d ε)
    (p : SmoothSymbol) (n : ℤ) (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE (n+d-1) (hiddenWeightedTransport ε p) := by
  apply WeightedSymbolOrderLE.sub
  · have hh := (WeightedSymbolOrderLE.C ε hε).mul (hp.coefficientDerivative 2)
    convert hh using 1 <;> norm_num [positionDerivativeWeight] <;> ring
  · have hh := ((hp.pderiv 2).mul
      (WeightedSymbolOrderLE.C (partialDerivative 2 ε) hε.hiddenDerivative)).mul
      (WeightedSymbolOrderLE.X 2)
    convert hh using 1 <;>
      norm_num [momentumCoordinateWeight, positionDerivativeWeight] <;> ring

theorem hiddenWeightedTransport_sub (ε ε₀ : Smooth) (p : SmoothSymbol) :
    hiddenWeightedTransport (ε-ε₀) p = hiddenWeightedTransport ε p-hiddenWeightedTransport ε₀ p := by
  simp only [hiddenWeightedTransport, map_sub]
  ring

/-- Exact higher-degree hidden transport error: both omitted Leibniz
corrections differentiate a hidden coefficient, so their cost is six. -/
theorem weighted_hidden_transport_error_general (ε : Smooth) (d : ℤ)
    (hε : HiddenDegreeLE d ε) (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (p : SmoothSymbol) (n : ℤ) (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE (n+d-4) (symbolBracket (C ε*X 2) p-hiddenWeightedTransport ε p) := by
  have hq : WeightedSymbolOrderLE (d+2) (C ε*X 2) := by
    simpa [momentumCoordinateWeight] using
      (WeightedSymbolOrderLE.C ε hε).mul (WeightedSymbolOrderLE.X 2)
  have hqv (i : Fin 3) (hi : i≠2) : symbolCoefficientDerivative i (C ε*X 2)=0 := by
    rw [symbolCoefficientDerivative_mul, symbolCoefficientDerivative_C, hεvis i hi,
      map_zero, zero_mul, symbolCoefficientDerivative_X, mul_zero, add_zero]
  have he : symbolBracket (C ε*X 2) p-hiddenWeightedTransport ε p =
      -symbolCompositionRemainder p (C ε*X 2) := by
    rw [symbolBracket_eq_poisson_remainders, symbolCompositionRemainder_C_X_left,
      symbolPoisson, symbolFirstCorrection_C_mul, symbolFirstCorrection_X_left,
      symbolFirstCorrection_hiddenRight p (C ε*X 2) hqv]
    simp only [hiddenWeightedTransport, symbolCoefficientDerivative_mul,
      symbolCoefficientDerivative_C, symbolCoefficientDerivative_X, mul_zero, add_zero]
    ring
  rw [he]
  have hh := (weightedSymbolCompositionRemainder_hiddenRight_order p (C ε*X 2)
    n (d+2) hp hq hqv).neg
  convert hh using 1 <;> ring

/-- For d≥3 only the actual hidden drift can attain the maximal raise d−1.
Every other canonical term lies at least one level below that raise. -/
theorem canonicalWeightedSymbol_high_transport_error (g F ε V r : Smooth) (d : ℤ)
    (hd : 3≤d) (hg : HiddenDegreeLE 0 g) (hF : HiddenDegreeLE 0 F)
    (hε : HiddenDegreeLE d ε) (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (hV : HiddenDegreeLE 1 V) (hr : HiddenDegreeLE d r)
    (hrvis : ∀i : Fin 3,i≠2 → partialDerivative i r=0)
    (p : SmoothSymbol) (n : ℤ) (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE (n+d-2)
      (symbolBracket (canonicalWeightedSymbol g F ε V r) p+hiddenWeightedTransport ε p) := by
  have hk : WeightedSymbolOrderLE (n+d-2)
      (symbolBracket ((1/2:ℝ) • ∑i : Fin 3,(X i)^2) p) := by
    rw [symbolBracket_smul_left, symbolBracket_sum_left]
    apply WeightedSymbolOrderLE.smul
    apply WeightedSymbolOrderLE.sum
    intro i _
    exact (weightedSymbolBracket_X_sq_order i p n hp).mono (by omega)
  have hgb : WeightedSymbolOrderLE (n+d-2) (symbolBracket (C g*X 1) p) := by
    have hq : WeightedSymbolOrderLE 1 (C g*X 1) := by
      simpa [momentumCoordinateWeight] using
        (WeightedSymbolOrderLE.C g hg).mul (WeightedSymbolOrderLE.X 1)
    exact (weightedSymbolBracket_order _ p 1 n hq hp).mono (by omega)
  have hFb : WeightedSymbolOrderLE (n+d-2) (symbolBracket (C F*X 2) p) := by
    have hq : WeightedSymbolOrderLE 2 (C F*X 2) := by
      simpa [momentumCoordinateWeight] using
        (WeightedSymbolOrderLE.C F hF).mul (WeightedSymbolOrderLE.X 2)
    exact (weightedSymbolBracket_order _ p 2 n hq hp).mono (by omega)
  have hεb := (weighted_hidden_transport_error_general ε d hε hεvis p n hp).mono
    (show n+d-4≤n+d-2 by omega)
  have hVb : WeightedSymbolOrderLE (n+d-2) (symbolBracket (C V) p) :=
    (weightedSymbolBracket_order _ p 1 n (WeightedSymbolOrderLE.C V hV) hp).mono (by omega)
  have hh : HiddenDegreeLE d (partialDerivative 2 ε+r) :=
    (hε.hiddenDerivative.mono (by omega)).add hr
  have hhvis (i : Fin 3) (hi : i≠2) : partialDerivative i (partialDerivative 2 ε+r)=0 := by
    have hc := congrArg (fun A : Operator => A ε) (partialDerivative_commute i 2)
    change partialDerivative i (partialDerivative 2 ε) = partialDerivative 2 (partialDerivative i ε) at hc
    rw [map_add, hc, hεvis i hi, map_zero, hrvis i hi, add_zero]
  have hpot : WeightedSymbolOrderLE (n+d-2)
      ((1/2:ℝ) • symbolBracket (C (partialDerivative 2 ε+r)) p) :=
    ((weightedSymbolBracket_hidden_multiplier_order _ d hh hhvis p n hp).mono (by omega)).smul _
  have he : symbolBracket (canonicalWeightedSymbol g F ε V r) p+hiddenWeightedTransport ε p =
      symbolBracket ((1/2:ℝ) • ∑i : Fin 3,(X i)^2) p - symbolBracket (C g*X 1) p -
      symbolBracket (C F*X 2) p - (symbolBracket (C ε*X 2) p-hiddenWeightedTransport ε p) +
      symbolBracket (C V) p - (1/2:ℝ) • symbolBracket (C (partialDerivative 2 ε+r)) p := by
    simp only [canonicalWeightedSymbol, symbolBracket_sub_left, symbolBracket_add_left,
      symbolBracket_smul_left]
    abel
  rw [he]
  exact (((hk.sub hgb).sub hFb).sub hεb).add hVb |>.sub hpot

/-- The required actual canonical ad L bridge: the exact normal commutator
has the displayed first-order highest weighted action modulo W_n. -/
theorem canonicalWeightedSymbol_transport_error (g F ε V r : Smooth)
    (hg : HiddenDegreeLE 0 g) (hF : HiddenDegreeLE 0 F)
    (hε : HiddenDegreeLE 2 ε) (hεvis : ∀i : Fin 3,i≠2 → partialDerivative i ε=0)
    (hV : HiddenDegreeLE 1 V) (hr : HiddenDegreeLE 2 r)
    (hrvis : ∀i : Fin 3,i≠2 → partialDerivative i r=0)
    (p : SmoothSymbol) (n : ℤ) (hp : WeightedSymbolOrderLE n p) :
    WeightedSymbolOrderLE n
      (symbolBracket (canonicalWeightedSymbol g F ε V r) p-canonicalWeightedTransport F ε p) := by
  have hk := weighted_kinetic_transport_error p n hp
  have hFb := weighted_vertical_transport_error F hF p n hp
  have hεb := weighted_hidden_transport_error ε hε hεvis p n hp
  have hgb : WeightedSymbolOrderLE n (symbolBracket (C g*X 1) p) := by
    have hq : WeightedSymbolOrderLE 1 (C g*X 1) := by
      simpa [momentumCoordinateWeight] using
        (WeightedSymbolOrderLE.C g hg).mul (WeightedSymbolOrderLE.X 1)
    simpa using weightedSymbolBracket_order _ p 1 n hq hp
  have hVb : WeightedSymbolOrderLE n (symbolBracket (C V) p) := by
    simpa using weightedSymbolBracket_order _ p 1 n (WeightedSymbolOrderLE.C V hV) hp
  have hh : HiddenDegreeLE 2 (partialDerivative 2 ε+r) :=
    (hε.hiddenDerivative.mono (by omega)).add hr
  have hhvis (i : Fin 3) (hi : i≠2) : partialDerivative i (partialDerivative 2 ε+r)=0 := by
    have hc := congrArg (fun A : Operator => A ε) (partialDerivative_commute i 2)
    change partialDerivative i (partialDerivative 2 ε) = partialDerivative 2 (partialDerivative i ε) at hc
    rw [map_add, hc, hεvis i hi, map_zero, hrvis i hi, add_zero]
  have hpot : WeightedSymbolOrderLE n
      ((1/2:ℝ) • symbolBracket (C (partialDerivative 2 ε+r)) p) :=
    ((weightedSymbolBracket_hidden_multiplier_order _ 2 hh hhvis p n hp).mono (by omega)).smul _
  have he : symbolBracket (canonicalWeightedSymbol g F ε V r) p-canonicalWeightedTransport F ε p =
      (symbolBracket ((1/2:ℝ) • ∑i : Fin 3,(X i)^2) p-kineticWeightedTransport p) -
      symbolBracket (C g*X 1) p - (symbolBracket (C F*X 2) p+verticalWeightedTransport F p) -
      (symbolBracket (C ε*X 2) p-hiddenWeightedTransport ε p) + symbolBracket (C V) p -
      (1/2:ℝ) • symbolBracket (C (partialDerivative 2 ε+r)) p := by
    simp only [canonicalWeightedSymbol, symbolBracket_sub_left, symbolBracket_add_left,
      symbolBracket_smul_left, canonicalWeightedTransport]
    abel
  rw [he]
  exact (((hk.sub hgb).sub hFb).sub hεb).add hVb |>.sub hpot

/-- The same bridge expressly names the actual commutator being represented. -/
theorem canonicalWeightedSymbol_actual_ad (g F ε V r : Smooth) (p : SmoothSymbol) :
    normalQuantize (symbolBracket (canonicalWeightedSymbol g F ε V r) p) =
      ⁅canonicalWeightedOperator g F ε V r,normalQuantize p⁆ := by
  rw [normalQuantize_symbolBracket, normalQuantize_canonicalWeightedSymbol]

end Wong.SmoothModel
