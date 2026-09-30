import Wong.AffinePrincipalRigidity
import Wong.EulerHighDegreeLadder

/-! Single compilation unit for the internally proved high-degree mixed-affinity obstruction. -/



/-! The same faithful radial momentum ladder at every ordinary order at least
 two. In particular a nonzero `t ξ₂^k` head cannot occur together with constant
 momentum remainder in a finite-dimensional actual estimation algebra. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Wong.SmoothModel
open MvPolynomial

def affineHigherOrder (d n : ℕ) : ℕ := (n+1)*(d+1)+2

theorem affineMomentumSeed_higher_homogeneous (B : Fin 3 → RealPoly) (d : ℕ)
    (hB : ∀i, (B i).IsHomogeneous (d+2)) :
    (affineMomentumSeed B).IsHomogeneous (affineHigherOrder d 0) := by
  apply IsHomogeneous.sum
  intro i _
  convert (isHomogeneous_X ℝ i).mul (hB i) using 1
  simp only [affineHigherOrder]
  omega

theorem affineMomentumStep_higher_homogeneous (B : Fin 3 → RealPoly) (d : ℕ)
    (hB : ∀i, (B i).IsHomogeneous (d+2)) (p : RealPoly) (r : ℕ)
    (hp : p.IsHomogeneous (r+1)) :
    (affineMomentumStep B p).IsHomogeneous (r+d+2) := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [Nat.add_sub_cancel, Nat.add_assoc] using hp.pderiv.mul (hB i)

theorem affineMomentumWords_higher_homogeneous (B : Fin 3 → RealPoly) (d : ℕ)
    (hB : ∀i, (B i).IsHomogeneous (d+2)) (n : ℕ) :
    (affineMomentumWords B n).IsHomogeneous (affineHigherOrder d n) := by
  induction n with
  | zero => exact affineMomentumSeed_higher_homogeneous B d hB
  | succ n ih =>
    have hh := affineMomentumStep_higher_homogeneous B d hB _ ((n+1)*(d+1)+1) ih
    change (affineMomentumStep B (affineMomentumWords B n)).IsHomogeneous _
    convert hh using 1
    unfold affineHigherOrder
    ring

theorem affineMomentumWords_higher_eval_ne_zero (B : Fin 3 → RealPoly) (d : ℕ)
    (hB : ∀i, (B i).IsHomogeneous (d+2)) (v : State) (lam : ℝ) (hlam : lam≠0)
    (hBv : ∀i, eval v (B i)=lam*v i)
    (hseed : eval v (affineMomentumSeed B)≠0) (n : ℕ) :
    eval v (affineMomentumWords B n)≠0 := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
    rw [affineMomentumWords, affineMomentumStep_eval B v lam hBv _ (affineHigherOrder d n)
      (affineMomentumWords_higher_homogeneous B d hB n)]
    exact mul_ne_zero (mul_ne_zero hlam (by unfold affineHigherOrder; positivity)) ih

theorem affinePrincipalWords_higher_order (l q : NormalForm) (d : ℕ)
    (hl : NormalDegreeLE 2 l) (hq : NormalDegreeLE (d+2) q) (n : ℕ) :
    NormalDegreeLE (affineHigherOrder d n) (affinePrincipalWords l q n) := by
  induction n with
  | zero =>
    apply normalDegreeLE_of_action_order
    rw [affinePrincipalWords, normalAction_bracket]
    rw [show affineHigherOrder d 0 = 2+(d+2)-1 by unfold affineHigherOrder; omega]
    exact lie_mem_orderSpace_sharp (action_order_of_normalDegreeLE _ _ hl)
      (action_order_of_normalDegreeLE _ _ hq)
  | succ n ih =>
    apply normalDegreeLE_of_action_order
    rw [affinePrincipalWords, normalAction_bracket]
    convert lie_mem_orderSpace_sharp (action_order_of_normalDegreeLE _ _ ih)
      (action_order_of_normalDegreeLE _ _ hq) using 1
    congr 1
    simp only [affineHigherOrder, Nat.add_mul]
    omega

theorem affinePrincipalWords_higher_symbol {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (d : ℕ)
    (q : NormalForm) (hq : NormalDegreeLE (d+2) q) (B : Fin 3 → RealPoly)
    (hB : ∀i, symbolCoefficientDerivative i (normalSymbol (d+2) q)=constantMomentum (B i))
    (n : ℕ) : normalSymbol (affineHigherOrder d n)
      (affinePrincipalWords (normalL0 f h) q n)=
      constantMomentum (affineMomentumWords B n) := by
  have hl : NormalDegreeLE 2 (normalL0 f h) := normalDegreeLE_of_action_order _ _ (by
    rw [normalAction_normalL0]; exact L0_mem_orderSpace_two f h)
  induction n with
  | zero =>
    rw [affinePrincipalWords, show affineHigherOrder d 0=1+(d+1)+1 by
      simp only [affineHigherOrder]; omega,
      normalSymbol_bracket _ _ 1 (d+1) hl hq, normalSymbol_normalL0]
    change symbolPoisson euclideanKinetic (normalSymbol (d+2) q)=_
    rw [poisson_euclideanKinetic]
    simp only [hB, affineMomentumWords, affineMomentumSeed, map_sum, map_mul,
      constantMomentum_X]
  | succ n ih =>
    have hord := affinePrincipalWords_higher_order (normalL0 f h) q d hl hq n
    change NormalDegreeLE (((n+1)*(d+1)+1)+1) _ at hord
    rw [affinePrincipalWords,
      show affineHigherOrder d (n+1)=((n+1)*(d+1)+1)+(d+1)+1 by
        unfold affineHigherOrder; ring,
      normalSymbol_bracket _ _ ((n+1)*(d+1)+1) (d+1) hord hq]
    change symbolPoisson (normalSymbol (affineHigherOrder d n)
      (affinePrincipalWords (normalL0 f h) q n)) (normalSymbol (d+2) q)=_
    rw [ih, poisson_constantMomentum_affine _ _ B hB]
    rfl

/-- Every radial eigenvalue of an affine position-dependent principal symbol
of ordinary order at least two must vanish in the genuine finite-dimensional
estimation algebra. -/
theorem actual_higher_affine_principal_radial_obstruction {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (d : ℕ) (q : NormalForm) (hq : NormalDegreeLE (d+2) q)
    (hqE : normalAction q ∈ estimationAlgebra f h) (B : Fin 3 → RealPoly)
    (hBhom : ∀i, (B i).IsHomogeneous (d+2))
    (hB : ∀i, symbolCoefficientDerivative i (normalSymbol (d+2) q)=constantMomentum (B i))
    (v : State) (lam : ℝ) (hBv : ∀i, eval v (B i)=lam*v i)
    (hseed : eval v (affineMomentumSeed B)≠0) : lam=0 := by
  by_contra hlam
  obtain ⟨N,hN⟩ := estimationAlgebra_uniform_order_bound f h
  have hmem (n : ℕ) : normalAction (affinePrincipalWords (normalL0 f h) q n) ∈
      estimationAlgebra f h := by
    induction n with
    | zero =>
      rw [affinePrincipalWords, normalAction_bracket, normalAction_normalL0]
      exact (estimationAlgebra f h).lie_mem
        (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hqE
    | succ n ih =>
      rw [affinePrincipalWords, normalAction_bracket]
      exact (estimationAlgebra f h).lie_mem ih hqE
  have hlt : N < affineHigherOrder d N := by
    have hh : N+1 ≤ (N+1)*(d+1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold affineHigherOrder
    omega
  have hz := normalSymbol_zero_of_lower_order
    (affinePrincipalWords (normalL0 f h) q N) N (affineHigherOrder d N)
    (normalDegreeLE_of_action_order _ _ (hN (hmem N))) hlt
  rw [affinePrincipalWords_higher_symbol f h d q hq B hB N] at hz
  have he := congrArg (momentumTest v) hz
  simp only [momentumTest_constantMomentum, map_zero] at he
  exact affineMomentumWords_higher_eval_ne_zero B d hBhom v lam hlam hBv hseed N he

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_higher_affine_principal_radial_obstruction


/-! A genuine polynomial-coefficient model inside smooth normal symbols. The
position degree falls under Euclidean kinetic transport; momentum degree and
position degree are kept distinct throughout. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Wong.SmoothModel
open MvPolynomial

abbrev PolynomialSymbol := MvPolynomial (Fin 3) RealPoly

def polynomialSmoothHom : RealPoly →+* Smooth where
  toFun := polynomialSmooth
  map_zero' := polynomialSmooth_zero
  map_one' := polynomialSmooth_one
  map_add' := polynomialSmooth_add
  map_mul' p q := polynomialSmooth_mul p q

def polynomialSymbolLift : PolynomialSymbol →+* SmoothSymbol :=
  MvPolynomial.map polynomialSmoothHom

def polynomialSymbolDerivative (i : Fin 3) : Module.End ℝ PolynomialSymbol :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (pderiv i).toLinearMap).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap)

@[simp] theorem polynomialSymbolDerivative_coeff (i : Fin 3)
    (p : PolynomialSymbol) (α : MultiIndex) :
    (polynomialSymbolDerivative i p).coeff α=pderiv i (p.coeff α) := rfl

@[simp] theorem polynomialSymbolLift_coeff (p : PolynomialSymbol) (α : MultiIndex) :
    (polynomialSymbolLift p).coeff α=polynomialSmooth (p.coeff α) := coeff_map polynomialSmoothHom p α

@[simp] theorem polynomialSymbolLift_C (p : RealPoly) :
    polynomialSymbolLift (C p)=C (polynomialSmooth p) := map_C _ _

@[simp] theorem polynomialSymbolLift_X (i : Fin 3) :
    polynomialSymbolLift (X i)=X i := map_X _ _

theorem polynomialSymbolLift_derivative (i : Fin 3) (p : PolynomialSymbol) :
    polynomialSymbolLift (polynomialSymbolDerivative i p)=
      symbolCoefficientDerivative i (polynomialSymbolLift p) := by
  apply MvPolynomial.ext
  intro α
  simp only [polynomialSymbolLift_coeff, polynomialSymbolDerivative_coeff,
    symbolCoefficientDerivative_coeff, partialDerivative_polynomialSmooth]

def polynomialKineticTransport : Module.End ℝ PolynomialSymbol where
  toFun p := ∑i : Fin 3, X i * polynomialSymbolDerivative i p
  map_add' p q := by simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by simp only [map_smul, mul_smul_comm, Finset.smul_sum, RingHom.id_apply]

def smoothKineticTransport : Module.End ℝ SmoothSymbol where
  toFun p := ∑i : Fin 3, X i * symbolCoefficientDerivative i p
  map_add' p q := by simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by simp only [map_smul, mul_smul_comm, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem polynomialKineticTransport_apply (p : PolynomialSymbol) :
    polynomialKineticTransport p=∑i : Fin 3,X i*polynomialSymbolDerivative i p := rfl

@[simp] theorem smoothKineticTransport_apply (p : SmoothSymbol) :
    smoothKineticTransport p=∑i : Fin 3,X i*symbolCoefficientDerivative i p := rfl

theorem smoothKineticTransport_poisson (p : SmoothSymbol) :
    smoothKineticTransport p=symbolPoisson euclideanKinetic p :=
  (poisson_euclideanKinetic p).symm

theorem polynomialSymbolLift_kinetic (p : PolynomialSymbol) :
    polynomialSymbolLift (polynomialKineticTransport p)=
      smoothKineticTransport (polynomialSymbolLift p) := by
  simp only [polynomialKineticTransport_apply, smoothKineticTransport_apply,
    map_sum, map_mul, polynomialSymbolLift_X, polynomialSymbolLift_derivative]

theorem polynomialSymbolLift_kinetic_power (p : PolynomialSymbol) (r : ℕ) :
    polynomialSymbolLift ((polynomialKineticTransport^r) p)=
      (smoothKineticTransport^r) (polynomialSymbolLift p) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, polynomialSymbolLift_kinetic,
      ih, pow_succ', Module.End.mul_apply]

def PolynomialPositionDegreeLE (n : ℕ) (p : PolynomialSymbol) : Prop :=
  ∀α : MultiIndex, (p.coeff α).totalDegree≤n

namespace PolynomialPositionDegreeLE

theorem zero (n : ℕ) : PolynomialPositionDegreeLE n 0 := by intro α; simp

theorem mono {m n : ℕ} {p : PolynomialSymbol} (hp : PolynomialPositionDegreeLE m p)
    (hmn : m≤n) : PolynomialPositionDegreeLE n p := fun α => (hp α).trans hmn

theorem add {n : ℕ} {p q : PolynomialSymbol}
    (hp : PolynomialPositionDegreeLE n p) (hq : PolynomialPositionDegreeLE n q) :
    PolynomialPositionDegreeLE n (p+q) := by
  intro α
  change totalDegree (p.coeff α + q.coeff α) ≤ n
  exact (totalDegree_add _ _).trans (max_le (hp α) (hq α))

theorem sum {ι : Type*} (s : Finset ι) (p : ι → PolynomialSymbol) (n : ℕ)
    (hp : ∀i∈s,PolynomialPositionDegreeLE n (p i)) :
    PolynomialPositionDegreeLE n (∑i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem C (p : RealPoly) (n : ℕ) (hp : p.totalDegree≤n) :
    PolynomialPositionDegreeLE n (MvPolynomial.C p) := by
  intro α
  rw [coeff_C]
  split_ifs
  · exact hp
  · simp

theorem X_mul {n : ℕ} {p : PolynomialSymbol} (hp : PolynomialPositionDegreeLE n p)
    (i : Fin 3) : PolynomialPositionDegreeLE n (X i*p) := by
  intro α
  rw [coeff_X_mul']
  split_ifs
  · exact hp _
  · simp

theorem derivative {n : ℕ} {p : PolynomialSymbol} (hp : PolynomialPositionDegreeLE (n+1) p)
    (i : Fin 3) : PolynomialPositionDegreeLE n (polynomialSymbolDerivative i p) := by
  intro α
  rw [polynomialSymbolDerivative_coeff]
  have hh := Wong.PolynomialGradient.partial_totalDegree_le (p.coeff α) i
  exact hh.trans (by have h := hp α; omega)

theorem kinetic {n : ℕ} {p : PolynomialSymbol} (hp : PolynomialPositionDegreeLE (n+1) p) :
    PolynomialPositionDegreeLE n (polynomialKineticTransport p) := by
  rw [polynomialKineticTransport_apply]
  apply sum
  intro i _
  exact (hp.derivative i).X_mul i

theorem kinetic_power (r n : ℕ) (p : PolynomialSymbol)
    (hp : PolynomialPositionDegreeLE (r+n) p) :
    PolynomialPositionDegreeLE n ((polynomialKineticTransport^r) p) := by
  induction r generalizing p with
  | zero => simpa using hp
  | succ r ih =>
    rw [pow_succ, Module.End.mul_apply]
    apply ih
    apply kinetic
    convert hp using 1
    omega

end PolynomialPositionDegreeLE

def constantPosition (p : RealPoly) : PolynomialSymbol := MvPolynomial.map C p

def positionConstantTerm (p : PolynomialSymbol) : RealPoly := MvPolynomial.map (eval (0 : State)) p

theorem position_degree_zero_constant (p : PolynomialSymbol)
    (hp : PolynomialPositionDegreeLE 0 p) : p=constantPosition (positionConstantTerm p) := by
  apply MvPolynomial.ext
  intro α
  simp only [constantPosition, positionConstantTerm, coeff_map]
  have hd : (p.coeff α).totalDegree=0 := Nat.eq_zero_of_le_zero (hp α)
  have he := (totalDegree_eq_zero_iff_eq_C.mp hd)
  rw [he]
  simp

theorem polynomialSymbolLift_constantPosition (p : RealPoly) :
    polynomialSymbolLift (constantPosition p)=constantMomentum p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [constantPosition, map_C, polynomialSymbolLift_C,
      polynomialSmooth_C, constantMomentum_C]
  | add p q hp hq => simpa only [constantPosition, map_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    change polynomialSymbolLift (MvPolynomial.map C (p*X i))=constantMomentum (p*X i)
    rw [map_mul, map_X, map_mul, polynomialSymbolLift_X, map_mul, constantMomentum_X]
    exact congrArg (fun q : SmoothSymbol => q*X i) hp

theorem polynomialSymbolLift_kinetic_degree_constant (p : PolynomialSymbol) (r : ℕ)
    (hp : PolynomialPositionDegreeLE r p) :
    ∃q : RealPoly, (smoothKineticTransport^r) (polynomialSymbolLift p)=constantMomentum q := by
  have hd : PolynomialPositionDegreeLE 0 ((polynomialKineticTransport^r) p) :=
    PolynomialPositionDegreeLE.kinetic_power r 0 p hp
  refine ⟨positionConstantTerm ((polynomialKineticTransport^r) p), ?_⟩
  rw [← polynomialSymbolLift_kinetic_power]
  exact (congrArg polynomialSymbolLift (position_degree_zero_constant _ hd)).trans
    (polynomialSymbolLift_constantPosition _)

end Wong.SmoothModel

#print axioms Wong.SmoothModel.polynomialSymbolLift_kinetic_degree_constant


/-! Elimination of a pure hidden highest position term. The remainder may have
arbitrary visible and hidden momentum terms; only its genuine position degree
is bounded. Every kinetic word is an actual bracket with the original L0. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Wong.SmoothModel
open MvPolynomial

@[simp] theorem coefficientDerivative_momentum_power (i j : Fin 3) (n : ℕ) :
    symbolCoefficientDerivative i ((X j : SmoothSymbol)^n)=0 := by
  induction n with
  | zero =>
    change symbolCoefficientDerivative i (C (1 : Smooth))=0
    rw [symbolCoefficientDerivative_C]
    have hh : partialDerivative i (1 : Smooth)=0 := by simpa using partialDerivative_const i 1
    rw [hh, map_zero]
  | succ n ih =>
    simp only [pow_succ, symbolCoefficientDerivative_mul, ih,
      symbolCoefficientDerivative_X, zero_mul, mul_zero, add_zero]

theorem partial_hidden_coordinate_pow_other (i : Fin 3) (hi : i≠2) (n : ℕ) :
    partialDerivative i (ladderHiddenCoordinate^(n+1))=0 := by
  have hd : partialDerivative i ladderHiddenCoordinate=0 := by
    simp [ladderHiddenCoordinate, partialDerivative_linearFunction, coordinateVector,
      hi]
  have hh := (smoothPartialDerivation i).leibniz_pow ladderHiddenCoordinate (n+1)
  simpa only [smoothPartialDerivation_apply, hd, mul_zero, smul_zero] using hh

theorem kinetic_hidden_monomial_step (a : ℝ) (n k : ℕ) :
    smoothKineticTransport (C (a • ladderHiddenCoordinate^(n+1))*X 2^k)=
      C ((a*(n+1:ℝ)) • ladderHiddenCoordinate^n)*X 2^(k+1) := by
  have hd (i : Fin 3) : symbolCoefficientDerivative i
      (C (a • ladderHiddenCoordinate^(n+1))*X 2^k)=
      if i=2 then C ((a*(n+1:ℝ)) • ladderHiddenCoordinate^n)*X 2^k else 0 := by
    rw [symbolCoefficientDerivative_mul, symbolCoefficientDerivative_C,
      coefficientDerivative_momentum_power, mul_zero, add_zero, map_smul]
    by_cases hi : i=2
    · subst i
      rw [partial_hidden_coordinate_pow_succ, smul_smul]
      simp only [ite_true]
    · rw [partial_hidden_coordinate_pow_other i hi, smul_zero, map_zero, zero_mul, ite_eq_right hi]
  rw [smoothKineticTransport_apply]
  simp only [hd, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem kinetic_hidden_monomial_power (n : ℕ) (a : ℝ) (k : ℕ) :
    (smoothKineticTransport^n) (C (a • ladderHiddenCoordinate^(n+1))*X 2^k)=
      C ((a*(Nat.factorial (n+1):ℝ)) • ladderHiddenCoordinate)*X 2^(n+k) := by
  induction n generalizing a k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, kinetic_hidden_monomial_step, ih]
    have he : (a*((n+1:ℕ):ℝ)+a)*(Nat.factorial (n+1):ℝ)=a*(Nat.factorial (n+1+1):ℝ) := by
      simp only [Nat.factorial_succ (n+1), Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    have he' : (a*(((n+1:ℕ):ℝ)+1))*(Nat.factorial (n+1):ℝ)=
        a*(Nat.factorial (n+1+1):ℝ) := by rw [mul_add, mul_one]; exact he
    rw [he', show n+(k+1)=n+1+k by omega]

/-- A linear hidden-position coefficient of a positive high-order pure hidden
head cannot be nonzero; the constant momentum remainder is fully retained. -/
theorem actual_hidden_affine_principal_obstruction {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] (d : ℕ)
    (q : NormalForm) (hq : NormalDegreeLE (d+2) q)
    (hqE : normalAction q ∈ estimationAlgebra f h) (a : ℝ) (r : RealPoly)
    (hS : normalSymbol (d+2) q =
      C (a • ladderHiddenCoordinate)*X 2^(d+2)+constantMomentum r) : a=0 := by
  by_contra ha
  let B : Fin 3 → RealPoly := fun i => if i=2 then C a*X 2^(d+2) else 0
  have hBhom (i : Fin 3) : (B i).IsHomogeneous (d+2) := by
    dsimp [B]
    split_ifs
    · exact isHomogeneous_C_mul_X_pow a 2 (d+2)
    · exact (homogeneousSubmodule (Fin 3) ℝ (d+2)).zero_mem
  have hB (i : Fin 3) : symbolCoefficientDerivative i (normalSymbol (d+2) q)=
      constantMomentum (B i) := by
    rw [hS, map_add, coefficientDerivative_constantMomentum, add_zero,
      symbolCoefficientDerivative_mul, symbolCoefficientDerivative_C,
      coefficientDerivative_momentum_power, mul_zero, add_zero, map_smul]
    simp only [ladderHiddenCoordinate, partialDerivative_linearFunction, coordinateVector,
      Pi.single_apply, B, apply_ite, map_zero, map_mul, constantMomentum_C,
      constantMomentum_X, map_pow]
    fin_cases i <;> simp
  have hBv (i : Fin 3) : eval (coordinateVector 2) (B i)=a*(coordinateVector 2) i := by
    fin_cases i <;> simp [B, coordinateVector]
  have hseed : eval (coordinateVector 2) (affineMomentumSeed B)≠0 := by
    simpa [affineMomentumSeed, B, Fin.sum_univ_three, coordinateVector, Pi.single_apply]
      using ha
  exact ha (actual_higher_affine_principal_radial_obstruction f h d q hq hqE
    B hBhom hB (coordinateVector 2) a hBv hseed)

def normalKineticWords {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : NormalForm) : ℕ → NormalForm
  | 0 => p
  | n+1 => normalBracket (normalL0 f h) (normalKineticWords f h p n)

theorem normalKineticWords_order {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : NormalForm) (hp : NormalDegreeLE 1 p) (n : ℕ) :
    NormalDegreeLE (n+1) (normalKineticWords f h p n) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    apply normalDegreeLE_of_action_order
    rw [normalKineticWords, normalAction_bracket, normalAction_normalL0]
    convert lie_mem_orderSpace_sharp (L0_mem_orderSpace_two f h)
      (action_order_of_normalDegreeLE _ _ ih) using 1
    congr 1
    omega

theorem normalKineticWords_principal {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : NormalForm) (hp : NormalDegreeLE 1 p) (n : ℕ) :
    normalSymbol (n+1) (normalKineticWords f h p n)=
      (smoothKineticTransport^n) (normalSymbol 1 p) := by
  have hl : NormalDegreeLE 2 (normalL0 f h) := normalDegreeLE_of_action_order _ _ (by
    rw [normalAction_normalL0]; exact L0_mem_orderSpace_two f h)
  induction n with
  | zero => simp [normalKineticWords]
  | succ n ih =>
    rw [normalKineticWords, show n+1+1=1+n+1 by omega,
      normalSymbol_bracket _ _ 1 n hl (normalKineticWords_order f h p hp n),
      normalSymbol_normalL0, ih, Wong.AdjointIteration.end_pow_succ_apply]
    exact (smoothKineticTransport_poisson _).symm

theorem normalKineticWords_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : NormalForm) (hpE : normalAction p ∈ estimationAlgebra f h) (n : ℕ) :
    normalAction (normalKineticWords f h p n) ∈ estimationAlgebra f h := by
  induction n with
  | zero => exact hpE
  | succ n ih =>
    rw [normalKineticWords, normalAction_bracket, normalAction_normalL0]
    exact (estimationAlgebra f h).lie_mem
      (LieSubalgebra.subset_lieSpan (Or.inl rfl)) ih

/-- The high-degree pure hidden top term is ruled out with a genuine lower
position-degree polynomial remainder, without any extra multiplier membership. -/
theorem actual_hidden_top_polynomial_obstruction {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (p : NormalForm) (hp : NormalDegreeLE 1 p)
    (hpE : normalAction p ∈ estimationAlgebra f h)
    (d : ℕ) (a : ℝ) (r : PolynomialSymbol)
    (hr : PolynomialPositionDegreeLE (d+1) r)
    (hS : normalSymbol 1 p=C (a • ladderHiddenCoordinate^(d+2))*X 2+
      polynomialSymbolLift r) : a=0 := by
  let q := normalKineticWords f h p (d+1)
  obtain ⟨s,hs⟩ := polynomialSymbolLift_kinetic_degree_constant r (d+1) hr
  have hq : NormalDegreeLE (d+2) q := normalKineticWords_order f h p hp (d+1)
  have hqE : normalAction q ∈ estimationAlgebra f h := normalKineticWords_mem f h p hpE (d+1)
  have hqS : normalSymbol (d+2) q=
      C ((a*(Nat.factorial (d+2):ℝ)) • ladderHiddenCoordinate)*X 2^(d+2)+constantMomentum s := by
    rw [normalKineticWords_principal f h p hp (d+1), hS, map_add, hs]
    have hh := kinetic_hidden_monomial_power (d+1) a 1
    simpa only [pow_one, show d+1+1=d+2 by omega] using congrArg (·+constantMomentum s) hh
  have hz := actual_hidden_affine_principal_obstruction f h d q hq hqE
    (a*(Nat.factorial (d+2):ℝ)) s hqS
  exact (mul_eq_zero.mp hz).resolve_right (by exact_mod_cast Nat.factorial_ne_zero (d+2))

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_hidden_top_polynomial_obstruction
