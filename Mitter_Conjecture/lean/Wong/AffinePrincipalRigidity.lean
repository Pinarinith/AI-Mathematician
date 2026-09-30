import Wong.PureHiddenSymbols
import Wong.NormalSymbolsHeads
import Wong.PolynomialSmooth

/-!
An actual order-growth obstruction for a second-order member with affine
principal coefficients.  Constant momentum polynomials are faithfully embedded
in the real smooth symbol ring.  The scalar recurrence follows from Euler's
identity, not an assumed principal-symbol correspondence.
-/
noncomputable section
set_option maxHeartbeats 2000000
namespace Wong.SmoothModel
open MvPolynomial

def constantMomentum : RealPoly →+* SmoothSymbol :=
  MvPolynomial.map (algebraMap ℝ Smooth)

@[simp] theorem constantMomentum_C (c : ℝ) :
    constantMomentum (C c) = C (c • smoothOne) := by
  simp [constantMomentum, Algebra.algebraMap_eq_smul_one]

@[simp] theorem constantMomentum_X (i : Fin 3) :
    constantMomentum (X i) = X i := by simp [constantMomentum]

@[simp] theorem coefficientDerivative_constantMomentum (i : Fin 3) (p : RealPoly) :
    symbolCoefficientDerivative i (constantMomentum p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [constantMomentum_C, symbolCoefficientDerivative_C, partialDerivative_const, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
    simp only [map_mul, constantMomentum_X, symbolCoefficientDerivative_mul,
      hp, symbolCoefficientDerivative_X, zero_mul, mul_zero, add_zero]

@[simp] theorem pderiv_constantMomentum (i : Fin 3) (p : RealPoly) :
    pderiv i (constantMomentum p) = constantMomentum (pderiv i p) := pderiv_map

def momentumTest (v : State) : SmoothSymbol →+* ℝ :=
  eval₂Hom (smoothEvalRing 0) v

@[simp] theorem momentumTest_constantMomentum (v : State) (p : RealPoly) :
    momentumTest v (constantMomentum p) = eval v p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [constantMomentum_C]
    change (eval₂Hom (smoothEvalRing 0) v) (C (c • smoothOne)) = (eval v) (C c)
    rw [eval₂Hom_C, eval_C]
    change c * 1 = c
    exact mul_one c
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, constantMomentum_X]
    simp only [momentumTest, eval₂Hom_X', map_mul, eval_X]

theorem constantMomentum_injective : Function.Injective constantMomentum := by
  intro p q hpq
  apply MvPolynomial.funext
  intro v
  simpa only [momentumTest_constantMomentum] using congrArg (momentumTest v) hpq

def euclideanKinetic : SmoothSymbol := (1/2 : ℝ) • ∑i : Fin 3, X i ^ 2

@[simp] theorem coefficientDerivative_euclideanKinetic (i : Fin 3) :
    symbolCoefficientDerivative i euclideanKinetic = 0 := by
  unfold euclideanKinetic
  rw [map_smul, map_sum]
  have hx (j : Fin 3) : symbolCoefficientDerivative i ((X j : SmoothSymbol)^2)=0 := by
    simp [pow_two, symbolCoefficientDerivative_mul]
  simp only [hx, Finset.sum_const_zero, smul_zero]

@[simp] theorem pderiv_euclideanKinetic (i : Fin 3) :
    pderiv i euclideanKinetic = X i := by
  simp only [euclideanKinetic]
  fin_cases i <;> norm_num [Fin.sum_univ_three, Pi.single_apply]
    <;> rw [two_mul] <;> module

theorem poisson_euclideanKinetic (q : SmoothSymbol) :
    symbolPoisson euclideanKinetic q =
      ∑i : Fin 3, X i * symbolCoefficientDerivative i q := by
  simp [symbolPoisson, symbolFirstCorrection]

def affineMomentumSeed (B : Fin 3 → RealPoly) : RealPoly :=
  ∑i : Fin 3, X i * B i

def affineMomentumStep (B : Fin 3 → RealPoly) (p : RealPoly) : RealPoly :=
  ∑i : Fin 3, pderiv i p * B i

def affineMomentumWords (B : Fin 3 → RealPoly) : ℕ → RealPoly
  | 0 => affineMomentumSeed B
  | n+1 => affineMomentumStep B (affineMomentumWords B n)

theorem affineMomentumSeed_homogeneous (B : Fin 3 → RealPoly)
    (hB : ∀i, (B i).IsHomogeneous 2) : (affineMomentumSeed B).IsHomogeneous 3 := by
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X ℝ i).mul (hB i)

theorem affineMomentumStep_homogeneous (B : Fin 3 → RealPoly)
    (hB : ∀i, (B i).IsHomogeneous 2) (p : RealPoly) (n : ℕ)
    (hp : p.IsHomogeneous (n+1)) : (affineMomentumStep B p).IsHomogeneous (n+2) := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [Nat.add_sub_cancel] using hp.pderiv.mul (hB i)

theorem affineMomentumWords_homogeneous (B : Fin 3 → RealPoly)
    (hB : ∀i, (B i).IsHomogeneous 2) (n : ℕ) :
    (affineMomentumWords B n).IsHomogeneous (n+3) := by
  induction n with
  | zero => exact affineMomentumSeed_homogeneous B hB
  | succ n ih =>
    exact affineMomentumStep_homogeneous B hB _ (n+2) ih

theorem affineMomentumStep_eval (B : Fin 3 → RealPoly) (v : State) (lam : ℝ)
    (hBv : ∀i, eval v (B i)=lam*v i) (p : RealPoly) (n : ℕ)
    (hp : p.IsHomogeneous n) :
    eval v (affineMomentumStep B p) = (lam*(n:ℝ))*eval v p := by
  have he := congrArg (eval v) hp.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at he
  unfold affineMomentumStep
  simp only [map_sum, map_mul, hBv]
  calc
    _ = lam * ∑i : Fin 3, v i * eval v (pderiv i p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [he]; ring

theorem affineMomentumWords_eval_ne_zero (B : Fin 3 → RealPoly)
    (hB : ∀i, (B i).IsHomogeneous 2) (v : State) (lam : ℝ) (hlam : lam≠0)
    (hBv : ∀i, eval v (B i)=lam*v i)
    (hseed : eval v (affineMomentumSeed B)≠0) (n : ℕ) :
    eval v (affineMomentumWords B n)≠0 := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
    rw [affineMomentumWords, affineMomentumStep_eval B v lam hBv _ (n+3)
      (affineMomentumWords_homogeneous B hB n)]
    exact mul_ne_zero (mul_ne_zero hlam (by positivity)) ih

theorem poisson_constantMomentum_affine (p : RealPoly) (q : SmoothSymbol)
    (B : Fin 3 → RealPoly)
    (hB : ∀i, symbolCoefficientDerivative i q=constantMomentum (B i)) :
    symbolPoisson (constantMomentum p) q = constantMomentum (affineMomentumStep B p) := by
  simp only [symbolPoisson, symbolFirstCorrection, coefficientDerivative_constantMomentum,
    mul_zero, Finset.sum_const_zero, sub_zero, pderiv_constantMomentum, hB,
    affineMomentumStep, map_sum, map_mul]

def affinePrincipalWords (l q : NormalForm) : ℕ → NormalForm
  | 0 => normalBracket l q
  | n+1 => normalBracket (affinePrincipalWords l q n) q

theorem affinePrincipalWords_order (l q : NormalForm)
    (hl : NormalDegreeLE 2 l) (hq : NormalDegreeLE 2 q) (n : ℕ) :
    NormalDegreeLE (n+3) (affinePrincipalWords l q n) := by
  induction n with
  | zero =>
    apply normalDegreeLE_of_action_order
    rw [affinePrincipalWords, normalAction_bracket]
    exact lie_mem_orderSpace_sharp (action_order_of_normalDegreeLE _ _ hl)
      (action_order_of_normalDegreeLE _ _ hq)
  | succ n ih =>
    apply normalDegreeLE_of_action_order
    rw [affinePrincipalWords, normalAction_bracket]
    convert lie_mem_orderSpace_sharp (action_order_of_normalDegreeLE _ _ ih)
      (action_order_of_normalDegreeLE _ _ hq) using 1
    congr 1

theorem affinePrincipalWords_symbol {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (q : NormalForm) (hq : NormalDegreeLE 2 q) (B : Fin 3 → RealPoly)
    (hB : ∀i, symbolCoefficientDerivative i (normalSymbol 2 q)=constantMomentum (B i))
    (n : ℕ) : normalSymbol (n+3) (affinePrincipalWords (normalL0 f h) q n)=
      constantMomentum (affineMomentumWords B n) := by
  have hl : NormalDegreeLE 2 (normalL0 f h) := normalDegreeLE_of_action_order _ _ (by
    rw [normalAction_normalL0]; exact L0_mem_orderSpace_two f h)
  induction n with
  | zero =>
    rw [affinePrincipalWords, show 0+3=1+1+1 from rfl,
      normalSymbol_bracket _ _ 1 1 hl hq, normalSymbol_normalL0]
    change symbolPoisson euclideanKinetic (normalSymbol 2 q)=_
    rw [poisson_euclideanKinetic]
    simp only [hB, affineMomentumWords, affineMomentumSeed, map_sum, map_mul,
      constantMomentum_X]
  | succ n ih =>
    rw [affinePrincipalWords, show n+1+3=(n+2)+1+1 by omega,
      normalSymbol_bracket _ _ (n+2) 1 (affinePrincipalWords_order _ _ hl hq n) hq,
      show n+2+1=n+3 by omega, ih, poisson_constantMomentum_affine _ _ B hB]
    rfl

/-- An affine second principal symbol cannot have a nonzero radial momentum
value of its coefficient gradient. All iterates here are genuine members of
the original estimation algebra. -/
theorem actual_affine_principal_radial_obstruction {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (q : NormalForm) (hq : NormalDegreeLE 2 q)
    (hqE : normalAction q ∈ estimationAlgebra f h) (B : Fin 3 → RealPoly)
    (hBhom : ∀i, (B i).IsHomogeneous 2)
    (hB : ∀i, symbolCoefficientDerivative i (normalSymbol 2 q)=constantMomentum (B i))
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
  have hz := normalSymbol_zero_of_lower_order
    (affinePrincipalWords (normalL0 f h) q N) N (N+3)
    (normalDegreeLE_of_action_order _ _ (hN (hmem N))) (by omega)
  rw [affinePrincipalWords_symbol f h q hq B hB N] at hz
  have he := congrArg (momentumTest v) hz
  simp only [momentumTest_constantMomentum, map_zero] at he
  exact affineMomentumWords_eval_ne_zero B hBhom v lam hlam hBv hseed N he

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_affine_principal_radial_obstruction
