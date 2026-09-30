import Wong.HiddenAxisLadder

/-!
# Actual quadratic visible Hessian obstruction

This connects the hidden-axis ladder to genuine brackets [L,p], [D₀,p],
[D₁,p]. The visible principal coefficients may be any smooth functions
independent of the hidden coordinate; their transverse terms are retained.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open MvPolynomial

def axisEuclideanKinetic : SmoothSymbol := (1/2 : ℝ) • ∑ i : Fin 3, X i ^ 2

@[simp] theorem coefficientDerivative_axisEuclideanKinetic (i : Fin 3) :
    symbolCoefficientDerivative i axisEuclideanKinetic = 0 := by
  unfold axisEuclideanKinetic
  rw [map_smul, map_sum]
  have hx (j : Fin 3) : symbolCoefficientDerivative i ((X j : SmoothSymbol)^2)=0 := by
    simp [pow_two, symbolCoefficientDerivative_mul]
  simp only [hx, Finset.sum_const_zero, smul_zero]

@[simp] theorem pderiv_axisEuclideanKinetic (i : Fin 3) :
    pderiv i axisEuclideanKinetic = X i := by
  unfold axisEuclideanKinetic
  fin_cases i <;> norm_num [Fin.sum_univ_three, Pi.single_apply]
    <;> rw [two_mul] <;> module

theorem poisson_axisEuclideanKinetic (p : SmoothSymbol) :
    symbolPoisson axisEuclideanKinetic p =
      ∑ i : Fin 3, X i * symbolCoefficientDerivative i p := by
  simp [symbolPoisson, symbolFirstCorrection]


def axisVectorSymbol (a : Fin 3 → Smooth) : SmoothSymbol := ∑ i, C (a i) * X i

theorem axisVectorSymbol_coefficientDerivative (a : Fin 3 → Smooth) (i : Fin 3) :
    symbolCoefficientDerivative i (axisVectorSymbol a) =
      axisVectorSymbol (fun j => partialDerivative i (a j)) := by
  simp only [axisVectorSymbol, map_sum, symbolCoefficientDerivative_mul,
    symbolCoefficientDerivative_C, symbolCoefficientDerivative_X, mul_zero, add_zero]

theorem axisVectorSymbol_project (a : Fin 3 → Smooth) :
    projectHiddenAxis (axisVectorSymbol a) = C (a 2) * X 2 := by
  simp [axisVectorSymbol, Fin.sum_univ_three]

theorem poisson_X_axisVectorSymbol (a : Fin 3 → Smooth) (i : Fin 3) :
    symbolPoisson (X i) (axisVectorSymbol a) =
      axisVectorSymbol (fun j => partialDerivative i (a j)) := by
  rw [symbolPoisson, symbolFirstCorrection, symbolFirstCorrection]
  simp only [symbolCoefficientDerivative_X, mul_zero, Finset.sum_const_zero, sub_zero,
    pderiv_X]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, axisVectorSymbol_coefficientDerivative]

theorem kinetic_axisVectorSymbol (a : Fin 3 → Smooth) :
    symbolPoisson axisEuclideanKinetic (axisVectorSymbol a) =
      ∑ i : Fin 3, ∑ j : Fin 3, C (partialDerivative i (a j)) * X i * X j := by
  rw [poisson_axisEuclideanKinetic]
  simp only [axisVectorSymbol_coefficientDerivative]
  simp only [axisVectorSymbol, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem kinetic_axisVectorSymbol_project (a : Fin 3 → Smooth) :
    projectHiddenAxis (symbolPoisson axisEuclideanKinetic (axisVectorSymbol a)) =
      C (partialDerivative 2 (a 2)) * X 2 ^ 2 := by
  rw [kinetic_axisVectorSymbol]
  simp [Fin.sum_univ_three, pow_two, mul_assoc]

theorem kinetic_axisVectorSymbol_project_pderiv_zero (a : Fin 3 → Smooth) :
    projectHiddenAxis (pderiv 0 (symbolPoisson axisEuclideanKinetic (axisVectorSymbol a))) =
      C (partialDerivative 0 (a 2) + partialDerivative 2 (a 0)) * X 2 := by
  rw [kinetic_axisVectorSymbol]
  simp [Fin.sum_univ_three, pderiv_X, add_mul]
  ring

theorem kinetic_axisVectorSymbol_project_pderiv_one (a : Fin 3 → Smooth) :
    projectHiddenAxis (pderiv 1 (symbolPoisson axisEuclideanKinetic (axisVectorSymbol a))) =
      C (partialDerivative 1 (a 2) + partialDerivative 2 (a 1)) * X 2 := by
  rw [kinetic_axisVectorSymbol]
  simp [Fin.sum_univ_three, pderiv_X, add_mul]
  ring

/-- A quadratic hidden coefficient with constant hidden derivative has zero
visible Hessian. All operators used by the proof are actual Lie members;
no membership for products of visible coordinates and derivatives is assumed. -/
theorem actual_quadratic_visible_hessian_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD₀ : D f 0 ∈ estimationAlgebra f h) (hD₁ : D f 1 ∈ estimationAlgebra f h)
    (p : NormalForm) (hp : NormalDegreeLE 1 p)
    (hpE : normalAction p ∈ estimationAlgebra f h)
    (a : Fin 3 → Smooth) (hpa : normalSymbol 1 p = axisVectorSymbol a)
    (c e g k d q : ℝ)
    (ha₀ : partialDerivative 2 (a 0) = 0)
    (ha₁ : partialDerivative 2 (a 1) = 0)
    (hg₂ : partialDerivative 2 (a 2) = c • smoothOne)
    (hg₀ : partialDerivative 0 (a 2) = hiddenAxisAffineCoefficient e k d)
    (hg₁ : partialDerivative 1 (a 2) = hiddenAxisAffineCoefficient g d q) :
    k = 0 ∧ d = 0 ∧ q = 0 := by
  let K := normalBracket (normalL0 f h) p
  let A := normalBracket (normalD f 0) p
  let B := normalBracket (normalD f 1) p
  have hl : NormalDegreeLE 2 (normalL0 f h) :=
    normalDegreeLE_of_action_order _ _ (by
      rw [normalAction_normalL0]; exact L0_mem_orderSpace_two f h)
  have hdi (i : Fin 3) : NormalDegreeLE 1 (normalD f i) :=
    normalDegreeLE_of_action_order _ _ (by
      rw [normalAction_normalD]; exact D_mem_orderSpace_one f i)
  have hK : NormalDegreeLE 2 K := by
    apply normalDegreeLE_of_action_order
    rw [normalAction_bracket, normalAction_normalL0]
    exact lie_mem_orderSpace_sharp (L0_mem_orderSpace_two f h)
      (action_order_of_normalDegreeLE p 1 hp)
  have hA : NormalDegreeLE 1 A := by
    apply normalDegreeLE_of_action_order
    rw [normalAction_bracket, normalAction_normalD]
    exact lie_mem_orderSpace_sharp (D_mem_orderSpace_one f 0)
      (action_order_of_normalDegreeLE p 1 hp)
  have hB : NormalDegreeLE 1 B := by
    apply normalDegreeLE_of_action_order
    rw [normalAction_bracket, normalAction_normalD]
    exact lie_mem_orderSpace_sharp (D_mem_orderSpace_one f 1)
      (action_order_of_normalDegreeLE p 1 hp)
  have hKE : normalAction K ∈ estimationAlgebra f h := by
    rw [normalAction_bracket, normalAction_normalL0]
    exact (estimationAlgebra f h).lie_mem
      (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hpE
  have hAE : normalAction A ∈ estimationAlgebra f h := by
    rw [normalAction_bracket, normalAction_normalD]
    exact (estimationAlgebra f h).lie_mem hD₀ hpE
  have hBE : normalAction B ∈ estimationAlgebra f h := by
    rw [normalAction_bracket, normalAction_normalD]
    exact (estimationAlgebra f h).lie_mem hD₁ hpE
  have hKs : normalSymbol 2 K = symbolPoisson axisEuclideanKinetic (axisVectorSymbol a) := by
    rw [show 2=1+0+1 from rfl, normalSymbol_bracket _ _ 1 0 hl hp,
      normalSymbol_normalL0, hpa]
    rfl
  have hAs : normalSymbol 1 A = axisVectorSymbol (fun j => partialDerivative 0 (a j)) := by
    rw [show 1=0+0+1 from rfl, normalSymbol_bracket _ _ 0 0 (hdi 0) hp,
      normalSymbol_normalD, hpa, poisson_X_axisVectorSymbol]
  have hBs : normalSymbol 1 B = axisVectorSymbol (fun j => partialDerivative 1 (a j)) := by
    rw [show 1=0+0+1 from rfl, normalSymbol_bracket _ _ 0 0 (hdi 1) hp,
      normalSymbol_normalD, hpa, poisson_X_axisVectorSymbol]
  exact actual_hiddenAxis_symmetric_ladder_zero (estimationAlgebra f h) K A B 1 0
    (by decide) hKE hAE hBE hK hA hB c e g k d q
    (by rw [hKs, kinetic_axisVectorSymbol_project, hg₂])
    (by simp only [hKs, kinetic_axisVectorSymbol_project_pderiv_zero, hg₀,
      ha₀, add_zero, pow_one])
    (by simp only [hKs, kinetic_axisVectorSymbol_project_pderiv_one, hg₁,
      ha₁, add_zero, pow_one])
    (by simp only [hAs, axisVectorSymbol_project, hg₀, zero_add, pow_one])
    (by simp only [hBs, axisVectorSymbol_project, hg₁, zero_add, pow_one])

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_quadratic_visible_hessian_zero
