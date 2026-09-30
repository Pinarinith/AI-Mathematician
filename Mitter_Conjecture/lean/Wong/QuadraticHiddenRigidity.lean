import Wong.AffinePrincipalRigidity
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A real Hessian eigenvector produces genuine unbounded operator order.
The visible coefficients of the original first-order operator may be arbitrary
affine functions. They need not themselves be removable by multiplication in E.
-/
noncomputable section
set_option maxHeartbeats 2000000
namespace Wong.SmoothModel
open MvPolynomial

def principalVectorSymbol (a : Fin 3 → Smooth) : SmoothSymbol :=
  ∑i : Fin 3, C (a i) * X i

def hiddenHessianMomentum (Q : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : RealPoly :=
  ∑j : Fin 3, C (Q i j) * X j * X 2

theorem hiddenHessianMomentum_homogeneous (Q : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    (hiddenHessianMomentum Q i).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_C_mul_X (Q i j) j).mul (isHomogeneous_X ℝ 2)

theorem hiddenHessianMomentum_eval (Q : Matrix (Fin 3) (Fin 3) ℝ) (v : State) (i : Fin 3) :
    eval v (hiddenHessianMomentum Q i) = (Q.mulVec v) i * v 2 := by
  simp only [hiddenHessianMomentum, map_sum, map_mul, eval_C, eval_X,
    Matrix.mulVec, dotProduct, Finset.sum_mul]

theorem coefficientDerivative_principalVectorSymbol (a : Fin 3 → Smooth) (i : Fin 3) :
    symbolCoefficientDerivative i (principalVectorSymbol a) =
      ∑j : Fin 3, C (partialDerivative i (a j)) * X j := by
  simp only [principalVectorSymbol, map_sum, symbolCoefficientDerivative_mul,
    symbolCoefficientDerivative_C, symbolCoefficientDerivative_X, mul_zero, add_zero]

theorem kinetic_vector_hessian (a : Fin 3 → Smooth)
    (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ∀i j k, partialDerivative i (partialDerivative j (a k)) =
      if k=2 then (Q i j) • smoothOne else 0) (i : Fin 3) :
    symbolCoefficientDerivative i (symbolPoisson euclideanKinetic (principalVectorSymbol a)) =
      constantMomentum (hiddenHessianMomentum Q i) := by
  rw [poisson_euclideanKinetic]
  simp only [map_sum, symbolCoefficientDerivative_mul, symbolCoefficientDerivative_X,
    zero_mul, zero_add, coefficientDerivative_principalVectorSymbol,
    symbolCoefficientDerivative_C, mul_zero, add_zero, hH]
  simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [hiddenHessianMomentum, map_sum, map_mul, constantMomentum_C, constantMomentum_X]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- If the first-order principal coefficients have a quadratic hidden component
and affine visible components, every Hessian eigenvector with nonzero hidden
coordinate has eigenvalue zero. The assertion concerns the actual estimation
algebra and includes arbitrary zero-order remainders. -/
theorem actual_quadratic_hidden_eigenvalue_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (p : NormalForm) (hp : NormalDegreeLE 1 p)
    (hpE : normalAction p ∈ estimationAlgebra f h)
    (a : Fin 3 → Smooth) (hpa : normalSymbol 1 p=principalVectorSymbol a)
    (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ∀i j k, partialDerivative i (partialDerivative j (a k)) =
      if k=2 then (Q i j) • smoothOne else 0)
    (v : State) (lam : ℝ) (hv : Q.mulVec v=lam • v) (hv₂ : v 2≠0) : lam=0 := by
  by_contra hlam
  let q := normalBracket (normalL0 f h) p
  have hl : NormalDegreeLE 2 (normalL0 f h) := normalDegreeLE_of_action_order _ _ (by
    rw [normalAction_normalL0]; exact L0_mem_orderSpace_two f h)
  have hq : NormalDegreeLE 2 q := by
    apply normalDegreeLE_of_action_order
    rw [normalAction_bracket, normalAction_normalL0]
    exact lie_mem_orderSpace_sharp (L0_mem_orderSpace_two f h)
      (action_order_of_normalDegreeLE p 1 hp)
  have hqE : normalAction q ∈ estimationAlgebra f h := by
    rw [normalAction_bracket, normalAction_normalL0]
    exact (estimationAlgebra f h).lie_mem
      (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hpE
  have hqS : normalSymbol 2 q=symbolPoisson euclideanKinetic (principalVectorSymbol a) := by
    rw [show 2=1+0+1 from rfl, normalSymbol_bracket _ _ 1 0 hl hp,
      normalSymbol_normalL0, hpa]
    rfl
  have hB (i : Fin 3) : symbolCoefficientDerivative i (normalSymbol 2 q)=
      constantMomentum (hiddenHessianMomentum Q i) := by
    rw [hqS]
    exact kinetic_vector_hessian a Q hH i
  have hBv (i : Fin 3) : eval v (hiddenHessianMomentum Q i)=(lam*v 2)*v i := by
    rw [hiddenHessianMomentum_eval, hv]
    change (lam*v i)*v 2=(lam*v 2)*v i
    ring
  have hnorm : 0 < ∑i : Fin 3, (v i)^2 := by
    have hh : 0 < (v 2)^2 := sq_pos_of_ne_zero hv₂
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hseed : eval v (affineMomentumSeed (hiddenHessianMomentum Q))≠0 := by
    have he : eval v (affineMomentumSeed (hiddenHessianMomentum Q))=
        (lam*v 2)*(∑i : Fin 3,(v i)^2) := by
      simp only [affineMomentumSeed, map_sum, map_mul, eval_X, hBv, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero hlam hv₂) (ne_of_gt hnorm)
  have hz := actual_affine_principal_radial_obstruction f h q hq hqE
    (hiddenHessianMomentum Q) (hiddenHessianMomentum_homogeneous Q) hB
    v (lam*v 2) hBv hseed
  exact mul_ne_zero hlam hv₂ hz

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_quadratic_hidden_eigenvalue_zero
