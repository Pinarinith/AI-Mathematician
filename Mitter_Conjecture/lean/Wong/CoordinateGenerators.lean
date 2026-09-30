import Wong.OrthogonalCoordinates
import Wong.Ocone

/-!
# Orthogonal coordinates preserve the actual filtering model

This module transforms the drift, every observation, the defining potential
`eta`, and the filtering generator itself. Consequently the conjugated Lie
algebra is exactly the estimation algebra of the transformed data.
-/

noncomputable section
namespace Wong.SmoothModel
open scoped Matrix

theorem CoordinateOrthogonal.entry_symm (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (i j : Fin 3) :
    e (coordinateVector i) j = e.symm (coordinateVector j) i := by
  have hh := he (e.symm (coordinateVector j)) (coordinateVector i)
  simpa [dotProduct, coordinateVector, Pi.single_apply, mul_ite, ite_mul] using hh

theorem CoordinateOrthogonal.row_inner (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (j k : Fin 3) :
    (∑ i, e (coordinateVector i) j * e (coordinateVector i) k) =
      if j = k then 1 else 0 := by
  simp only [he.entry_symm e]
  have hh := he.symm (coordinateVector j) (coordinateVector k)
  simpa [dotProduct, coordinateVector, Pi.single_apply, mul_ite, ite_mul,
    eq_comm] using hh

/-- Orthogonality contracts both real matrix indices of any module-valued tensor. -/
theorem orthogonal_sum_contract {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : State ≃L[ℝ] State) (he : CoordinateOrthogonal e) (a : Fin 3 → Fin 3 → V) :
    (∑ i, ∑ j, ∑ k,
      (e (coordinateVector i) j * e (coordinateVector i) k) • a j k) = ∑ j, a j j := by
  calc
    _ = ∑ j, ∑ k, ∑ i,
        (e (coordinateVector i) j * e (coordinateVector i) k) • a j k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [← Finset.sum_smul, he.row_inner e]
      simp

/-- Every observation is transported by the same genuine smooth pullback. -/
def coordinateObservations {m : ℕ} (e : State ≃L[ℝ] State) (h : Fin m → Smooth) :
    Fin m → Smooth := fun j => coordinatePullback e (h j)

theorem coordinateObservations_symm {m : ℕ} (e : State ≃L[ℝ] State) (h : Fin m → Smooth) :
    coordinateObservations e.symm (coordinateObservations e h) = h := by
  funext j
  exact (coordinatePullback e).symm_apply_apply (h j)

theorem directionalDerivative_coefficientAlong (f : Fin 3 → Smooth) (v w : State) :
    directionalDerivative v (coefficientAlong f w) =
      ∑ i, ∑ j, (v i * w j) • partialDerivative i (f j) := by
  simp only [directionalDerivative, coefficientAlong, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem coordinateDrift_divergence (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (f : Fin 3 → Smooth) :
    (∑ i, partialDerivative i (coordinateDrift e f i)) =
      coordinatePullback e (∑ i, partialDerivative i (f i)) := by
  have hi (i : Fin 3) : partialDerivative i (coordinateDrift e f i) =
      coordinatePullback e (∑ j, ∑ k,
        (e (coordinateVector i) j * e (coordinateVector i) k) • partialDerivative j (f k)) := by
    rw [← coordinate_directionalDerivative i]
    rw [coordinateDrift, directionalDerivative_coordinatePullback,
      directionalDerivative_coefficientAlong]
  simp_rw [hi]
  rw [← map_sum]
  exact congrArg (coordinatePullback e)
    (orthogonal_sum_contract e he (fun j k => partialDerivative j (f k)))

theorem smoothMul_coefficientAlong (f : Fin 3 → Smooth) (v w : State) :
    smoothMul (coefficientAlong f v) (coefficientAlong f w) =
      ∑ i, ∑ j, (v i * w j) • smoothMul (f i) (f j) := by
  apply Subtype.ext
  funext x
  simp [coefficientAlong, smoothMul, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm]
  rw [Finset.sum_comm]

theorem coordinateDrift_sum_square (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (f : Fin 3 → Smooth) :
    (∑ i, smoothMul (coordinateDrift e f i) (coordinateDrift e f i)) =
      coordinatePullback e (∑ i, smoothMul (f i) (f i)) := by
  simp only [coordinateDrift, ← coordinatePullback_smoothMul, smoothMul_coefficientAlong]
  rw [← map_sum]
  exact congrArg (coordinatePullback e)
    (orthogonal_sum_contract e he (fun j k => smoothMul (f j) (f k)))

theorem eta_coordinateDrift {m : ℕ} (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    eta (coordinateDrift e f) (coordinateObservations e h) = coordinatePullback e (eta f h) := by
  simp only [eta, Finset.sum_add_distrib, coordinateDrift_divergence e he,
    coordinateDrift_sum_square e he, coordinateObservations,
    ← coordinatePullback_smoothMul, ← map_sum, ← map_add]

@[simp] theorem directionD_coordinate (f : Fin 3 → Smooth) (i : Fin 3) :
    directionD f (coordinateVector i) = D f i := by
  simp only [directionD_eq_directionalDerivative_sub, coordinate_directionalDerivative,
    coefficientAlong_coordinate, D]

theorem coordinateConjugation_D (e : State ≃L[ℝ] State) (f : Fin 3 → Smooth) (i : Fin 3) :
    coordinateConjugation e (D f i) = directionD (coordinateDrift e f) (e.symm (coordinateVector i)) := by
  have hh := coordinateConjugation_directionD e f (e.symm (coordinateVector i))
  simpa only [e.apply_symm_apply, directionD_coordinate] using hh

theorem directionD_mul_directionD (f : Fin 3 → Smooth) (v w : State) :
    directionD f v * directionD f w =
      ∑ i, ∑ j, (v i * w j) • (D f i * D f j) := by
  simp only [directionD, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem orthogonal_sum_directionD_square (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (f : Fin 3 → Smooth) :
    (∑ i, directionD f (e (coordinateVector i)) * directionD f (e (coordinateVector i))) =
      ∑ i, D f i * D f i := by
  simp only [directionD_mul_directionD]
  exact orthogonal_sum_contract e he _

theorem coordinateConjugation_L0 {m : ℕ} (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    coordinateConjugation e (L0 f h) =
      L0 (coordinateDrift e f) (coordinateObservations e h) := by
  simp only [L0, map_sub, map_smul, map_sum, map_mul, coordinateConjugation_D,
    coordinateConjugation_multiplication, orthogonal_sum_directionD_square e.symm he.symm,
    eta_coordinateDrift e he]

theorem coordinateAlgebra_estimationAlgebra {m : ℕ} (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    coordinateAlgebra e (estimationAlgebra f h) =
      estimationAlgebra (coordinateDrift e f) (coordinateObservations e h) := by
  unfold coordinateAlgebra estimationAlgebra
  rw [LieSubalgebra.map_lieSpan]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  congr 1
  · congr 1
    exact coordinateConjugation_L0 e he f h
  · congr 1
    funext j
    exact coordinateConjugation_multiplication e (h j)

theorem finiteDimensional_coordinateEstimationAlgebra {m : ℕ}
    (e : State ≃L[ℝ] State) (he : CoordinateOrthogonal e)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    FiniteDimensional ℝ (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) := by
  rw [← coordinateAlgebra_estimationAlgebra e he]
  exact coordinateAlgebra_finiteDimensional e (estimationAlgebra f h)

theorem multiplication_pullback_mem_coordinateAlgebra (e : State ≃L[ℝ] State)
    (E : LieSubalgebra ℝ Operator) (u : Smooth) :
    multiplication (coordinatePullback e u) ∈ coordinateAlgebra e E ↔ multiplication u ∈ E := by
  constructor
  · rintro ⟨A, hA, he⟩
    change coordinateConjugation e A = multiplication (coordinatePullback e u) at he
    have hEq : coordinateConjugation e A = coordinateConjugation e (multiplication u) := by
      simpa only [coordinateConjugation_multiplication] using he
    exact (coordinateConjugation e).injective hEq ▸ hA
  · intro hu
    exact ⟨multiplication u, hu, coordinateConjugation_multiplication e u⟩

theorem linear_mem_coordinateAlgebra (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (E : LieSubalgebra ℝ Operator) (v : State) :
    multiplication (linearFunction v) ∈ coordinateAlgebra e E ↔
      multiplication (linearFunction (e v)) ∈ E := by
  rw [← coordinatePullback_linearFunction_orthogonal e he v]
  exact multiplication_pullback_mem_coordinateAlgebra e E _

theorem linearCoefficientSpace_coordinateAlgebra (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (E : LieSubalgebra ℝ Operator) :
    linearCoefficientSpace (coordinateAlgebra e E) =
      (linearCoefficientSpace E).map e.symm.toLinearMap := by
  ext v
  change (multiplication (linearFunction v) ∈ coordinateAlgebra e E) ↔ _
  rw [linear_mem_coordinateAlgebra e he]
  constructor
  · intro hv
    exact ⟨e v, hv, e.symm_apply_apply v⟩
  · rintro ⟨w, hw, rfl⟩
    change multiplication (linearFunction (e (e.symm w))) ∈ E
    rw [e.apply_symm_apply]
    exact hw

theorem linearRank_coordinateAlgebra (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (E : LieSubalgebra ℝ Operator) :
    linearRank (coordinateAlgebra e E) = linearRank E := by
  unfold linearRank
  rw [linearCoefficientSpace_coordinateAlgebra e he]
  exact (e.symm.toLinearEquiv.submoduleMap (linearCoefficientSpace E)).finrank_eq.symm

theorem linearRank_coordinateEstimationAlgebra {m : ℕ} (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    linearRank (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) =
      linearRank (estimationAlgebra f h) := by
  rw [← coordinateAlgebra_estimationAlgebra e he, linearRank_coordinateAlgebra e he]

/-- A polynomial equal as a genuine function to an affine expression cannot
    have total degree two. Polynomial evaluation is injective over the reals. -/
theorem totalDegree_le_one_of_polynomialSmooth_affine (p : RealPoly) (c : ℝ) (a : State)
    (hp : polynomialSmooth p = c • smoothOne + linearFunction a) : p.totalDegree ≤ 1 := by
  have hp' : p = MvPolynomial.C c + ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i := by
    apply MvPolynomial.funext
    intro x
    have hx := congrArg (fun u : Smooth => u.1 x) hp
    simpa [polynomialSmooth, linearFunction, smoothOne] using hx
  rw [hp']
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- Quadratic-freeness is preserved for the actual finite-dimensional model.
    The proved Ocone theorem supplies affine function elements on the source;
    no unproved polynomial-substitution or degree-preservation premise is used. -/
theorem quadraticFree_coordinateAlgebra_estimation {m : ℕ}
    (e : State ≃L[ℝ] State) (he : CoordinateOrthogonal e)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hq : QuadraticFree (estimationAlgebra f h)) :
    QuadraticFree (coordinateAlgebra e (estimationAlgebra f h)) := by
  intro p hp ⟨A, hA, hact⟩
  have hAM : A = multiplication (polynomialSmooth p) := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    exact hact u x
  rw [hAM] at hA
  have hsource : multiplication (coordinatePullback e.symm (polynomialSmooth p)) ∈
      estimationAlgebra f h := by
    apply (multiplication_pullback_mem_coordinateAlgebra e (estimationAlgebra f h) _).mp
    change multiplication ((coordinatePullback e)
      ((coordinatePullback e).symm (polynomialSmooth p))) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    exact hA
  obtain ⟨c, a, ha⟩ := quadraticFree_function_element_affine f h hq _ hsource
  have htrans := congrArg (coordinatePullback e) ha
  have hlin : coordinatePullback e (linearFunction a) = linearFunction (e.symm a) := by
    simpa only [e.apply_symm_apply] using
      coordinatePullback_linearFunction_orthogonal e he (e.symm a)
  have hpa : polynomialSmooth p = c • smoothOne + linearFunction (e.symm a) := by
    simpa only [← coordinatePullback_symm, LinearEquiv.apply_symm_apply,
      map_add, map_smul, coordinatePullback_smoothOne, hlin] using htrans
  have hdeg := totalDegree_le_one_of_polynomialSmooth_affine p c (e.symm a) hpa
  omega

theorem quadraticFree_coordinateEstimationAlgebra {m : ℕ}
    (e : State ≃L[ℝ] State) (he : CoordinateOrthogonal e)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hq : QuadraticFree (estimationAlgebra f h)) :
    QuadraticFree (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) := by
  rw [← coordinateAlgebra_estimationAlgebra e he]
  exact quadraticFree_coordinateAlgebra_estimation e he f h hq

theorem quadraticFree_coordinateEstimationAlgebra_iff {m : ℕ}
    (e : State ≃L[ℝ] State) (he : CoordinateOrthogonal e)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] :
    QuadraticFree (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) ↔
      QuadraticFree (estimationAlgebra f h) := by
  constructor
  · intro hq
    let := finiteDimensional_coordinateEstimationAlgebra e he f h
    have hback := quadraticFree_coordinateEstimationAlgebra e.symm he.symm
      (coordinateDrift e f) (coordinateObservations e h) hq
    simpa only [coordinateDrift_symm, coordinateObservations_symm] using hback
  · exact quadraticFree_coordinateEstimationAlgebra e he f h

/-- Full reduction from the original hypotheses to an actual filtering model
    in adapted orthogonal coordinates, with every hypothesis preserved. -/
theorem estimationAlgebra_adapted_coordinates {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h)) :
    ∃ e : State ≃L[ℝ] State, CoordinateOrthogonal e ∧
      FiniteDimensional ℝ (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) ∧
      linearRank (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) = 2 ∧
      QuadraticFree (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) ∧
      multiplication (linearFunction (coordinateVector 0)) ∈
        estimationAlgebra (coordinateDrift e f) (coordinateObservations e h) ∧
      multiplication (linearFunction (coordinateVector 1)) ∈
        estimationAlgebra (coordinateDrift e f) (coordinateObservations e h) ∧
      (WongConstant (coordinateDrift e f) ↔ WongConstant f) := by
  obtain ⟨e, he, h₀, h₁⟩ := exists_coordinateAlgebra_adapted (estimationAlgebra f h) hrank
  refine ⟨e, he, finiteDimensional_coordinateEstimationAlgebra e he f h, ?_,
    quadraticFree_coordinateEstimationAlgebra e he f h hq, ?_, ?_,
    WongConstant_coordinateDrift_iff e f⟩
  · rw [linearRank_coordinateEstimationAlgebra e he]
    exact hrank
  · rwa [← coordinateAlgebra_estimationAlgebra e he]
  · rwa [← coordinateAlgebra_estimationAlgebra e he]

end Wong.SmoothModel
