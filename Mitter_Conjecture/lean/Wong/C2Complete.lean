import Wong.HiddenIndependentSectors
import Wong.AffineGaugeRepresentative
import Wong.RankTwoFunctionCurvature


/-! Source segment: C2QuadraticWord.lean -/

/-! Exact C2 finite Lie words. Scalar remainders are retained throughout.
The identities below extract a genuine first-order operator with quadratic
shear coefficients; no equality modulo unspecified differential order is used.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel

def c2Z (L X : Operator) : Operator := (1 / 2 : ℝ) • ⁅L, X * X⁆ - (1 / 2 : ℝ) • 1
def c2T (L X : Operator) : Operator := ⁅L, c2Z L X⁆ - ⁅c2Z L X, ⁅L, c2Z L X⁆⁆
def c2K (L X : Operator) : Operator := (1 / 12 : ℝ) • ((2 : ℝ) • c2T L X + ⁅c2T L X, c2Z L X⁆)
def c2R (L X : Operator) : Operator := (3 : ℝ) • c2K L X - c2T L X

theorem c2Z_eq (L X D : Operator) (hLX : ⁅L, X⁆ = D) (hDX : ⁅D, X⁆ = 1) :
    c2Z L X = X * D := by
  have hcomm : D * X = X * D + 1 := by
    rw [operator_lie_def] at hDX
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hDX)
  rw [c2Z, operator_lie_mul_right, hLX, hcomm]
  module

/-- Exact algebraic extraction; U and V are the actual successive D brackets. -/
theorem c2R_exact (L X D H U V : Operator)
    (hLX : ⁅L, X⁆ = D) (hDX : ⁅D, X⁆ = 1)
    (hLD : ⁅L, D⁆ = H) (hHX : ⁅H, X⁆ = 0)
    (hDH : ⁅D, H⁆ = U) (hUX : ⁅U, X⁆ = 0) (hDU : ⁅D, U⁆ = V) :
    c2R L X = X * X * U + (1 / 4 : ℝ) • (X * X * X * V) := by
  have hnegleft (A B : Operator) : (-A) * B = -(A * B) := by
    ext u
    rfl
  have hnegright (A B : Operator) : A * (-B) = -(A * B) := by
    apply LinearMap.ext
    intro u
    exact map_neg A (B u)
  have hXD : ⁅X, D⁆ = -1 := by rw [← lie_skew, hDX]
  have hXH : ⁅X, H⁆ = 0 := by rw [← lie_skew, hHX, neg_zero]
  have hUD : ⁅U, D⁆ = -V := by rw [← lie_skew, hDU]
  have hZX : ⁅X * D, X⁆ = X := by
    rw [operator_lie_mul_left, hDX, lie_self, mul_one, zero_mul, add_zero]
  have hXZ : ⁅X, X * D⁆ = -X := by rw [← lie_skew, hZX]
  have hZD : ⁅X * D, D⁆ = -D := by
    rw [operator_lie_mul_left, lie_self, hXD, mul_zero, zero_add, hnegleft, one_mul]
  have hDZ : ⁅D, X * D⁆ = D := by rw [← lie_skew, hZD, neg_neg]
  have hZH : ⁅X * D, H⁆ = X * U := by
    rw [operator_lie_mul_left, hDH, hXH, zero_mul, add_zero]
  have hUZ : ⁅U, X * D⁆ = -(X * V) := by
    rw [operator_lie_mul_right, hUX, hUD, zero_mul, zero_add, hnegright]
  have hLZ : ⁅L, X * D⁆ = D * D + X * H := by
    rw [operator_lie_mul_right, hLX, hLD]
  have hTZ : c2T L X = (3 : ℝ) • (D * D) - X * X * U := by
    rw [c2T, c2Z_eq L X D hLX hDX, hLZ, lie_add,
      operator_lie_mul_right, hZD, operator_lie_mul_right, hZX, hZH]
    simp only [hnegleft, hnegright, mul_assoc]
    module
  have hTZbr : ⁅c2T L X, X * D⁆ =
      (6 : ℝ) • (D * D) + X * X * X * V + (2 : ℝ) • (X * X * U) := by
    rw [hTZ, sub_lie, smul_lie, operator_lie_mul_left, hDZ,
      operator_lie_mul_left, hUZ, operator_lie_mul_left, hXZ]
    simp only [hnegright, hnegleft, add_mul, mul_assoc]
    module
  rw [c2R, c2K, c2Z_eq L X D hLX hDX, hTZbr, hTZ]
  module

theorem c2R_mem (E : LieSubalgebra ℝ Operator) (L X : Operator)
    (hL : L ∈ E) (hXX : X * X ∈ E) (hI : (1 : Operator) ∈ E) : c2R L X ∈ E := by
  have hZ : c2Z L X ∈ E := E.sub_mem
    (E.smul_mem (1 / 2 : ℝ) (E.lie_mem hL hXX)) (E.smul_mem (1 / 2 : ℝ) hI)
  have hT : c2T L X ∈ E := E.sub_mem (E.lie_mem hL hZ)
    (E.lie_mem hZ (E.lie_mem hL hZ))
  have hK : c2K L X ∈ E := E.smul_mem (1 / 12 : ℝ)
    (E.add_mem (E.smul_mem (2 : ℝ) hT) (E.lie_mem hT hZ))
  exact E.sub_mem (E.smul_mem (3 : ℝ) hK) hT

theorem multiplication_firstOrder (f a : Fin 3 → Smooth) (b u : Smooth) :
    multiplication u * firstOrder f a b =
      firstOrder f (fun j => smoothMul u (a j)) (smoothMul u b) := by
  simp only [firstOrder, mul_add, Finset.mul_sum, ← mul_assoc, multiplication_mul]

/-- The complete scalar of [D₀,[L₀,D₀]]. -/
def c2UScalar {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) : Smooth :=
  partialDerivative 0 (generatorRemainder f h 0) +
    ∑ j, smoothMul (wong f 0 j) (wong f j 0)

def c2VScalar {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (a : Fin 3 → ℝ) : Smooth :=
  partialDerivative 0 (c2UScalar f h) + ∑ j, smoothMul (a j • smoothOne) (wong f j 0)

def c2RScalar {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (a : Fin 3 → ℝ) : Smooth :=
  let x := linearFunction (coordinateVector 0)
  smoothMul (smoothMul x x) (c2UScalar f h) +
    (1 / 4 : ℝ) • smoothMul (smoothMul (smoothMul x x) x) (c2VScalar f h a)

theorem c2R_firstOrder {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (a : Fin 3 → ℝ) (ha₀ : a 0 = 0)
    (hrow : ∀ j, partialDerivative 0 (wong f 0 j) = a j • smoothOne) :
    c2R (L0 f h) (multiplication (linearFunction (coordinateVector 0))) =
      firstOrder f (fun j => a j • smoothMul (linearFunction (coordinateVector 0))
        (linearFunction (coordinateVector 0))) (c2RScalar f h a) := by
  let x := linearFunction (coordinateVector 0)
  let X := multiplication x
  let d := D f 0
  let H := firstOrder f (wong f 0) (generatorRemainder f h 0)
  let U := firstOrder f (fun j => a j • smoothOne) (c2UScalar f h)
  have hLX : ⁅L0 f h, X⁆ = d := by
    exact (lie_L0_linearFunction f h (coordinateVector 0)).trans (directionD_coordinate f 0)
  have hDX : ⁅d, X⁆ = 1 := by
    simp [d, X, x, lie_D_multiplication, partialDerivative_linearFunction, coordinateVector]
  have hLD : ⁅L0 f h, d⁆ = H := lie_L0_D_eq_firstOrder f h 0
  have hHX : ⁅H, X⁆ = 0 := by
    change commuteWithMultiplier (linearFunction (coordinateVector 0)) H = 0
    rw [commuteWithLinear_firstOrder, coefficientAlong_coordinate, wong_self, multiplication_zero]
  have hDH : ⁅d, H⁆ = U := by
    simp only [d, H, U, lie_D_firstOrder, hrow, c2UScalar]
  have hUX : ⁅U, X⁆ = 0 := by
    change commuteWithMultiplier (linearFunction (coordinateVector 0)) U = 0
    rw [commuteWithLinear_firstOrder, coefficientAlong_coordinate, ha₀, zero_smul, multiplication_zero]
  have hDU : ⁅d, U⁆ = multiplication (c2VScalar f h a) := by
    change ⁅D f 0, firstOrder f (fun j => a j • smoothOne) (c2UScalar f h)⁆ = _
    rw [lie_D_firstOrder]
    simp only [partialDerivative_const, c2VScalar,
      firstOrder, multiplication_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have he := c2R_exact (L0 f h) X d H U (multiplication (c2VScalar f h a))
    hLX hDX hLD hHX hDH hUX hDU
  have hc (j : Fin 3) : smoothMul (smoothMul x x) (a j • smoothOne) =
      a j • smoothMul x x := by
    apply Subtype.ext
    funext z
    simp [smoothMul, smoothOne]
    ring
  rw [he]
  change multiplication x * multiplication x *
      firstOrder f (fun j => a j • smoothOne) (c2UScalar f h) +
      (1 / 4 : ℝ) • (multiplication x * multiplication x * multiplication x *
        multiplication (c2VScalar f h a)) = _
  rw [multiplication_mul, multiplication_firstOrder]
  simp only [multiplication_mul, hc, firstOrder, c2RScalar,
    multiplication_add, multiplication_smul]
  abel

end Wong.SmoothModel

#print axioms Wong.SmoothModel.c2R_exact
#print axioms Wong.SmoothModel.c2R_firstOrder


/-! Source segment: C2QuadraticShear.lean -/

/-! A genuine orthogonal swap transfers the one-admitted-derivative shear
obstruction. No old hidden covariant derivative is assumed to be admitted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel

def c2AxisSwapLinear : State ≃ₗ[ℝ] State where
  toFun x := ![x 0, x 2, x 1]
  invFun x := ![x 0, x 2, x 1]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' c x := by funext i; fin_cases i <;> simp
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv x := by funext i; fin_cases i <;> simp

def c2AxisSwap : State ≃L[ℝ] State := c2AxisSwapLinear.toContinuousLinearEquiv

theorem c2AxisSwap_orthogonal : CoordinateOrthogonal c2AxisSwap := by
  intro v w
  simp [dotProduct, Fin.sum_univ_three, c2AxisSwap, c2AxisSwapLinear]
  ring

theorem c2AxisSwap_vector_zero : c2AxisSwap.symm (coordinateVector 0) = coordinateVector 0 := by
  funext i
  fin_cases i <;> simp [c2AxisSwap, c2AxisSwapLinear, coordinateVector]

theorem c2AxisSwap_vector_one : c2AxisSwap.symm (coordinateVector 1) = coordinateVector 2 := by
  funext i
  fin_cases i <;> simp [c2AxisSwap, c2AxisSwapLinear, coordinateVector]

theorem c2AxisSwap_x : coordinatePullback c2AxisSwap (linearFunction (coordinateVector 0)) =
    linearFunction (coordinateVector 0) := by
  apply Subtype.ext
  funext z
  simp [coordinatePullback_apply, c2AxisSwap, c2AxisSwapLinear,
    linearFunction, coordinateVector, Fin.sum_univ_three]

def c2Square : Smooth := smoothMul (linearFunction (coordinateVector 0))
  (linearFunction (coordinateVector 0))

theorem partial_c2Square (i : Fin 3) :
    partialDerivative i c2Square =
      if i = 0 then (2 : ℝ) • linearFunction (coordinateVector 0) else 0 := by
  rw [c2Square, partialDerivative_smoothMul, partialDerivative_linearFunction]
  by_cases hi : i = 0
  · subst i
    simp [coordinateVector, smoothMul_eq_mul, smoothOne_eq_one, two_smul]
  · simp [coordinateVector, hi, smoothMul_eq_mul]

theorem c2AxisSwap_square : coordinatePullback c2AxisSwap c2Square = c2Square := by
  rw [c2Square, coordinatePullback_smoothMul, c2AxisSwap_x]

theorem c2AxisSwap_firstOrder (f : Fin 3 → Smooth) (b : ℝ) (s : Smooth) :
    coordinateConjugation c2AxisSwap (firstOrder f ![0, b • c2Square, 0] s) =
      firstOrder (coordinateDrift c2AxisSwap f) ![0, 0, b • c2Square]
        (coordinatePullback c2AxisSwap s) := by
  simp only [firstOrder, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, multiplication_zero, zero_mul,
    zero_add, add_zero, map_add, map_mul, coordinateConjugation_multiplication,
    coordinateConjugation_D, c2AxisSwap_vector_one, directionD_coordinate,
    map_smul, c2AxisSwap_square]

theorem actual_visible_quadratic_shear_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD₀ : D f 0 ∈ estimationAlgebra f h)
    (b : ℝ) (s : Smooth)
    (hR : firstOrder f ![0, b • c2Square, 0] s ∈ estimationAlgebra f h) : b = 0 := by
  let f' := coordinateDrift c2AxisSwap f
  let h' := coordinateObservations c2AxisSwap h
  let _ : FiniteDimensional ℝ (estimationAlgebra f' h') :=
    finiteDimensional_coordinateEstimationAlgebra c2AxisSwap c2AxisSwap_orthogonal f h
  have hD' : D f' 0 ∈ estimationAlgebra f' h' := by
    rw [← coordinateAlgebra_estimationAlgebra c2AxisSwap c2AxisSwap_orthogonal]
    refine ⟨D f 0, hD₀, ?_⟩
    change coordinateConjugation c2AxisSwap (D f 0) = D f' 0
    rw [coordinateConjugation_D, c2AxisSwap_vector_zero, directionD_coordinate]
  have hR' : firstOrder f' ![0, 0, b • c2Square] (coordinatePullback c2AxisSwap s) ∈
      estimationAlgebra f' h' := by
    rw [← coordinateAlgebra_estimationAlgebra c2AxisSwap c2AxisSwap_orthogonal]
    exact ⟨_, hR, c2AxisSwap_firstOrder f b s⟩
  have hk := actual_firstOrder_quadratic_hidden_shear_zero f' h' hD'
    ![0, 0, b • c2Square] (coordinatePullback c2AxisSwap s) hR' 0 0 (2*b)
    (by simp) (by simp) (by
      simp [map_smul, partial_c2Square]) (by
      apply Subtype.ext
      funext z
      simp [map_smul, partial_c2Square, coordinateVector, hiddenAxisAffineCoefficient,
        linearFunction, Fin.sum_univ_three, smoothOne]
      ring) (by
      simp [map_smul, partial_c2Square])
  linarith

theorem actual_two_direction_quadratic_shear_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD₀ : D f 0 ∈ estimationAlgebra f h) (hD₁ : D f 1 ∈ estimationAlgebra f h)
    (b c : ℝ) (s : Smooth)
    (hR : firstOrder f ![0, b • c2Square, c • c2Square] s ∈ estimationAlgebra f h) :
    b = 0 ∧ c = 0 := by
  let a : Fin 3 → Smooth := ![0, b • c2Square, c • c2Square]
  have hc := actual_quadratic_visible_hessian_zero f h hD₀ hD₁ (normalFirstOrder f a s)
    (normalFirstOrder_degree_le_one f a s) (by rwa [normalAction_normalFirstOrder]) a
    (normalSymbol_one_normalFirstOrder f a s) 0 0 0 (2*c) 0 0
    (by simp [a]) (by
      simp [a, map_smul, partial_c2Square]) (by
      simp [a, map_smul, partial_c2Square]) (by
      apply Subtype.ext
      funext z
      simp [a, map_smul, partial_c2Square, coordinateVector, hiddenAxisAffineCoefficient,
        linearFunction, Fin.sum_univ_three, smoothOne]
      ring) (by
      apply Subtype.ext
      funext z
      simp [a, map_smul, partial_c2Square, hiddenAxisAffineCoefficient,
        linearFunction, Fin.sum_univ_three])
  have hc0 : c = 0 := by linarith [hc.1]
  refine ⟨?_, hc0⟩
  apply actual_visible_quadratic_shear_zero f h hD₀ b s
  simpa only [hc0, zero_smul] using hR

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_two_direction_quadratic_shear_zero


/-! Source segment: C2Constancy.lean -/

/-! Full C2 constancy once the internally proved affine Wong structure is
supplied. The actual finite Lie word removes the x₀ row slopes, the complete
C2 function space removes the remaining visible slope, and the real weak-HF
sector theorem removes every mixed slope. No two-dimensional classification
and no quadratic-free hypothesis are used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel

/-- A genuine admitted coordinate square forces both corresponding affine
Wong row slopes to vanish. The scalar remainder of R is unrestricted. -/
theorem coordinate_square_forces_affine_row_slopes_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hsquare : multiplication c2Square ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j z, (wong f i j).1 z = p.matrix z i j) :
    p.b₁ = 0 ∧ p.k₁ = 0 := by
  let a : Fin 3 → ℝ := ![0, p.b₁, p.k₁]
  have hrow (j : Fin 3) : partialDerivative 0 (wong f 0 j) = a j • smoothOne := by
    rw [VisibleHeads.partial_wong_affine f p hp]
    fin_cases j <;> simp [a, VisibleHeads.slopes]
  have hI : (1 : Operator) ∈ estimationAlgebra f h := by
    simpa only [multiplication_smoothOne] using
      smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have hR : c2R (L0 f h) (multiplication (linearFunction (coordinateVector 0))) ∈
      estimationAlgebra f h := by
    apply c2R_mem _ _ _ (LieSubalgebra.subset_lieSpan (Or.inl rfl)) ?_ hI
    rwa [multiplication_mul]
  rw [c2R_firstOrder f h a (by simp [a]) hrow] at hR
  have hshape : (fun j => a j • smoothMul (linearFunction (coordinateVector 0))
      (linearFunction (coordinateVector 0))) = ![0, p.b₁ • c2Square, p.k₁ • c2Square] := by
    funext j
    fin_cases j <;> simp [a, c2Square]
  rw [hshape] at hR
  exact actual_two_direction_quadratic_shear_zero f h
    (D_mem_of_coordinate_mem f h 0 hx₀) (D_mem_of_coordinate_mem f h 1 hx₁)
    p.b₁ p.k₁ _ hR

theorem c2_function_visible_mixed_zero (E : LieSubalgebra ℝ Operator)
    (hC2 : HiddenIndependent.C2FunctionSpace E) (u : Smooth) (hu : multiplication u ∈ E) :
    partialDerivative 0 (partialDerivative 1 u) = 0 := by
  obtain ⟨c, a, b, q, rfl⟩ := hC2.2 u hu
  simp only [map_add, map_smul, partialDerivative_smoothMul,
    partialDerivative_linearFunction, SectorTwo.partial_one]
  simp [coordinateVector, smoothMul_eq_mul]

theorem c2Square_curvatureGradient_one (f : Fin 3 → Smooth) :
    functionCurvatureGradient f c2Square 1 =
      smoothMul ((2 : ℝ) • linearFunction (coordinateVector 0)) (wong f 0 1) := by
  simp only [functionCurvatureGradient, Fin.sum_univ_three, partial_c2Square]
  apply Subtype.ext
  funext z
  simp [coordinateVector, smoothMul]

theorem c2_second_visible_slope_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hC2 : HiddenIndependent.C2FunctionSpace (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j z, (wong f i j).1 z = p.matrix z i j) :
    p.b₂ = 0 := by
  have hG := function_curvature_gradient_mem_of_adapted_rank_two
    f h hrank hx₀ hx₁ c2Square hC2.1 1 (Or.inr rfl)
  have hz := c2_function_visible_mixed_zero _ hC2 _ hG
  have hfirst : partialDerivative 1 (functionCurvatureGradient f c2Square 1) =
      (2*p.b₂) • linearFunction (coordinateVector 0) := by
    rw [c2Square_curvatureGradient_one, partialDerivative_smoothMul, map_smul,
      partialDerivative_linearFunction, VisibleHeads.partial_wong_affine f p hp]
    apply Subtype.ext
    funext z
    simp [coordinateVector, VisibleHeads.slopes, smoothMul, smoothOne]
    ring
  rw [hfirst, map_smul, partialDerivative_linearFunction] at hz
  have hv := congrArg (fun u : Smooth => u.1 (0 : State)) hz
  have hb : 2*p.b₂ = 0 := by simpa [coordinateVector, smoothOne] using hv
  linarith

/-- The complete C2 function-space case, with actual affine data supplied by
the proved structure theorem, has constant Wong matrix. -/
theorem c2_wongConstant_of_affine {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hC2 : HiddenIndependent.C2FunctionSpace (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀ i j z, (wong f i j).1 z = p.matrix z i j) :
    WongConstant f := by
  have hb₁ := (coordinate_square_forces_affine_row_slopes_zero f h hrank hx₀ hx₁ hC2.1 p hp).1
  have hb₂ := c2_second_visible_slope_zero f h hrank hC2 hx₀ hx₁ p hp
  exact HiddenIndependent.c2_wongConstant_of_affine_visible_constant
    f h hrank hC2 hx₀ hx₁ p hp hb₁ hb₂

end Wong.SmoothModel

#print axioms Wong.SmoothModel.coordinate_square_forces_affine_row_slopes_zero
#print axioms Wong.SmoothModel.c2_wongConstant_of_affine
