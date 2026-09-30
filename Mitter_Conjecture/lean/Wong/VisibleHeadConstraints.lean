import Wong.VisibleGeneratorHeads
import Wong.PureHead

/-! Constraints on the actual double-coordinate heads of all second-order Lie elements. -/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads

@[simp] theorem multiplication_neg (u : Smooth) : multiplication (-u) = -multiplication u :=
  multiplicationLinear.map_neg u

def visibleAffine (c a b : ℝ) : Smooth :=
  c • smoothOne + a • linearFunction (coordinateVector 0) +
    b • linearFunction (coordinateVector 1)

@[simp] theorem partial_visibleAffine (c a b : ℝ) (i : Fin 3) :
    partialDerivative i (visibleAffine c a b) = ![a, b, 0] i • smoothOne := by
  have hone : partialDerivative i smoothOne = 0 := by
    simpa only [one_smul] using partialDerivative_const i 1
  simp only [visibleAffine, map_add, map_smul, hone, smul_zero,
    partialDerivative_linearFunction, zero_add]
  fin_cases i <;> simp [coordinateVector]

theorem δ_commute (i j : Fin 3) (A : Operator) : δ i (δ j A) = δ j (δ i A) := by
  change commuteWithMultiplier _ ⁅A, multiplication _⁆ = _
  rw [commuteWithMultiplier_lie]
  simp only [commuteWithMultiplier_apply, lie_multiplication_multiplication, lie_zero, zero_add]
  rfl

theorem δ_δ_lie (i j : Fin 3) (A B : Operator)
    (hA : δ i (δ j A) = 0) :
    δ i (δ j ⁅A, B⁆) = ⁅A, δ i (δ j B)⁆ +
      ⁅δ i A, δ j B⁆ + ⁅δ j A, δ i B⁆ := by
  change commuteWithMultiplier _ (commuteWithMultiplier _ ⁅A, B⁆) = _
  rw [commuteWithMultiplier_lie, map_add, commuteWithMultiplier_lie,
    commuteWithMultiplier_lie]
  change ⁅A, δ i (δ j B)⁆ + ⁅δ i A, δ j B⁆ +
    (⁅δ j A, δ i B⁆ + ⁅δ i (δ j A), B⁆) = _
  rw [hA, zero_lie, add_zero]

theorem double_head_affine {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (B : Operator) (hBE : B ∈ estimationAlgebra f h) (hB : B ∈ orderSpace 2)
    (i j : Fin 3) (hi : i = 0 ∨ i = 1) (hj : j = 0 ∨ j = 1) :
    ∃ c a b : ℝ, δ i (δ j B) = multiplication (visibleAffine c a b) := by
  have hMi : multiplication (linearFunction (coordinateVector i)) ∈ estimationAlgebra f h := by
    rcases hi with rfl | rfl <;> assumption
  have hMj : multiplication (linearFunction (coordinateVector j)) ∈ estimationAlgebra f h := by
    rcases hj with rfl | rfl <;> assumption
  have he : δ i (δ j B) ∈ estimationAlgebra f h :=
    (estimationAlgebra f h).lie_mem ((estimationAlgebra f h).lie_mem hBE hMj) hMi
  have ho : δ i (δ j B) ∈ orderSpace 0 :=
    mem_orderSpace_succ.mp (mem_orderSpace_succ.mp hB _) _
  have hh := orderSpace_zero_representation ho
  obtain ⟨c, a, b, heq⟩ := function_element_adapted f h hrank hq h₀ h₁
    (δ i (δ j B) smoothOne) (hh ▸ he)
  exact ⟨c, a, b, hh.trans (congrArg multiplication heq)⟩

theorem pure_head_linear_slope_zero {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)] (i : Fin 3)
    (B : Operator) (hBE : B ∈ estimationAlgebra f h) (hB : B ∈ orderSpace 2)
    (a c : ℝ) (hh : δ i (δ i B) =
      multiplication (a • linearFunction (coordinateVector i) + c • smoothOne)) : a = 0 := by
  have hzero := pure_head_slope_zero f h i B hBE hB (a / 2) c (by
    change δ i (δ i B) = _
    rw [hh, multiplication_add, multiplication_smul, multiplication_smul,
      multiplication_smoothOne]
    congr 1
    congr 1
    ring)
  linarith

def firstGenerator {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) (r : Fin 3) : Operator :=
  ⁅L0 f h, D f r⁆

@[simp] theorem δ_firstGenerator {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (r i : Fin 3) : δ i (firstGenerator f h r) = multiplication (wong f r i) := by
  rw [firstGenerator, lie_L0_D_eq_firstOrder, δ_firstOrder]

theorem firstGenerator_lie_visibleAffine {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (r : Fin 3) (c a b : ℝ) :
    ⁅firstGenerator f h r, multiplication (visibleAffine c a b)⁆ =
      multiplication (a • wong f r 0 + b • wong f r 1) := by
  simp only [firstGenerator, lie_L0_D_eq_firstOrder, firstOrder, add_lie,
    operator_lie_mul_left, lie_multiplication_multiplication, zero_mul, add_zero,
    lie_D_multiplication, multiplication_mul,
    partial_visibleAffine, Fin.sum_univ_three]
  simp only [← multiplication_add]
  apply congrArg multiplication
  apply Subtype.ext
  funext x
  simp [smoothMul, smoothOne]
  ring

theorem firstGenerator_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (r : Fin 3) (hr : multiplication (linearFunction (coordinateVector r)) ∈ estimationAlgebra f h) :
    firstGenerator f h r ∈ estimationAlgebra f h :=
  (estimationAlgebra f h).lie_mem (LieSubalgebra.subset_lieSpan (Or.inl rfl))
    (D_mem_of_coordinate_mem f h r hr)

theorem firstGenerator_mem_orderSpace_one {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (r : Fin 3) : firstGenerator f h r ∈ orderSpace 1 :=
  lie_L0_D_mem_orderSpace_one f h r

theorem normalized_wong01 (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) (hb₁ : p.b₁ = 0) :
    wong f 0 1 = p.b₂ • linearFunction (coordinateVector 1) + p.b₀ • smoothOne := by
  apply Subtype.ext
  funext x
  simp [hp, Wong.AffineParameters.matrix, Wong.AffineParameters.w12, hb₁,
    linearFunction, coordinateVector, Pi.single_apply, smoothOne]

theorem lie_normalized_wong01 (f : Fin 3 → Smooth) (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) (hb₁ : p.b₁ = 0) (A : Operator) :
    ⁅A, multiplication (wong f 0 1)⁆ = p.b₂ • δ 1 A := by
  rw [normalized_wong01 f p hp hb₁, multiplication_add, multiplication_smul,
    multiplication_smul, multiplication_smoothOne, lie_add, lie_smul,
    lie_scalar_identity, add_zero]
  rfl

theorem head00_firstGenerator0 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (B : Operator) (c a b : ℝ) (hh : δ 0 (δ 0 B) = multiplication (visibleAffine c a b)) :
    δ 0 (δ 0 ⁅firstGenerator f h 0, B⁆) = multiplication (b • wong f 0 1) := by
  rw [δ_δ_lie 0 0 _ _ (by simp), δ_firstGenerator, wong_self, multiplication_zero,
    zero_lie, add_zero, add_zero, hh, firstGenerator_lie_visibleAffine]
  simp

theorem head11_firstGenerator1 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (B : Operator) (c a b : ℝ) (hh : δ 1 (δ 1 B) = multiplication (visibleAffine c a b)) :
    δ 1 (δ 1 ⁅firstGenerator f h 1, B⁆) = multiplication ((-a) • wong f 0 1) := by
  rw [δ_δ_lie 1 1 _ _ (by simp), δ_firstGenerator, wong_self, multiplication_zero,
    zero_lie, add_zero, add_zero, hh, firstGenerator_lie_visibleAffine]
  simp [wong_skew f 0 1]

theorem head00_firstGenerator1 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (B : Operator) (c a b : ℝ)
    (hh : δ 0 (δ 0 B) = multiplication (visibleAffine c a b)) :
    δ 0 (δ 0 ⁅firstGenerator f h 1, B⁆) =
      multiplication ((-a) • wong f 0 1) + (2 * p.b₂) • δ 0 (δ 1 B) := by
  rw [δ_δ_lie 0 0 _ _ (by simp), δ_firstGenerator, hh,
    firstGenerator_lie_visibleAffine, wong_self, smul_zero, add_zero, wong_skew f 0 1]
  have hb : ⁅multiplication (-(wong f 0 1)), δ 0 B⁆ = p.b₂ • δ 0 (δ 1 B) := by
    rw [multiplication_neg, neg_lie, ← lie_skew, neg_neg,
      lie_normalized_wong01 f p hp hb₁, δ_commute 1 0]
  rw [hb]
  simp only [smul_neg, neg_smul, multiplication_neg, multiplication_smul]
  module



/-- Under the normalized visible Wong slope, every pure `0` head is
independent of the `0` coordinate. -/
theorem head00_no_own_slope {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ ≠ 0)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (B : Operator) (hBE : B ∈ estimationAlgebra f h) (hB : B ∈ orderSpace 2)
    (c a b : ℝ) (hh : δ 0 (δ 0 B) = multiplication (visibleAffine c a b)) : a = 0 := by
  let C := ⁅firstGenerator f h 0, B⁆ - p.b₂ • B
  have hCE : C ∈ estimationAlgebra f h :=
    (estimationAlgebra f h).sub_mem
      ((estimationAlgebra f h).lie_mem (firstGenerator_mem f h 0 h₀) hBE)
      ((estimationAlgebra f h).smul_mem p.b₂ hBE)
  have hC : C ∈ orderSpace 2 := (orderSpace 2).sub_mem
    (lie_mem_orderSpace_sharp (firstGenerator_mem_orderSpace_one f h 0) hB)
    ((orderSpace 2).smul_mem p.b₂ hB)
  have hCC : δ 0 (δ 0 C) = multiplication
      ((-p.b₂ * a) • linearFunction (coordinateVector 0) +
        (b * p.b₀ - p.b₂ * c) • smoothOne) := by
    simp only [C, map_sub, map_smul, head00_firstGenerator0 f h B c a b hh, hh,
      ← multiplication_smul, ← multiplication_sub, normalized_wong01 f p hp hb₁]
    congr 1
    apply Subtype.ext
    funext x
    simp [visibleAffine, smoothOne, linearFunction, coordinateVector]
    ring
  have hz := pure_head_linear_slope_zero f h 0 C hCE hC (-p.b₂ * a)
    (b * p.b₀ - p.b₂ * c) hCC
  exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hb₂)

/-- Every pure `1` head is constant in both visible coordinates. -/
theorem head11_slopes_zero {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ ≠ 0)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (B : Operator) (hBE : B ∈ estimationAlgebra f h) (hB : B ∈ orderSpace 2)
    (c a b : ℝ) (hh : δ 1 (δ 1 B) = multiplication (visibleAffine c a b)) : a = 0 ∧ b = 0 := by
  let C := ⁅firstGenerator f h 1, B⁆
  have hCE : C ∈ estimationAlgebra f h :=
    (estimationAlgebra f h).lie_mem (firstGenerator_mem f h 1 h₁) hBE
  have hC : C ∈ orderSpace 2 :=
    lie_mem_orderSpace_sharp (firstGenerator_mem_orderSpace_one f h 1) hB
  have hCC : δ 1 (δ 1 C) = multiplication
      ((-a * p.b₂) • linearFunction (coordinateVector 1) + (-a * p.b₀) • smoothOne) := by
    rw [head11_firstGenerator1 f h B c a b hh, normalized_wong01 f p hp hb₁]
    congr 1
    module
  have hz := pure_head_linear_slope_zero f h 1 C hCE hC (-a * p.b₂) (-a * p.b₀) hCC
  have ha : a = 0 := neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hb₂)
  refine ⟨ha, pure_head_linear_slope_zero f h 1 B hBE hB b c ?_⟩
  simpa [visibleAffine, ha, add_comm] using hh

/-- The mixed head has no slope in the `0` coordinate either. -/
theorem head01_no_first_slope {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ ≠ 0)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (B : Operator) (hBE : B ∈ estimationAlgebra f h) (hB : B ∈ orderSpace 2)
    (c₀ a₀ b₀ c a b : ℝ)
    (hh₀ : δ 0 (δ 0 B) = multiplication (visibleAffine c₀ a₀ b₀))
    (hh : δ 0 (δ 1 B) = multiplication (visibleAffine c a b)) : a = 0 := by
  have ha₀ := head00_no_own_slope f h p hp hb₁ hb₂ h₀ B hBE hB c₀ a₀ b₀ hh₀
  let C := ⁅firstGenerator f h 1, B⁆
  have hCE : C ∈ estimationAlgebra f h :=
    (estimationAlgebra f h).lie_mem (firstGenerator_mem f h 1 h₁) hBE
  have hC : C ∈ orderSpace 2 :=
    lie_mem_orderSpace_sharp (firstGenerator_mem_orderSpace_one f h 1) hB
  have hCC : δ 0 (δ 0 C) = multiplication
      (visibleAffine (2 * p.b₂ * c) (2 * p.b₂ * a) (2 * p.b₂ * b)) := by
    rw [head00_firstGenerator1 f h p hp hb₁ B c₀ a₀ b₀ hh₀, ha₀]
    simp only [neg_zero, zero_smul, multiplication_zero, zero_add, hh, ← multiplication_smul]
    congr 1
    simp only [visibleAffine, smul_add, smul_smul]
  have hz := head00_no_own_slope f h p hp hb₁ hb₂ h₀ C hCE hC
    (2 * p.b₂ * c) (2 * p.b₂ * a) (2 * p.b₂ * b) hCC
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hb₂)

/-- All restrictions before the mixed-slope symbol ladder, proved on the
original operator Lie algebra rather than imposed as a symbol hypothesis. -/
theorem normalized_visible_heads {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ ≠ 0)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (B : Operator) (hBE : B ∈ estimationAlgebra f h) (hB : B ∈ orderSpace 2) :
    ∃ c₀ a₀ c₁ c a : ℝ,
      δ 0 (δ 0 B) = multiplication (visibleAffine c₀ 0 a₀) ∧
      δ 1 (δ 1 B) = multiplication (c₁ • smoothOne) ∧
      δ 0 (δ 1 B) = multiplication (visibleAffine c 0 a) := by
  obtain ⟨c₀, a₀, b₀, hh₀⟩ := double_head_affine f h hrank hq h₀ h₁ B hBE hB
    0 0 (Or.inl rfl) (Or.inl rfl)
  obtain ⟨c₁, a₁, b₁, hh₁⟩ := double_head_affine f h hrank hq h₀ h₁ B hBE hB
    1 1 (Or.inr rfl) (Or.inr rfl)
  obtain ⟨c, a, b, hh⟩ := double_head_affine f h hrank hq h₀ h₁ B hBE hB
    0 1 (Or.inl rfl) (Or.inr rfl)
  have ha₀ := head00_no_own_slope f h p hp hb₁ hb₂ h₀ B hBE hB c₀ a₀ b₀ hh₀
  obtain ⟨ha₁, hb₁'⟩ := head11_slopes_zero f h p hp hb₁ hb₂ h₁ B hBE hB c₁ a₁ b₁ hh₁
  have ha := head01_no_first_slope f h p hp hb₁ hb₂ h₀ h₁ B hBE hB c₀ a₀ b₀ c a b hh₀ hh
  refine ⟨c₀, b₀, c₁, c, b, ?_, ?_, ?_⟩
  · simpa only [ha₀] using hh₀
  · simpa [visibleAffine, ha₁, hb₁'] using hh₁
  · simpa only [ha] using hh

end Wong.SmoothModel.VisibleHeads
