import Wong.VisibleHeadCalculus

/-!
# The three actual visible second-order heads of the generator word

`H=[L₀,D₀]`, `X=[L₀,H]`, `Y=[L₀,X]` are actual operators. Their
double coordinate commutators are computed by Jacobi and Leibniz on the
smooth model. No principal-symbol identification is assumed.
-/

noncomputable section
namespace Wong.SmoothModel.VisibleHeads

def constantSecondPart (f : Fin 3 → Smooth) (s : Fin 3 → State) : Operator :=
  ∑ j, ∑ k, s j k • (D f k * D f j)

def lowerPart {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (a : Fin 3 → Smooth) (b : Smooth) : Operator :=
  (∑ j, multiplication (a j) * ⁅L0 f h, D f j⁆) + ⁅L0 f h, multiplication b⁆

theorem lie_L0_D_mem_orderSpace_one {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3) : ⁅L0 f h, D f i⁆ ∈ orderSpace 1 := by
  rw [lie_L0_D_eq_firstOrder]
  exact firstOrder_mem_orderSpace_one f _ _

theorem lowerPart_mem_orderSpace_one {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (a : Fin 3 → Smooth) (b : Smooth) : lowerPart f h a b ∈ orderSpace 1 := by
  apply (orderSpace 1).add_mem
  · apply (orderSpace 1).sum_mem
    intro j _
    exact mul_mem_orderSpace (multiplication_mem_orderSpace_zero (a j))
      (lie_L0_D_mem_orderSpace_one f h j)
  · exact lie_L0_mem_orderSpace f h (multiplication_mem_orderSpace_zero b)

theorem lie_L0_firstOrder_decomposition {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (a : Fin 3 → Smooth) (b : Smooth) (s : Fin 3 → State)
    (ha : ∀ j k, partialDerivative k (a j) = s j k • smoothOne) :
    ⁅L0 f h, firstOrder f a b⁆ = constantSecondPart f s + lowerPart f h a b := by
  have hLA (j : Fin 3) : ⁅L0 f h, multiplication (a j)⁆ = ∑ k, s j k • D f k :=
    lie_L0_multiplication_affine f h (a j) (s j) (ha j)
  simp only [firstOrder, lie_add, lie_sum, operator_lie_mul_right, hLA,
    Finset.sum_mul, smul_mul_assoc, Finset.sum_add_distrib, constantSecondPart, lowerPart]
  abel

theorem lie_L0_constantSecondPart_mem_orderSpace_two {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (s : Fin 3 → State) :
    ⁅L0 f h, constantSecondPart f s⁆ ∈ orderSpace 2 := by
  simp only [constantSecondPart, lie_sum, lie_smul, operator_lie_mul_right]
  apply (orderSpace 2).sum_mem
  intro j _
  apply (orderSpace 2).sum_mem
  intro k _
  apply (orderSpace 2).smul_mem
  apply (orderSpace 2).add_mem
  · exact mul_mem_orderSpace (lie_L0_D_mem_orderSpace_one f h k) (D_mem_orderSpace_one f j)
  · exact mul_mem_orderSpace (D_mem_orderSpace_one f k) (lie_L0_D_mem_orderSpace_one f h j)

/-- The second-order part of `X` has genuinely constant coefficients. -/
theorem X_decomposition {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    X f h = constantSecondPart f (fun j => slopes p 0 j) +
      lowerPart f h (wong f 0) (generatorRemainder f h 0) := by
  rw [X, H_eq_firstOrder]
  exact lie_L0_firstOrder_decomposition f h _ _ _ (fun j k => partial_wong_affine f p hp k 0 j)

/-- A further commutator has order at most two because the second-order
    coefficients just proved above are constant. -/
theorem Y_mem_orderSpace_two {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    Y f h ∈ orderSpace 2 := by
  rw [Y, X_decomposition f h p hp, lie_add]
  apply (orderSpace 2).add_mem
  · exact lie_L0_constantSecondPart_mem_orderSpace_two f h _
  · exact lie_L0_mem_orderSpace f h (lowerPart_mem_orderSpace_one f h _ _)

theorem Y_mem_of_coordinate_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h) :
    Y f h ∈ estimationAlgebra f h := by
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  exact (estimationAlgebra f h).lie_mem hL ((estimationAlgebra f h).lie_mem hL
    ((estimationAlgebra f h).lie_mem hL (D_mem_of_coordinate_mem f h 0 h₀)))

theorem head00 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    δ 0 (δ 0 (Y f h)) = multiplication
      ((-6 * p.k₁) • wong f 0 2 + (-6 * p.b₁) • wong f 0 1 +
        partialDerivative 0 (partialDerivative 0 (partialDerivative 0 (eta f h)))) := by
  rw [δ_δ_Y f h p hp]
  apply congrArg multiplication
  simp only [doubleHead, remainderX, map_add, map_sum, partialDerivative_smoothMul,
    partial_partial_generatorRemainder f h p hp, partial_wong_affine f p hp]
  apply Subtype.ext
  funext x
  simp [Fin.sum_univ_three, slopes, smoothMul, smoothOne,
    wong_skew f 0 1, wong_skew f 0 2]
  ring

theorem head11 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    δ 1 (δ 1 (Y f h)) = multiplication
      ((2 * p.b₁) • wong f 0 1 + (-2 * p.h₂) • wong f 0 2 +
        (-4 * p.k₂) • wong f 1 2 +
        partialDerivative 0 (partialDerivative 1 (partialDerivative 1 (eta f h)))) := by
  rw [δ_δ_Y f h p hp]
  apply congrArg multiplication
  simp only [doubleHead, remainderX, map_add, map_sum, partialDerivative_smoothMul,
    partial_partial_generatorRemainder f h p hp, partial_wong_affine f p hp]
  apply Subtype.ext
  funext x
  simp [Fin.sum_univ_three, slopes, smoothMul, smoothOne,
    wong_skew f 1 2]
  ring

theorem head01 {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    δ 0 (δ 1 (Y f h)) = multiplication
      ((-4 * p.b₂) • wong f 0 1 + (-4 * p.k₂) • wong f 0 2 +
        (-2 * p.k₁) • wong f 1 2 +
        partialDerivative 0 (partialDerivative 0 (partialDerivative 1 (eta f h)))) := by
  rw [δ_δ_Y f h p hp]
  apply congrArg multiplication
  simp only [doubleHead, remainderX, map_add, map_sum, partialDerivative_smoothMul,
    partial_partial_generatorRemainder f h p hp, partial_wong_affine f p hp]
  apply Subtype.ext
  funext x
  simp [Fin.sum_univ_three, slopes, smoothMul, smoothOne,
    wong_skew f 0 1, wong_skew f 0 2, wong_skew f 1 2, bianchi_slopes f p hp]
  rw [partialDerivative_commute_apply 1 0 (eta f h)]
  ring

end Wong.SmoothModel.VisibleHeads
