import Wong.VisibleGeneratorHeads

/-!
# Visible curvature constancy by Jacobi identities

The contradiction below uses actual Lie words and their double coordinate
commutators. It does not use the explicit third-derivative head formulas or
commutation of fourth derivatives of the filtering potential.
-/

noncomputable section

namespace Wong.JacobiVisible

section LieAlgebra
variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]

/-- The first compatibility identity is a direct instance of Jacobi. -/
theorem first_identity (L P Q W : A) (b : ℝ)
    (hQP : ⁅Q, P⁆ = W) (hLW : ⁅L, W⁆ = b • Q)
    (hWH : ⁅W, ⁅L, P⁆⁆ = (-b) • W) :
    ⁅Q, ⁅P, ⁅L, P⁆⁆⁆ - ⁅P, ⁅P, ⁅L, Q⁆⁆⁆ = (-2 * b) • W := by
  have hcompat : ⁅Q, ⁅L, P⁆⁆ - ⁅P, ⁅L, Q⁆⁆ = b • Q := by
    have hj := leibniz_lie L Q P
    rw [hQP, hLW, ← lie_skew ⁅L, Q⁆ P] at hj
    rw [neg_add_eq_sub] at hj
    exact hj.symm
  calc
    ⁅Q, ⁅P, ⁅L, P⁆⁆⁆ - ⁅P, ⁅P, ⁅L, Q⁆⁆⁆ =
        ⁅P, ⁅Q, ⁅L, P⁆⁆ - ⁅P, ⁅L, Q⁆⁆⁆ + ⁅W, ⁅L, P⁆⁆ := by
      rw [lie_sub, leibniz_lie Q P, hQP]
      abel
    _ = b • ⁅P, Q⁆ + (-b) • W := by rw [hcompat, lie_smul, hWH]
    _ = (-2 * b) • W := by
      rw [← lie_skew P Q, hQP, smul_neg, ← neg_smul, ← add_smul]
      congr 1
      ring

/-- Differentiating the Jacobi compatibility identity gives the scalar
obstruction, with no coefficient expansion of the generator. -/
theorem second_identity (L P Q W e : A) (b : ℝ)
    (hQP : ⁅Q, P⁆ = W) (hLW : ⁅L, W⁆ = b • Q)
    (hWH : ⁅W, ⁅L, P⁆⁆ = (-b) • W)
    (hQW : ⁅Q, W⁆ = b • e) (hWJ : ⁅W, ⁅P, ⁅L, Q⁆⁆⁆ = 0) :
    ⁅Q, ⁅Q, ⁅P, ⁅L, P⁆⁆⁆⁆ - ⁅P, ⁅Q, ⁅P, ⁅L, Q⁆⁆⁆⁆ =
      (-2 * b ^ 2) • e := by
  have hi := congrArg (fun Z : A => ⁅Q, Z⁆) (first_identity L P Q W b hQP hLW hWH)
  rw [lie_sub, lie_smul, hQW, smul_smul] at hi
  rw [leibniz_lie Q P ⁅P, ⁅L, Q⁆⁆, hQP, hWJ, zero_add] at hi
  have hcoef : (-2 * b) * b = -2 * b ^ 2 := by ring
  simpa only [hcoef] using hi

end LieAlgebra
end Wong.JacobiVisible

namespace Wong.SmoothModel.VisibleHeads

/-- In normalized visible coordinates the curvature multiplier is affine
in the second coordinate alone. -/
theorem jacobi_visible_multiplier (f : Fin 3 → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) :
    multiplication (wong f 0 1) = p.b₀ • (1 : Operator) +
      p.b₂ • multiplication (linearFunction (coordinateVector 1)) := by
  have hs : wong f 0 1 = p.b₀ • smoothOne +
      p.b₂ • linearFunction (coordinateVector 1) := by
    apply Subtype.ext
    funext x
    simp [hp, Wong.AffineParameters.matrix, Wong.AffineParameters.w12,
      hb₁, smoothOne, linearFunction, coordinateVector, Fin.sum_univ_three]
    ring
  rw [hs, multiplication_add, multiplication_smul, multiplication_smul,
    multiplication_smoothOne]

set_option maxHeartbeats 1000000 in
/-- The Jacobi proof on the genuine smooth-operator model. -/
theorem normalized_slope_zero_by_jacobi {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters) (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (c₁ c : ℝ)
    (h11 : δ 1 (δ 1 (Y f h)) = multiplication (c₁ • smoothOne))
    (h01 : δ 0 (δ 1 (Y f h)) = multiplication (c • smoothOne)) : p.b₂ = 0 := by
  let L := L0 f h
  let P := D f 0
  let Q := D f 1
  let W := multiplication (wong f 0 1)
  let G := ⁅L, Q⁆
  let J11 := ⁅P, H f h⁆
  let J12 := ⁅P, G⁆
  have hW : W = p.b₀ • (1 : Operator) +
      p.b₂ • multiplication (linearFunction (coordinateVector 1)) :=
    jacobi_visible_multiplier f p hp hb₁
  have hQP : ⁅Q, P⁆ = W := lie_D_D f 0 1
  have hPW : ⁅P, W⁆ = 0 := by
    dsimp [P, W]
    rw [lie_D_multiplication, partial_wong_affine f p hp]
    simp [slopes, hb₁]
  have hQW : ⁅Q, W⁆ = p.b₂ • (1 : Operator) := by
    dsimp [Q, W]
    rw [lie_D_multiplication, partial_wong_affine f p hp]
    simp [slopes, multiplication_smul, multiplication_smoothOne]
  have hLW : ⁅L, W⁆ = p.b₂ • Q := by
    rw [hW, lie_add, lie_scalar_identity, zero_add, lie_smul]
    exact congrArg (fun Z : Operator => p.b₂ • Z) (δ_L0 f h 1)
  have hH0 : δ 0 (H f h) = 0 := by
    rw [δ_H]
    simp [wong]
  have hH1 : δ 1 (H f h) = W := δ_H f h 1
  have hG0 : δ 0 G = -W := by
    dsimp [G, L, Q]
    rw [δ_lie_L0, δ_D, lie_scalar_identity, zero_add]
    rw [← lie_skew (D f 0) (D f 1), hQP]
  have hG1 : δ 1 G = 0 := by
    dsimp [G, L, Q]
    rw [δ_lie_L0, δ_D, lie_scalar_identity, zero_add, lie_self]
  have hJ110 : δ 0 J11 = 0 := by
    dsimp [J11, P]
    rw [δ_lie_D, hH0, lie_zero]
  have hJ111 : δ 1 J11 = 0 := by
    dsimp [J11, P]
    rw [δ_lie_D, hH1]
    exact hPW
  have hJ120 : δ 0 J12 = 0 := by
    dsimp only [J12, P]
    rw [δ_lie_D, hG0, lie_neg, hPW, neg_zero]
  have hJ121 : δ 1 J12 = 0 := by
    dsimp only [J12, P]
    rw [δ_lie_D, hG1, lie_zero]
  have hWH : ⁅W, ⁅L, P⁆⁆ = (-p.b₂) • W := by
    have hHW : ⁅H f h, W⁆ = p.b₂ • W := by
      conv_lhs => rw [hW]
      rw [lie_add, lie_scalar_identity, zero_add, lie_smul]
      exact congrArg (fun Z : Operator => p.b₂ • Z) hH1
    rw [← lie_skew W ⁅L, P⁆, show ⁅L, P⁆ = H f h from rfl, hHW, neg_smul]
  have hWJ : ⁅W, J12⁆ = 0 := by
    rw [hW, add_lie, scalar_identity_lie, zero_add, smul_lie,
      ← lie_skew (multiplication (linearFunction (coordinateVector 1))) J12]
    change p.b₂ • -δ 1 J12 = 0
    rw [hJ121, neg_zero, smul_zero]
  have hcompat : ⁅Q, H f h⁆ - J12 = p.b₂ • Q := by
    have hj := leibniz_lie L Q P
    rw [hQP, hLW, ← lie_skew ⁅L, Q⁆ P] at hj
    change p.b₂ • Q = -J12 + ⁅Q, H f h⁆ at hj
    rw [neg_add_eq_sub] at hj
    exact hj.symm
  have hfirst : ⁅Q, J11⁆ - ⁅P, J12⁆ = (-2 * p.b₂) • W :=
    Wong.JacobiVisible.first_identity L P Q W p.b₂ hQP hLW hWH
  have hX0 : δ 0 (X f h) = J11 := by
    rw [X, δ_lie_L0, hH0, lie_zero, zero_add]
  have hX1 : δ 1 (X f h) = J12 + (2 * p.b₂) • Q := by
    rw [X, δ_lie_L0, hH1, hLW]
    have hc : ⁅Q, H f h⁆ = J12 + p.b₂ • Q := by
      rw [sub_eq_iff_eq_add] at hcompat
      exact hcompat.trans (add_comm _ _)
    change p.b₂ • Q + ⁅Q, H f h⁆ = _
    rw [hc, show 2 * p.b₂ = p.b₂ + p.b₂ by ring, add_smul]
    abel
  have hdQ0 : δ 0 Q = 0 := by simp [Q, coordinateVector]
  have hdQ1 : δ 1 Q = (1 : Operator) := by simp [Q, coordinateVector]
  have hQQ : ⁅D f 1, Q⁆ = 0 := lie_self Q
  have hhead11 : δ 1 (δ 1 (Y f h)) = (2 : ℝ) • ⁅Q, J12⁆ := by
    rw [Y, δ_lie_L0, map_add, δ_lie_L0, δ_lie_D, hX1]
    simp only [map_add, map_smul, hJ121, hdQ1, zero_add, lie_add,
      lie_smul, hQQ, smul_zero, add_zero]
    change (2 * p.b₂) • ⁅L, (1 : Operator)⁆ + ⁅Q, J12⁆ + ⁅Q, J12⁆ = _
    have hone : ⁅L, (1 : Operator)⁆ = 0 := by
      simpa only [one_smul] using lie_scalar_identity L 1
    rw [hone, smul_zero, zero_add, two_smul]
  have hhead01 : δ 0 (δ 1 (Y f h)) = (2 : ℝ) • ⁅Q, J11⁆ := by
    rw [Y, δ_lie_L0, map_add, δ_lie_L0, δ_lie_D, hX1, hX0]
    simp only [map_add, map_smul, hJ120, hdQ0, smul_zero,
      zero_add, lie_zero, lie_add, lie_smul]
    change ⁅P, J12⁆ + (2 * p.b₂) • ⁅P, Q⁆ + ⁅Q, J11⁆ = _
    rw [← lie_skew P Q, hQP, smul_neg]
    have hf : ⁅P, J12⁆ = ⁅Q, J11⁆ + (2 * p.b₂) • W := by
      rw [neg_mul, neg_smul] at hfirst
      have he := sub_eq_iff_eq_add.mp hfirst
      calc
        ⁅P, J12⁆ = (⁅P, J12⁆ - (2 * p.b₂) • W) + (2 * p.b₂) • W := by abel
        _ = ⁅Q, J11⁆ + (2 * p.b₂) • W := by rw [he]; abel
    rw [hf, two_smul]
    abel
  have hzero1 : ⁅Q, ⁅Q, J11⁆⁆ = 0 := by
    have hc := congrArg (fun Z : Operator => ⁅Q, Z⁆) (hhead01.symm.trans h01)
    rw [lie_smul, multiplication_smul, multiplication_smoothOne, lie_scalar_identity] at hc
    exact (smul_eq_zero.mp hc).resolve_left (by norm_num)
  have hzero2 : ⁅P, ⁅Q, J12⁆⁆ = 0 := by
    have hc := congrArg (fun Z : Operator => ⁅P, Z⁆) (hhead11.symm.trans h11)
    rw [lie_smul, multiplication_smul, multiplication_smoothOne, lie_scalar_identity] at hc
    exact (smul_eq_zero.mp hc).resolve_left (by norm_num)
  have hlast := Wong.JacobiVisible.second_identity L P Q W (1 : Operator)
    p.b₂ hQP hLW hWH hQW hWJ
  change ⁅Q, ⁅Q, J11⁆⁆ - ⁅P, ⁅Q, J12⁆⁆ = _ at hlast
  rw [hzero1, hzero2, sub_self] at hlast
  have hv := congrArg (fun A : Operator => (A smoothOne).1 (0 : State)) hlast
  have hs : -2 * p.b₂ ^ 2 = 0 := by simpa [smoothOne] using hv.symm
  nlinarith [sq_nonneg p.b₂]

end Wong.SmoothModel.VisibleHeads
