import Wong.QuadraticFunctionWongConstraints
import Wong.PublishedAffineStatement
import Wong.RootAnalyticBridges

/-! Genuine visible and radial quadratic Wong constraints, compiled together to share import memory. All interfaces retain actual operator membership and scalar remainders. -/


/-! Source segment: VisibleQuadraticWongRigidity -/

/-! Actual visible quadratic multipliers constrain the affine visible Wong
entry. All products of covariant derivatives used below are proved genuine
Lie words; no coordinate-times-derivative membership is assumed. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

theorem polynomialSmooth_coordinate (i : Fin 3) :
    polynomialSmooth (X i) = linearFunction (coordinateVector i) := by
  apply Subtype.ext
  funext x
  simp [polynomialSmooth, linearFunction, coordinateVector, Pi.single_apply, ite_mul]

theorem partialDerivative_polynomial_coordinate_square (i j : Fin 3) :
    partialDerivative j (polynomialSmooth (X i ^ 2)) =
      if j = i then (2 : ℝ) • polynomialSmooth (X i) else 0 := by
  rw [partialDerivative_polynomialSmooth]
  apply Subtype.ext
  funext x
  by_cases hji : j = i
  · subst j
    simp [polynomialSmooth, pow_two]
    ring
  · simp [polynomialSmooth, pow_two, hji]

theorem lie_L0_polynomial_coordinate_square {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (i : Fin 3) :
    ⁅L0 f h, multiplication (polynomialSmooth (X i ^ 2))⁆ =
      (2 : ℝ) • (multiplication (polynomialSmooth (X i)) * D f i) + 1 := by
  rw [lie_L0_multiplication]
  have hsecond : ∑ j : Fin 3,
      partialDerivative j (partialDerivative j (polynomialSmooth (X i ^ 2))) =
      (2 : ℝ) • smoothOne := by
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    fin_cases i <;> norm_num [Fin.sum_univ_three, polynomialSmooth, pow_two, Pi.single_apply]
  rw [hsecond]
  simp only [partialDerivative_polynomial_coordinate_square]
  fin_cases i <;> simp [Fin.sum_univ_three, multiplication_smul, smul_mul_assoc]

theorem coordinate_times_covariant_mem_of_square_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (i : Fin 3)
    (hsquare : multiplication (polynomialSmooth (X i ^ 2)) ∈ estimationAlgebra f h) :
    multiplication (polynomialSmooth (X i)) * D f i ∈ estimationAlgebra f h := by
  have hL : L0 f h ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hone := smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have hword := (estimationAlgebra f h).lie_mem hL hsquare
  rw [lie_L0_polynomial_coordinate_square] at hword
  have hsub := (estimationAlgebra f h).sub_mem hword hone
  have hscaled := (estimationAlgebra f h).smul_mem (1 / 2 : ℝ) hsub
  simpa using hscaled

theorem visible_square_pair_wong_product_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hzero : multiplication (polynomialSmooth (X 0 ^ 2)) ∈ estimationAlgebra f h)
    (hone : multiplication (polynomialSmooth (X 1 ^ 2)) ∈ estimationAlgebra f h) :
    multiplication (smoothMul (smoothMul (polynomialSmooth (X 0))
      (polynomialSmooth (X 1))) (wong f 0 1)) ∈ estimationAlgebra f h := by
  have h0 := coordinate_times_covariant_mem_of_square_member f h hrank 0 hzero
  have h1 := coordinate_times_covariant_mem_of_square_member f h hrank 1 hone
  have hm := (estimationAlgebra f h).lie_mem h1 h0
  rw [lie_covariant_monomials] at hm
  have h10 : partialDerivative 1 (polynomialSmooth (X 0)) = 0 := by
    simp [partialDerivative_polynomialSmooth, Pi.single_apply]
  have h01 : partialDerivative 0 (polynomialSmooth (X 1)) = 0 := by
    simp [partialDerivative_polynomialSmooth, Pi.single_apply]
  have hmul : smoothMul (polynomialSmooth (X 1)) (polynomialSmooth (X 0)) =
      smoothMul (polynomialSmooth (X 0)) (polynomialSmooth (X 1)) :=
    smoothMul_comm _ _
  simpa only [h10, h01, smoothMul_eq_mul, mul_zero, multiplication_zero, zero_mul,
    sub_zero, zero_sub, add_zero, zero_add, mul_comm] using hm

theorem visible_affine_wong_slopes_zero_of_square_pair {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hzero : multiplication (polynomialSmooth (X 0 ^ 2)) ∈ estimationAlgebra f h)
    (hone : multiplication (polynomialSmooth (X 1 ^ 2)) ∈ estimationAlgebra f h)
    (c k l : ℝ)
    (hw : wong f 0 1 = polynomialSmooth (C c + C k * X 0 + C l * X 1)) :
    k = 0 ∧ l = 0 := by
  let q : RealPoly := X 0 * X 1 * (C c + C k * X 0 + C l * X 1)
  have hqE : multiplication (polynomialSmooth q) ∈ estimationAlgebra f h := by
    simpa only [q, polynomialSmooth_mul, hw] using
      visible_square_pair_wong_product_mem f h hrank hzero hone
  have hq := polynomial_function_element_degree_le_two f h q hqE
  have hdegree (i : Fin 3) : (pderiv i q).totalDegree < 2 := by
    have hd := Wong.PolynomialGradient.partial_totalDegree_le q i
    omega
  have hk := polynomial_partial_pow_zero_of_totalDegree (pderiv 1 q) 0 2 (hdegree 1)
  have hl := polynomial_partial_pow_zero_of_totalDegree (pderiv 0 q) 1 2 (hdegree 0)
  have hk' : C (2 * k) = (0 : RealPoly) := by
    simpa [q, pow_two, Module.End.mul_apply, Pi.single_apply] using hk
  have hl' : C (2 * l) = (0 : RealPoly) := by
    simpa [q, pow_two, Module.End.mul_apply, Pi.single_apply] using hl
  have hkreal := congrArg (eval (0 : State)) hk'
  have hlreal := congrArg (eval (0 : State)) hl'
  simp only [eval_C, map_zero] at hkreal hlreal
  constructor <;> linarith

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visible_affine_wong_slopes_zero_of_square_pair


/-! Source segment: VisibleRadialWongRigidity -/

/-! A genuine visible radial quadratic multiplier forces the visible
affine Wong entry to be constant. Lower affine function terms are removed
using the admitted visible coordinate multipliers only. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

def actualPolynomialFunctionSpace (E : LieSubalgebra ℝ Operator) :
    Submodule ℝ RealPoly :=
  E.toSubmodule.comap (multiplicationLinear.comp polynomialSmoothLinear)

theorem actualPolynomialFunctionSpace_mem_iff
    (E : LieSubalgebra ℝ Operator) (p : RealPoly) :
    p ∈ actualPolynomialFunctionSpace E ↔ multiplication (polynomialSmooth p) ∈ E :=
  Iff.rfl

theorem visible_radial_quadratic_curvature_products_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth (X 0 ^ 2 + X 1 ^ 2)) ∈
      estimationAlgebra f h) :
    multiplication (smoothMul (polynomialSmooth (X 0)) (wong f 0 1)) ∈
      estimationAlgebra f h ∧
    multiplication (smoothMul (polynomialSmooth (X 1)) (wong f 0 1)) ∈
      estimationAlgebra f h := by
  let u := polynomialSmooth (X 0 ^ 2 + X 1 ^ 2)
  have hH (i : Fin 3) (hi : i = 0 ∨ i = 1) (j : Fin 3) :
      partialDerivative i (partialDerivative j u) =
        (if j = i then (2 : ℝ) else 0) • smoothOne := by
    dsimp only [u]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    rcases hi with rfl | rfl <;> fin_cases j
      <;> norm_num [polynomialSmooth, pow_two, Pi.single_apply, smoothOne]
  have hcurv0 := function_curvature_gradient_mem_of_visible_hessian_row
    f h hx0 hx1 u hq 0 (Or.inl rfl)
    (fun j => if j = 0 then (2 : ℝ) else 0) (hH 0 (Or.inl rfl)) (by norm_num)
  have hcurv1 := function_curvature_gradient_mem_of_visible_hessian_row
    f h hx0 hx1 u hq 1 (Or.inr rfl)
    (fun j => if j = 1 then (2 : ℝ) else 0) (hH 1 (Or.inr rfl)) (by norm_num)
  have heq0 : functionCurvatureGradient f u 0 =
      (-2 : ℝ) • smoothMul (polynomialSmooth (X 1)) (wong f 0 1) := by
    dsimp only [functionCurvatureGradient, u]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    have hw := congrArg (fun v : Smooth => v.1 x) (wong_skew f 0 1)
    simp [polynomialSmooth, functionCurvatureGradient, u, partialDerivative_polynomialSmooth,
      Fin.sum_univ_three, pow_two, Pi.single_apply, smoothMul_apply] at *
    rw [hw]
    ring
  have heq1 : functionCurvatureGradient f u 1 =
      (2 : ℝ) • smoothMul (polynomialSmooth (X 0)) (wong f 0 1) := by
    dsimp only [functionCurvatureGradient, u]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    simp [polynomialSmooth, functionCurvatureGradient, u, partialDerivative_polynomialSmooth,
      Fin.sum_univ_three, pow_two, Pi.single_apply, smoothMul_apply]
    ring
  constructor
  · rw [heq1, multiplication_smul] at hcurv1
    simpa using (estimationAlgebra f h).smul_mem (1 / 2 : ℝ) hcurv1
  · rw [heq0, multiplication_smul] at hcurv0
    have hs : (-1 / 2 : ℝ) * (-2) = 1 := by norm_num
    simpa only [smul_smul, hs, one_smul] using
      (estimationAlgebra f h).smul_mem (-1 / 2 : ℝ) hcurv0

theorem visible_affine_wong_slopes_zero_of_radial_quadratic {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth (X 0 ^ 2 + X 1 ^ 2)) ∈ estimationAlgebra f h)
    (c k l : ℝ)
    (hw : wong f 0 1 = polynomialSmooth (C c + C k * X 0 + C l * X 1)) :
    k = 0 ∧ l = 0 := by
  by_cases hz : k = 0 ∧ l = 0
  · exact hz
  let E := estimationAlgebra f h
  let S := actualPolynomialFunctionSpace E
  have hcoord0 : X 0 ∈ S := by
    change multiplication (polynomialSmooth (X 0)) ∈ E
    rwa [polynomialSmooth_coordinate]
  have hcoord1 : X 1 ∈ S := by
    change multiplication (polynomialSmooth (X 1)) ∈ E
    rwa [polynomialSmooth_coordinate]
  have hqS : X 0 ^ 2 + X 1 ^ 2 ∈ S := hq
  obtain ⟨h0, h1⟩ := visible_radial_quadratic_curvature_products_mem f h hx0 hx1 hq
  have hf0 : X 0 * (C c + C k * X 0 + C l * X 1) ∈ S := by
    change multiplication (polynomialSmooth _) ∈ E
    simpa only [polynomialSmooth_mul, hw] using h0
  have hf1 : X 1 * (C c + C k * X 0 + C l * X 1) ∈ S := by
    change multiplication (polynomialSmooth _) ∈ E
    simpa only [polynomialSmooth_mul, hw] using h1
  let F0 : RealPoly := C k * X 0 ^ 2 + C l * X 0 * X 1
  let F1 : RealPoly := C k * X 0 * X 1 + C l * X 1 ^ 2
  have hF0 : F0 ∈ S := by
    convert S.sub_mem hf0 (S.smul_mem c hcoord0) using 1
    simp only [F0, smul_eq_C_mul]
    ring
  have hF1 : F1 ∈ S := by
    convert S.sub_mem hf1 (S.smul_mem c hcoord1) using 1
    simp only [F1, smul_eq_C_mul]
    ring
  have hnorm : k ^ 2 + l ^ 2 ≠ 0 := by
    intro hn
    apply hz
    constructor <;> nlinarith [sq_nonneg k, sq_nonneg l]
  have hscaled : (k ^ 2 + l ^ 2) • ((X 0 : RealPoly) ^ 2) ∈ S := by
    convert S.add_mem (S.sub_mem (S.smul_mem k hF0) (S.smul_mem l hF1))
      (S.smul_mem (l ^ 2) hqS) using 1
    simp only [F0, F1, smul_eq_C_mul, map_add, map_pow]
    ring
  have hsquare0 : (X 0 : RealPoly)^2 ∈ S := by
    have hh := S.smul_mem (k ^ 2 + l ^ 2)⁻¹ hscaled
    simpa only [smul_smul, inv_mul_cancel₀ hnorm, one_smul] using hh
  have hsquare1 : (X 1 : RealPoly)^2 ∈ S := by
    convert S.sub_mem hqS hsquare0 using 1
    ring
  exact visible_affine_wong_slopes_zero_of_square_pair f h hrank hsquare0 hsquare1 c k l hw

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visible_affine_wong_slopes_zero_of_radial_quadratic


/-! Source segment: PolynomialFunctionGamma -/

/-! Genuine polynomial function elements are closed under the bilinear
carre-du-champ. A Jordan associator repairs the visible part of the radial
quadratic branch without assuming omitted highest-order terms vanish. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open MvPolynomial

def polynomialGradientPair (p q : RealPoly) : RealPoly :=
  ∑ i : Fin 3, pderiv i p * pderiv i q

theorem polynomialGradientPair_mem_actual_function_space {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (p q : RealPoly)
    (hp : p ∈ actualPolynomialFunctionSpace (estimationAlgebra f h))
    (hq : q ∈ actualPolynomialFunctionSpace (estimationAlgebra f h)) :
    polynomialGradientPair p q ∈ actualPolynomialFunctionSpace (estimationAlgebra f h) := by
  change multiplication (polynomialSmooth (polynomialGradientPair p q)) ∈ estimationAlgebra f h
  have hL : L0 f h ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hm := (estimationAlgebra f h).lie_mem
    ((estimationAlgebra f h).lie_mem hL hp) hq
  change ⁅⁅L0 f h, multiplication (polynomialSmooth p)⁆,
    multiplication (polynomialSmooth q)⁆ ∈ estimationAlgebra f h at hm
  rw [double_lie_L0_multiplication] at hm
  simpa only [polynomialGradientPair, polynomialSmooth_sum, polynomialSmooth_mul,
    partialDerivative_polynomialSmooth] using hm

def radialCurvatureQuadraticZero (k l a : ℝ) : RealPoly :=
  -(C k * X 0 * X 1) - C l * X 1 ^ 2 - C a * X 2 ^ 2

def radialCurvatureQuadraticOne (k l b : ℝ) : RealPoly :=
  C k * X 0 ^ 2 + C l * X 0 * X 1 - C b * X 2 ^ 2

def radialCurvatureAssociator (k l a b : ℝ) : RealPoly :=
  let F := radialCurvatureQuadraticZero k l a
  let G := radialCurvatureQuadraticOne k l b
  polynomialGradientPair (polynomialGradientPair F F) G -
    polynomialGradientPair F (polynomialGradientPair F G)

theorem radialCurvatureAssociator_gradient_square (k l a b : ℝ) :
    polynomialGradientPair (radialCurvatureAssociator k l a b)
      (radialCurvatureAssociator k l a b) =
      (16 * (k ^ 2 + l ^ 2) ^ 3 : ℝ) • (X 0 ^ 2 + X 1 ^ 2 : RealPoly) := by
  apply MvPolynomial.funext
  intro x
  simp [radialCurvatureAssociator, radialCurvatureQuadraticZero,
    radialCurvatureQuadraticOne, polynomialGradientPair, Fin.sum_univ_three,
    pow_two, Pi.single_apply, smul_eq_C_mul, map_add, map_mul, map_pow]
  ring

theorem visible_radial_quadratic_member_of_radial_curvature_quadratics {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (k l a b : ℝ)
    (hn : k ^ 2 + l ^ 2 ≠ 0)
    (hF : radialCurvatureQuadraticZero k l a ∈
      actualPolynomialFunctionSpace (estimationAlgebra f h))
    (hG : radialCurvatureQuadraticOne k l b ∈
      actualPolynomialFunctionSpace (estimationAlgebra f h)) :
    multiplication (polynomialSmooth (X 0 ^ 2 + X 1 ^ 2)) ∈ estimationAlgebra f h := by
  let S := actualPolynomialFunctionSpace (estimationAlgebra f h)
  have hFF := polynomialGradientPair_mem_actual_function_space f h _ _ hF hF
  have hFFG := polynomialGradientPair_mem_actual_function_space f h _ _ hFF hG
  have hFG := polynomialGradientPair_mem_actual_function_space f h _ _ hF hG
  have hFFG' := polynomialGradientPair_mem_actual_function_space f h _ _ hF hFG
  have hH : radialCurvatureAssociator k l a b ∈ S := S.sub_mem hFFG hFFG'
  have hHH := polynomialGradientPair_mem_actual_function_space f h _ _ hH hH
  rw [radialCurvatureAssociator_gradient_square] at hHH
  have hc : (16 * (k ^ 2 + l ^ 2) ^ 3 : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 3 hn)
  have hscaled := S.smul_mem (16 * (k ^ 2 + l ^ 2) ^ 3 : ℝ)⁻¹ hHH
  apply (actualPolynomialFunctionSpace_mem_iff (estimationAlgebra f h) _).mp
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hscaled

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visible_radial_quadratic_member_of_radial_curvature_quadratics


/-! Source segment: FullRadialWongVisibleRigidity -/

/-! A genuine full radial quadratic provides a polynomial in its actual
carre-du-champ action that extracts homogeneous quadratic terms. This avoids
subtracting any unadmitted hidden linear multiplier. The resulting Jordan
associator eliminates visible Wong slopes before the hidden branch ladder. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open MvPolynomial

def fullRadialQuadraticPolynomial : RealPoly := X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2

def fullRadialHomogenization (p : RealPoly) : RealPoly :=
  (1 / 8 : ℝ) • polynomialGradientPair fullRadialQuadraticPolynomial
      (polynomialGradientPair fullRadialQuadraticPolynomial p) -
    (1 / 4 : ℝ) • polynomialGradientPair fullRadialQuadraticPolynomial p

theorem fullRadialHomogenization_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (p : RealPoly)
    (hq : fullRadialQuadraticPolynomial ∈
      actualPolynomialFunctionSpace (estimationAlgebra f h))
    (hp : p ∈ actualPolynomialFunctionSpace (estimationAlgebra f h)) :
    fullRadialHomogenization p ∈ actualPolynomialFunctionSpace (estimationAlgebra f h) := by
  let S := actualPolynomialFunctionSpace (estimationAlgebra f h)
  have hΓ := polynomialGradientPair_mem_actual_function_space f h _ _ hq hp
  have hΓΓ := polynomialGradientPair_mem_actual_function_space f h _ _ hq hΓ
  exact S.sub_mem (S.smul_mem (1 / 8 : ℝ) hΓΓ) (S.smul_mem (1 / 4 : ℝ) hΓ)

def fullRadialCurvatureZeroPolynomial (c k l a g : ℝ) : RealPoly :=
  (-2 : ℝ) • (X 1 * (C c + C k * X 0 + C l * X 1) + X 2 * (C g + C a * X 2))

def fullRadialCurvatureOnePolynomial (c k l b d : ℝ) : RealPoly :=
  (2 : ℝ) • (X 0 * (C c + C k * X 0 + C l * X 1) - X 2 * (C d + C b * X 2))

theorem fullRadialCurvatureZeroPolynomial_homogenization (c k l a g : ℝ) :
    fullRadialHomogenization (fullRadialCurvatureZeroPolynomial c k l a g) =
      (2 : ℝ) • radialCurvatureQuadraticZero k l a := by
  apply MvPolynomial.funext
  intro x
  simp [fullRadialHomogenization, fullRadialQuadraticPolynomial,
    fullRadialCurvatureZeroPolynomial, radialCurvatureQuadraticZero,
    polynomialGradientPair, Fin.sum_univ_three, smul_eq_C_mul, pow_two,
    Pi.single_apply, map_add, map_mul, map_pow]
  ring

theorem fullRadialCurvatureOnePolynomial_homogenization (c k l b d : ℝ) :
    fullRadialHomogenization (fullRadialCurvatureOnePolynomial c k l b d) =
      (2 : ℝ) • radialCurvatureQuadraticOne k l b := by
  apply MvPolynomial.funext
  intro x
  simp [fullRadialHomogenization, fullRadialQuadraticPolynomial,
    fullRadialCurvatureOnePolynomial, radialCurvatureQuadraticOne,
    polynomialGradientPair, Fin.sum_univ_three, smul_eq_C_mul, pow_two,
    Pi.single_apply, map_add, map_mul, map_pow]
  ring

theorem full_radial_curvature_homogeneous_members {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth fullRadialQuadraticPolynomial) ∈
      estimationAlgebra f h)
    (c k l a b g d : ℝ)
    (h01 : wong f 0 1 = polynomialSmooth (C c + C k * X 0 + C l * X 1))
    (h02 : wong f 0 2 = polynomialSmooth (C g + C a * X 2))
    (h12 : wong f 1 2 = polynomialSmooth (C d + C b * X 2)) :
    radialCurvatureQuadraticZero k l a ∈ actualPolynomialFunctionSpace (estimationAlgebra f h) ∧
    radialCurvatureQuadraticOne k l b ∈ actualPolynomialFunctionSpace (estimationAlgebra f h) := by
  let u := polynomialSmooth fullRadialQuadraticPolynomial
  let S := actualPolynomialFunctionSpace (estimationAlgebra f h)
  have hH (i : Fin 3) (hi : i = 0 ∨ i = 1) (j : Fin 3) :
      partialDerivative i (partialDerivative j u) =
        (if j = i then (2 : ℝ) else 0) • smoothOne := by
    dsimp only [u, fullRadialQuadraticPolynomial]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    rcases hi with rfl | rfl <;> fin_cases j
      <;> norm_num [polynomialSmooth, pow_two, Pi.single_apply, smoothOne]
  have hcurv0 := function_curvature_gradient_mem_of_visible_hessian_row
    f h hx0 hx1 u hq 0 (Or.inl rfl)
    (fun j => if j = 0 then (2 : ℝ) else 0) (hH 0 (Or.inl rfl)) (by norm_num)
  have hcurv1 := function_curvature_gradient_mem_of_visible_hessian_row
    f h hx0 hx1 u hq 1 (Or.inr rfl)
    (fun j => if j = 1 then (2 : ℝ) else 0) (hH 1 (Or.inr rfl)) (by norm_num)
  have heq0 : polynomialSmooth (fullRadialCurvatureZeroPolynomial c k l a g) =
      functionCurvatureGradient f u 0 := by
    dsimp only [functionCurvatureGradient, u, fullRadialQuadraticPolynomial]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    have h10 := congrArg (fun v : Smooth => v.1 x) (wong_skew f 0 1)
    have h20 := congrArg (fun v : Smooth => v.1 x) (wong_skew f 0 2)
    simp [polynomialSmooth, functionCurvatureGradient, u, fullRadialQuadraticPolynomial,
      fullRadialCurvatureZeroPolynomial, partialDerivative_polynomialSmooth,
      Fin.sum_univ_three, pow_two, Pi.single_apply, smoothMul_apply,
      h01, h02, smul_eq_C_mul] at *
    rw [h10, h20]
    ring
  have heq1 : polynomialSmooth (fullRadialCurvatureOnePolynomial c k l b d) =
      functionCurvatureGradient f u 1 := by
    dsimp only [functionCurvatureGradient, u, fullRadialQuadraticPolynomial]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    have h21 := congrArg (fun v : Smooth => v.1 x) (wong_skew f 1 2)
    simp [polynomialSmooth, functionCurvatureGradient, u, fullRadialQuadraticPolynomial,
      fullRadialCurvatureOnePolynomial, partialDerivative_polynomialSmooth,
      Fin.sum_univ_three, pow_two, Pi.single_apply, smoothMul_apply,
      h01, h12, smul_eq_C_mul] at *
    rw [h21]
    ring
  have hP0 : fullRadialCurvatureZeroPolynomial c k l a g ∈ S := by
    apply (actualPolynomialFunctionSpace_mem_iff (estimationAlgebra f h) _).mpr
    rwa [heq0]
  have hP1 : fullRadialCurvatureOnePolynomial c k l b d ∈ S := by
    apply (actualPolynomialFunctionSpace_mem_iff (estimationAlgebra f h) _).mpr
    rwa [heq1]
  have hF := fullRadialHomogenization_mem f h _ hq hP0
  have hG := fullRadialHomogenization_mem f h _ hq hP1
  rw [fullRadialCurvatureZeroPolynomial_homogenization] at hF
  rw [fullRadialCurvatureOnePolynomial_homogenization] at hG
  constructor
  · simpa using S.smul_mem (1 / 2 : ℝ) hF
  · simpa using S.smul_mem (1 / 2 : ℝ) hG

theorem full_radial_quadratic_visible_wong_slopes_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth fullRadialQuadraticPolynomial) ∈ estimationAlgebra f h)
    (c k l a b g d : ℝ)
    (h01 : wong f 0 1 = polynomialSmooth (C c + C k * X 0 + C l * X 1))
    (h02 : wong f 0 2 = polynomialSmooth (C g + C a * X 2))
    (h12 : wong f 1 2 = polynomialSmooth (C d + C b * X 2)) :
    k = 0 ∧ l = 0 := by
  by_cases hz : k = 0 ∧ l = 0
  · exact hz
  have hn : k ^ 2 + l ^ 2 ≠ 0 := by
    intro he
    apply hz
    constructor <;> nlinarith [sq_nonneg k, sq_nonneg l]
  obtain ⟨hF, hG⟩ := full_radial_curvature_homogeneous_members
    f h hx0 hx1 hq c k l a b g d h01 h02 h12
  have hvisible := visible_radial_quadratic_member_of_radial_curvature_quadratics
    f h k l a b hn hF hG
  exact visible_affine_wong_slopes_zero_of_radial_quadratic
    f h hrank hx0 hx1 hvisible c k l h01

end Wong.SmoothModel

#print axioms Wong.SmoothModel.full_radial_quadratic_visible_wong_slopes_zero
