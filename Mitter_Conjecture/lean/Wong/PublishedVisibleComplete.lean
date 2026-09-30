import Wong.RankTwoFunctionCurvature
import Wong.PolynomialVisibleProductRigidity
import Wong.PolynomialHiddenSpecializationBridge
import Wong.IntrinsicWongPolynomial
import Wong.NormalSymbolsRing
import Wong.SmoothGeometry

/-! Consolidated internal proof of the full published visible-affinity assertion.
Only the initial imports above are external to this compilation unit; each is a
previously proved foundation-only operator, polynomial, or coordinate theorem. -/

/-!
# Removing quadratic-freeness from the visible Wong affinity proof

The constant-hidden-partial case uses the actual carré-du-champ function
and the actual curvature-gradient membership theorem. No published affinity
input, quadratic-freeness hypothesis, or target constancy theorem is used.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Wong.SmoothModel
open MvPolynomial Wong.PolynomialGradient

theorem curvatureGradient_hidden_independent_zero
    (f : Fin 3 → Smooth) (u : Smooth) (hu : partialDerivative 2 u = 0) :
    functionCurvatureGradient f u 0 = -smoothMul (partialDerivative 1 u) (wong f 0 1) := by
  simp only [functionCurvatureGradient, Fin.sum_univ_three, wong_self,
    wong_skew f 0 1, hu]
  apply Subtype.ext
  funext x
  simp [smoothMul]

theorem curvatureGradient_hidden_independent_one
    (f : Fin 3 → Smooth) (u : Smooth) (hu : partialDerivative 2 u = 0) :
    functionCurvatureGradient f u 1 = smoothMul (partialDerivative 0 u) (wong f 0 1) := by
  simp only [functionCurvatureGradient, Fin.sum_univ_three, wong_self, hu]
  apply Subtype.ext
  funext x
  simp [smoothMul]

/-- If the true visible Wong entry has constant hidden partial derivative,
its full real polynomial degree is at most one even without QFree. -/
theorem visible_wong_affine_of_hidden_partial_constant {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (g : ℝ) (hconstant : partialDerivative 2 (wong f 0 1) = g • smoothOne) :
    ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = wong f 0 1 := by
  have hw := wong_mem_of_coordinate_mem f h 0 1 hx₀ hx₁
  obtain ⟨p, hp, hpw⟩ := function_element_polynomial_degree_le_two f h _ hw
  refine ⟨p, ?_, hpw⟩
  by_contra hbad
  have hd : p.totalDegree = 2 := by omega
  let q := gradientSquare p
  have hqE : multiplication (polynomialSmooth q) ∈ estimationAlgebra f h := by
    rw [polynomial_gradient_double_commutator, hpw]
    exact (estimationAlgebra f h).lie_mem
      ((estimationAlgebra f h).lie_mem (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hw) hw
  have hqhidden : partialDerivative 2 (polynomialSmooth q) = 0 := by
    rw [polynomialSmooth_gradientSquare, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hi : partialDerivative 2 (partialDerivative i (polynomialSmooth p)) = 0 := by
      rw [hpw, partialDerivative_commute_apply 2 i, hconstant, partialDerivative_const]
    rw [partialDerivative_smoothMul, hi]
    apply Subtype.ext
    funext x
    simp [smoothMul]
  have hqhiddenP : pderiv 2 q = 0 := by
    apply polynomialSmooth_injective
    rw [← partialDerivative_polynomialSmooth, polynomialSmooth_zero, hqhidden]
  have hqd : q.totalDegree = 2 := by
    dsimp only [q]
    rw [gradientSquare_totalDegree p (by omega), hd]
  have hproduct₀ : (pderiv 0 q * p).totalDegree ≤ 2 := by
    apply polynomial_function_element_degree_le_two f h
    have he := function_curvature_gradient_mem_of_adapted_rank_two
      f h hrank hx₀ hx₁ _ hqE 1 (Or.inr rfl)
    rw [curvatureGradient_hidden_independent_one f _ hqhidden] at he
    simpa only [polynomialSmooth_mul, ← partialDerivative_polynomialSmooth, hpw] using he
  have hproduct₁ : (pderiv 1 q * p).totalDegree ≤ 2 := by
    have he := function_curvature_gradient_mem_of_adapted_rank_two
      f h hrank hx₀ hx₁ _ hqE 0 (Or.inl rfl)
    rw [curvatureGradient_hidden_independent_zero f _ hqhidden] at he
    have heq : polynomialSmooth (-(pderiv 1 q * p)) =
        -smoothMul (partialDerivative 1 (polynomialSmooth q)) (wong f 0 1) := by
      rw [partialDerivative_polynomialSmooth, ← hpw]
      apply Subtype.ext
      funext x
      simp [polynomialSmooth, smoothMul]
    have hneg : (-(pderiv 1 q * p)).totalDegree ≤ 2 := by
      apply polynomial_function_element_degree_le_two f h
      rw [heq]
      exact he
    simpa only [totalDegree_neg] using hneg
  obtain ⟨i, hi, hdi⟩ := hidden_independent_polynomial_has_maximal_visible_partial
    q (by omega) hqhiddenP
  have hprod : (pderiv i q * p).totalDegree ≤ 2 := by
    rcases hi with rfl | rfl
    · exact hproduct₀
    · exact hproduct₁
  have hpne : p ≠ 0 := by intro hz; simp [hz] at hd
  have hdqne : pderiv i q ≠ 0 := by
    intro hz
    simp [hz, hqd] at hdi
  rw [totalDegree_mul_of_isDomain hdqne hpne, hdi, hqd, hd] at hprod
  omega

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visible_wong_affine_of_hidden_partial_constant


/-! An actual critical hidden plane has affine visible Wong restriction.
No polynomial representation of the mixed Wong entries is required. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Wong.SmoothModel
open MvPolynomial

theorem curvatureGradient_point_hidden_zero_zero
    (f : Fin 3 → Smooth) (u : Smooth) (x : State)
    (hu : (partialDerivative 2 u).1 x = 0) :
    (functionCurvatureGradient f u 0).1 x =
      -(partialDerivative 1 u).1 x * (wong f 0 1).1 x := by
  simp [functionCurvatureGradient, Fin.sum_univ_three, smoothMul, hu,
    wong_skew f 0 1]

theorem curvatureGradient_point_hidden_zero_one
    (f : Fin 3 → Smooth) (u : Smooth) (x : State)
    (hu : (partialDerivative 2 u).1 x = 0) :
    (functionCurvatureGradient f u 1).1 x =
      (partialDerivative 0 u).1 x * (wong f 0 1).1 x := by
  simp [functionCurvatureGradient, Fin.sum_univ_three, smoothMul, hu]

/-- If the true hidden derivative of the visible Wong entry vanishes on a
hidden coordinate plane, the polynomial restriction to that plane is affine.
The degree bounds come from real curvature-gradient function elements. -/
theorem visible_wong_critical_hidden_slice_affine {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : RealPoly) (hpw : polynomialSmooth p = wong f 0 1)
    (t : ℝ) (ht : ∀ x : State,
      (partialDerivative 2 (wong f 0 1)).1 ![x 0, x 1, t] = 0) :
    (polynomialHiddenSpecialization t p).totalDegree ≤ 1 := by
  have hw := wong_mem_of_coordinate_mem f h 0 1 hx₀ hx₁
  obtain ⟨F₀, hF₀degree, hF₀⟩ := function_curvature_gradient_degree_le_two_of_rank_two
    f h hrank hx₀ hx₁ _ hw 0 (Or.inl rfl)
  obtain ⟨F₁, hF₁degree, hF₁⟩ := function_curvature_gradient_degree_le_two_of_rank_two
    f h hrank hx₀ hx₁ _ hw 1 (Or.inr rfl)
  let q := polynomialHiddenSpecialization t p
  have heval (x : State) : eval x q = (wong f 0 1).1 ![x 0, x 1, t] := by
    rw [eval_polynomialHiddenSpecialization]
    change (polynomialSmooth p).1 _ = _
    rw [hpw]
  have hpartial (i : Fin 3) (hi : i ≠ 2) (x : State) :
      eval x (pderiv i q) = (partialDerivative i (wong f 0 1)).1 ![x 0, x 1, t] := by
    rw [polynomialHiddenSpecialization_visible_partial t p i hi,
      eval_polynomialHiddenSpecialization]
    change (polynomialSmooth (pderiv i p)).1 _ = _
    rw [← partialDerivative_polynomialSmooth, hpw]
  have hprod₀ : pderiv 0 q * q = polynomialHiddenSpecialization t F₁ := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, heval, hpartial 0 (by decide), eval_polynomialHiddenSpecialization]
    change _ = (polynomialSmooth F₁).1 _
    rw [hF₁, curvatureGradient_point_hidden_zero_one f _ _ (ht x)]
  have hprod₁ : pderiv 1 q * q = -polynomialHiddenSpecialization t F₀ := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, heval, hpartial 1 (by decide), map_neg, eval_polynomialHiddenSpecialization]
    change _ = -(polynomialSmooth F₀).1 _
    rw [hF₀, curvatureGradient_point_hidden_zero_zero f _ _ (ht x)]
    ring
  apply hidden_independent_polynomial_degree_le_one_of_product_bounds q
    (polynomialHiddenSpecialization_hidden_partial_zero t p)
  · rw [hprod₀]
    exact (polynomialHiddenSpecialization_degree_le t F₁).trans hF₁degree
  · rw [hprod₁, totalDegree_neg]
    exact (polynomialHiddenSpecialization_degree_le t F₀).trans hF₀degree

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visible_wong_critical_hidden_slice_affine


/-! A genuine purely hidden quadratic function element removes the hidden
variation of the visible Wong entry. This uses polynomiality, Ocone, the
rank-two prohibition of mixed quadratic functions, and the actual Bianchi
identity. It does not use Wong affinity or quadratic-freeness. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open MvPolynomial

def hiddenAffinePolynomial (g k : ℝ) : RealPoly := C g + C k * X 2

theorem polynomialSmooth_hiddenAffinePolynomial (g k : ℝ) :
    polynomialSmooth (hiddenAffinePolynomial g k) =
      g • smoothOne + k • linearFunction (coordinateVector 2) := by
  apply Subtype.ext
  funext x
  simp [hiddenAffinePolynomial, polynomialSmooth, linearFunction, coordinateVector,
    Pi.single_apply, smoothOne]

theorem hiddenAffinePolynomial_positive_degree (g k : ℝ) (hk : k ≠ 0) :
    1 ≤ (hiddenAffinePolynomial g k).totalDegree := by
  have hc : (hiddenAffinePolynomial g k).coeff (Finsupp.single 2 1) = k := by
    have hne : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 2 1 := by
      intro he
      have hv := congrArg (fun d : Fin 3 →₀ ℕ => d 2) he
      simpa using hv
    simp [hiddenAffinePolynomial, hne]
  have hs : Finsupp.single 2 1 ∈ (hiddenAffinePolynomial g k).support := by
    rw [mem_support_iff, hc]
    exact hk
  simpa using le_totalDegree hs

theorem hiddenAffine_product_function_visible_partial_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (g k : ℝ) (hk : k ≠ 0) (r : RealPoly)
    (hrE : multiplication (polynomialSmooth (hiddenAffinePolynomial g k * r)) ∈
      estimationAlgebra f h)
    (j : Fin 3) (hj : j = 0 ∨ j = 1) :
    partialDerivative j (polynomialSmooth r) = 0 := by
  have hLp := hiddenAffinePolynomial_positive_degree g k hk
  have hLne : hiddenAffinePolynomial g k ≠ 0 := by intro hz; simp [hz] at hLp
  have hrdeg : r.totalDegree ≤ 1 := by
    by_cases hrz : r = 0
    · simp [hrz]
    have hp := polynomial_function_element_degree_le_two f h _ hrE
    rw [totalDegree_mul_of_isDomain hLne hrz] at hp
    omega
  obtain ⟨c, b, hb⟩ := polynomialSmooth_exists_affine_of_degree_le_one r hrdeg
  have hRj : partialDerivative j (polynomialSmooth r) = b j • smoothOne := by
    rw [hb, map_add, partialDerivative_const, partialDerivative_linearFunction, zero_add]
  have hj2 : j ≠ 2 := by rcases hj with rfl | rfl <;> decide
  have hAj : partialDerivative j (polynomialSmooth (hiddenAffinePolynomial g k)) = 0 := by
    rw [polynomialSmooth_hiddenAffinePolynomial, map_add, partialDerivative_const,
      map_smul, partialDerivative_linearFunction]
    simp [coordinateVector, hj2]
  have hA2 : partialDerivative 2 (polynomialSmooth (hiddenAffinePolynomial g k)) =
      k • smoothOne := by
    rw [polynomialSmooth_hiddenAffinePolynomial, map_add, partialDerivative_const,
      map_smul, partialDerivative_linearFunction]
    simp [coordinateVector]
  have hjE : multiplication (linearFunction (coordinateVector j)) ∈ estimationAlgebra f h := by
    rcases hj with rfl | rfl
    · exact hx₀
    · exact hx₁
  have hz := function_element_hidden_visible_mixed_zero f h hrank hx₀ hx₁ _ hrE j hjE
  rw [polynomialSmooth_mul, partialDerivative_smoothMul, hAj, hRj] at hz
  simp only [smoothMul_eq_mul, zero_mul, zero_add] at hz
  change partialDerivative 2 (smoothMul
    (polynomialSmooth (hiddenAffinePolynomial g k)) (b j • smoothOne)) = 0 at hz
  rw [partialDerivative_smoothMul, hA2, partialDerivative_const] at hz
  have hval := congrArg (fun u : Smooth => u.1 (0 : State)) hz
  have hbzero : b j = 0 := (mul_eq_zero.mp (by simpa [smoothMul, smoothOne] using hval)).resolve_left hk
  rw [hRj, hbzero, zero_smul]

/-- The existence of a true purely hidden quadratic function element already
forces the hidden partial of the visible Wong entry to vanish. -/
theorem hidden_quadratic_function_visible_wong_hidden_partial_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h)
    (hu₀ : partialDerivative 0 u = 0) (hu₁ : partialDerivative 1 u = 0)
    (g k : ℝ) (hk : k ≠ 0)
    (hu₂ : partialDerivative 2 u = g • smoothOne +
      k • linearFunction (coordinateVector 2)) : partialDerivative 2 (wong f 0 1) = 0 := by
  have hmix (i : Fin 3) (hi : i = 0 ∨ i = 1) (j : Fin 3) (hj : j = 0 ∨ j = 1) :
      partialDerivative j (wong f 2 i) = 0 := by
    obtain ⟨r, hr⟩ := wong_polynomialSmooth_of_rank_two f h hrank 2 i
    have he := function_curvature_gradient_mem_of_adapted_rank_two
      f h hrank hx₀ hx₁ u hu i hi
    have hshape : functionCurvatureGradient f u i = smoothMul
        (g • smoothOne + k • linearFunction (coordinateVector 2)) (wong f 2 i) := by
      simp only [functionCurvatureGradient, Fin.sum_univ_three, hu₀, hu₁, hu₂,
        smoothMul_eq_mul, zero_mul, zero_add]
    rw [hshape] at he
    have hrE : multiplication (polynomialSmooth (hiddenAffinePolynomial g k * r)) ∈
        estimationAlgebra f h := by
      simpa only [polynomialSmooth_mul, polynomialSmooth_hiddenAffinePolynomial, hr] using he
    rw [← hr]
    exact hiddenAffine_product_function_visible_partial_zero f h hrank hx₀ hx₁
      g k hk r hrE j hj
  have h20 := hmix 0 (Or.inl rfl) 1 (Or.inr rfl)
  have h21 := hmix 1 (Or.inr rfl) 0 (Or.inl rfl)
  rw [wong_skew f 0 2, map_neg, neg_eq_zero] at h20
  rw [wong_skew f 1 2, map_neg, neg_eq_zero] at h21
  have hb := wong_bianchi f 0 1 2
  simpa only [h20, h21, sub_zero, add_zero] using hb

end Wong.SmoothModel

#print axioms Wong.SmoothModel.hidden_quadratic_function_visible_wong_hidden_partial_zero


/-! Full adapted rank-two visible Wong affinity, without quadratic-freeness
or an external published theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open MvPolynomial

def hiddenQuadraticPolynomial (g k : ℝ) : RealPoly := C (k/2) * X 2 ^ 2 + C g * X 2

theorem pderiv_hiddenQuadraticPolynomial_two (g k : ℝ) :
    pderiv 2 (hiddenQuadraticPolynomial g k) = hiddenAffinePolynomial g k := by
  apply MvPolynomial.funext
  intro x
  simp [hiddenQuadraticPolynomial, hiddenAffinePolynomial, pderiv_X]
  ring

theorem pderiv_hiddenQuadraticPolynomial_visible (g k : ℝ) (i : Fin 3) (hi : i ≠ 2) :
    pderiv i (hiddenQuadraticPolynomial g k) = 0 := by
  simp [hiddenQuadraticPolynomial, pderiv_X, Ne.symm hi]

theorem hiddenQuadraticPolynomial_specialization (g k t : ℝ) :
    polynomialHiddenSpecialization t (hiddenQuadraticPolynomial g k) =
      C ((k/2)*t^2+g*t) := by
  simp [hiddenQuadraticPolynomial, polynomialHiddenSpecialization_X]

theorem polynomial_affine_visible_remainder_of_critical_slice
    (p : RealPoly) (g k t : ℝ)
    (hp : pderiv 2 p = hiddenAffinePolynomial g k)
    (hslice : (polynomialHiddenSpecialization t p).totalDegree ≤ 1) :
    ∃ q : RealPoly, q.totalDegree ≤ 1 ∧ pderiv 2 q = 0 ∧
      p = q + hiddenQuadraticPolynomial g k := by
  let q := p - hiddenQuadraticPolynomial g k
  have hq₂ : pderiv 2 q = 0 := by
    rw [map_sub, hp, pderiv_hiddenQuadraticPolynomial_two, sub_self]
  have hqshape : q = polynomialHiddenSpecialization t p - C ((k/2)*t^2+g*t) := by
    calc
      q = polynomialHiddenSpecialization t q :=
        (polynomialHiddenSpecialization_eq_self_of_hidden_partial_zero t q hq₂).symm
      _ = _ := by rw [map_sub, hiddenQuadraticPolynomial_specialization]
  refine ⟨q, ?_, hq₂, ?_⟩
  · rw [hqshape]
    exact (totalDegree_sub_C_le _ _).trans hslice
  · dsimp only [q]
    ring

theorem affine_hidden_independent_polynomial_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (q : RealPoly) (hq : q.totalDegree ≤ 1) (hq₂ : pderiv 2 q = 0) :
    multiplication (polynomialSmooth q) ∈ estimationAlgebra f h := by
  obtain ⟨c, a, ha⟩ := polynomialSmooth_exists_affine_of_degree_le_one q hq
  have hd : a 2 • smoothOne = 0 := by
    have hh := partialDerivative_polynomialSmooth 2 q
    rw [ha, map_add, partialDerivative_const, partialDerivative_linearFunction,
      zero_add, hq₂, polynomialSmooth_zero] at hh
    exact hh
  have ha₂ : a 2 = 0 := by
    simpa [smoothOne] using congrArg (fun u : Smooth => u.1 (0 : State)) hd
  have hshape : linearFunction a = a 0 • linearFunction (coordinateVector 0) +
      a 1 • linearFunction (coordinateVector 1) := by
    apply Subtype.ext
    funext x
    simp [linearFunction, Fin.sum_univ_three, coordinateVector, Pi.single_apply, ha₂]
  rw [ha, hshape, multiplication_add, multiplication_smul, multiplication_add,
    multiplication_smul, multiplication_smul]
  exact (estimationAlgebra f h).add_mem
    ((estimationAlgebra f h).smul_mem c (smoothOne_mem_estimationAlgebra_of_rank_two f h hrank))
    ((estimationAlgebra f h).add_mem ((estimationAlgebra f h).smul_mem _ hx₀)
      ((estimationAlgebra f h).smul_mem _ hx₁))

/-- Shi--Yau 2017 Theorem 3.4's affine conclusion from its actual rank-two
hypotheses, proved internally and without quadratic-freeness. -/
theorem visible_wong_affine_without_quadraticFree {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = wong f 0 1 := by
  have hw := wong_mem_of_coordinate_mem f h 0 1 hx₀ hx₁
  obtain ⟨g, k, hhidden⟩ := function_element_hidden_partial_affine_hidden f h hrank hx₀ hx₁ _ hw
  by_cases hk : k = 0
  · apply visible_wong_affine_of_hidden_partial_constant f h hrank hx₀ hx₁ g
    simpa only [hk, zero_smul, add_zero] using hhidden
  obtain ⟨p, _, hpw⟩ := function_element_polynomial_degree_le_two f h _ hw
  let t := -g/k
  have ht (x : State) : (partialDerivative 2 (wong f 0 1)).1 ![x 0, x 1, t] = 0 := by
    rw [hhidden]
    simp [linearFunction, coordinateVector, Pi.single_apply, smoothOne, t] <;>
      field_simp [hk] <;> ring
  have hslice := visible_wong_critical_hidden_slice_affine f h hrank hx₀ hx₁ p hpw t ht
  have hp₂ : pderiv 2 p = hiddenAffinePolynomial g k := by
    apply polynomialSmooth_injective
    rw [← partialDerivative_polynomialSmooth, hpw, hhidden,
      polynomialSmooth_hiddenAffinePolynomial]
  obtain ⟨q, hqd, hq₂, hpq⟩ :=
    polynomial_affine_visible_remainder_of_critical_slice p g k t hp₂ hslice
  have hqE := affine_hidden_independent_polynomial_mem f h hrank hx₀ hx₁ q hqd hq₂
  have hHE : multiplication (polynomialSmooth (hiddenQuadraticPolynomial g k)) ∈
      estimationAlgebra f h := by
    have he : hiddenQuadraticPolynomial g k = p-q := by rw [hpq]; ring
    rw [he]
    change polynomialMultiplicationLinear (p-q) ∈ estimationAlgebra f h
    rw [map_sub]
    apply (estimationAlgebra f h).sub_mem ?_ hqE
    change multiplication (polynomialSmooth p) ∈ estimationAlgebra f h
    rw [hpw]
    exact hw
  have hH₀ : partialDerivative 0 (polynomialSmooth (hiddenQuadraticPolynomial g k)) = 0 := by
    rw [partialDerivative_polynomialSmooth,
      pderiv_hiddenQuadraticPolynomial_visible g k 0 (by decide), polynomialSmooth_zero]
  have hH₁ : partialDerivative 1 (polynomialSmooth (hiddenQuadraticPolynomial g k)) = 0 := by
    rw [partialDerivative_polynomialSmooth,
      pderiv_hiddenQuadraticPolynomial_visible g k 1 (by decide), polynomialSmooth_zero]
  have hH₂ : partialDerivative 2 (polynomialSmooth (hiddenQuadraticPolynomial g k)) =
      g • smoothOne + k • linearFunction (coordinateVector 2) := by
    rw [partialDerivative_polynomialSmooth, pderiv_hiddenQuadraticPolynomial_two,
      polynomialSmooth_hiddenAffinePolynomial]
  have hz := hidden_quadratic_function_visible_wong_hidden_partial_zero f h hrank hx₀ hx₁
    _ hHE hH₀ hH₁ g k hk hH₂
  apply visible_wong_affine_of_hidden_partial_constant f h hrank hx₀ hx₁ 0
  simpa only [zero_smul] using hz

/-- Full visible polynomial statement, including absence of the hidden
coordinate, under the published theorem's actual adapted hypotheses. -/
theorem visible_wong_published_polynomial_without_quadraticFree {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ pderiv 2 p = 0 ∧ polynomialSmooth p = wong f 0 1 := by
  obtain ⟨p, hpd, hpw⟩ := visible_wong_affine_without_quadraticFree f h hrank hx₀ hx₁
  obtain ⟨c, a, ha⟩ := polynomialSmooth_exists_affine_of_degree_le_one p hpd
  have hw := wong_mem_of_coordinate_mem f h 0 1 hx₀ hx₁
  have haE : a ∈ linearCoefficientSpace (estimationAlgebra f h) := by
    change multiplication (linearFunction a) ∈ estimationAlgebra f h
    have hsub := (estimationAlgebra f h).sub_mem hw
      ((estimationAlgebra f h).smul_mem c (smoothOne_mem_estimationAlgebra_of_rank_two f h hrank))
    rw [← hpw, ha] at hsub
    simpa only [multiplication_add, multiplication_smul, add_sub_cancel_left] using hsub
  have ha₂ := rank_two_adapted_coefficient_zero (estimationAlgebra f h) hrank hx₀ hx₁ a haE
  refine ⟨p, hpd, ?_, hpw⟩
  apply polynomialSmooth_injective
  rw [← partialDerivative_polynomialSmooth, ha, map_add, partialDerivative_const,
    partialDerivative_linearFunction, ha₂, zero_smul, zero_add, polynomialSmooth_zero]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.visible_wong_published_polynomial_without_quadraticFree
