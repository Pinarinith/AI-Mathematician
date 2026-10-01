import Wong.HiddenSquareWongRigidity
import Wong.VisibleWongQuadraticAnalysis
import Wong.VisibleFilteringHessianCompatibility
import Wong.SmoothCoordinateEuler

/-! Source segment: FullRadialHiddenWongRigidity.lean -/

/-! The full-radial quadratic case is reduced to the actual hidden-square
case after the independently proved visible Γ-associator obstruction.
No unverified highest-order omission from the paper is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open MvPolynomial

theorem full_radial_quadratic_hidden_wong_slopes_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth fullRadialQuadraticPolynomial)∈estimationAlgebra f h)
    (c k l a b g d : ℝ)
    (h01 : wong f 0 1=polynomialSmooth (C c+C k*X 0+C l*X 1))
    (h02 : wong f 0 2=polynomialSmooth (C g+C a*X 2))
    (h12 : wong f 1 2=polynomialSmooth (C d+C b*X 2)) :
    k=0 ∧ l=0 ∧ a=0 ∧ b=0 := by
  obtain ⟨hk,hl⟩ := full_radial_quadratic_visible_wong_slopes_zero
    f h hrank hx0 hx1 hq c k l a b g d h01 h02 h12
  obtain ⟨hF,hG⟩ := full_radial_curvature_homogeneous_members
    f h hx0 hx1 hq c k l a b g d h01 h02 h12
  let S := actualPolynomialFunctionSpace (estimationAlgebra f h)
  have hF' : (-a) • (X 2^2 : RealPoly)∈S := by
    simpa [radialCurvatureQuadraticZero,hk,hl,smul_eq_C_mul] using hF
  have hG' : (-b) • (X 2^2 : RealPoly)∈S := by
    simpa [radialCurvatureQuadraticOne,hk,hl,smul_eq_C_mul] using hG
  have hpure (z : ℝ) (hz : z≠0) (hzE : (-z) • (X 2^2 : RealPoly)∈S) :
      multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h := by
    have hs : (X 2^2 : RealPoly)∈S := by
      simpa only [smul_smul,inv_mul_cancel₀ (neg_ne_zero.mpr hz),one_smul] using
        S.smul_mem (-z)⁻¹ hzE
    change multiplication (polynomialSmooth (X 2^2))∈estimationAlgebra f h at hs
    simpa [pow_two,polynomialSmooth_mul,polynomialSmooth_coordinate,hiddenShearTime,smoothMul_eq_mul] using hs
  have hrow (j : Fin 3) : partialDerivative 2 (wong f 2 j)=
      (![(-a),(-b),0] : Fin 3 → ℝ) j • smoothOne := by
    fin_cases j
    · change partialDerivative 2 (wong f 2 0)=(-a) • smoothOne
      rw [wong_skew f 0 2,map_neg,h02,partialDerivative_polynomialSmooth]
      simp [polynomialSmooth_C]
    · change partialDerivative 2 (wong f 2 1)=(-b) • smoothOne
      rw [wong_skew f 1 2,map_neg,h12,partialDerivative_polynomialSmooth]
      simp [polynomialSmooth_C]
    · simp
  have hI : (1 : Operator)∈estimationAlgebra f h := by
    simpa only [multiplication_smoothOne] using
      smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have hz (hs : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h) :
      a=0 ∧ b=0 := by
    have hh := hidden_coordinate_square_forces_hidden_row_slopes_zero f h hI hs
      ![-a,-b,0] (by simp) hrow
    exact ⟨neg_eq_zero.mp hh.1,neg_eq_zero.mp hh.2⟩
  have ha : a=0 := by
    by_contra han
    exact han (hz (hpure a han hF')).1
  have hb : b=0 := by
    by_contra hbn
    exact hbn (hz (hpure b hbn hG')).2
  exact ⟨hk,hl,ha,hb⟩

theorem full_radial_quadratic_mixed_wong_constants_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth fullRadialQuadraticPolynomial)∈estimationAlgebra f h)
    (c g d : ℝ)
    (h01 : wong f 0 1=polynomialSmooth (C c))
    (h02 : wong f 0 2=polynomialSmooth (C g))
    (h12 : wong f 1 2=polynomialSmooth (C d)) : g=0 ∧ d=0 := by
  have hG0 := function_curvature_gradient_mem_of_adapted_rank_two f h hrank hx0 hx1
    (polynomialSmooth fullRadialQuadraticPolynomial) hq 0 (Or.inl rfl)
  have hG1 := function_curvature_gradient_mem_of_adapted_rank_two f h hrank hx0 hx1
    (polynomialSmooth fullRadialQuadraticPolynomial) hq 1 (Or.inr rfl)
  have he0 : functionCurvatureGradient f (polynomialSmooth fullRadialQuadraticPolynomial) 0 =
      linearFunction ![0,-2*c,-2*g] := by
    dsimp only [functionCurvatureGradient,fullRadialQuadraticPolynomial]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext z
    have h10 := congrArg (fun v : Smooth => v.1 z) (wong_skew f 0 1)
    have h20 := congrArg (fun v : Smooth => v.1 z) (wong_skew f 0 2)
    simp [Fin.sum_univ_three,h01,h02,polynomialSmooth,linearFunction,
      smoothMul,pow_two,Pi.single_apply] at *
    rw [h10,h20]
    ring
  have he1 : functionCurvatureGradient f (polynomialSmooth fullRadialQuadraticPolynomial) 1 =
      linearFunction ![2*c,0,-2*d] := by
    dsimp only [functionCurvatureGradient,fullRadialQuadraticPolynomial]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext z
    have h21 := congrArg (fun v : Smooth => v.1 z) (wong_skew f 1 2)
    simp [Fin.sum_univ_three,h01,h12,polynomialSmooth,linearFunction,
      smoothMul,pow_two,Pi.single_apply] at *
    rw [h21]
    ring
  rw [he0] at hG0
  rw [he1] at hG1
  have hg := rank_two_adapted_coefficient_zero (estimationAlgebra f h) hrank hx0 hx1
    ![0,-2*c,-2*g] hG0
  have hd := rank_two_adapted_coefficient_zero (estimationAlgebra f h) hrank hx0 hx1
    ![2*c,0,-2*d] hG1
  change -2*g=0 at hg
  change -2*d=0 at hd
  constructor <;> linarith

/-- Complete B1 curvature conclusion from the original actual model and
one genuine full-radial quadratic member. Affine Wong data are supplied by
the internally proved structural theorem; no quadratic-free hypothesis or
extra classification of the whole function space is imposed. -/
theorem full_radial_affine_wongConstant_and_mixed_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth fullRadialQuadraticPolynomial)∈estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀i j z,(wong f i j).1 z=p.matrix z i j) :
    WongConstant f ∧ wong f 0 2=0 ∧ wong f 1 2=0 := by
  obtain ⟨hk1,hk2,hh1,hh2⟩ := affine_diagonal_mixed_visible_slopes_zero f h hrank hx0 hx1 p hp
    (polynomialSmooth fullRadialQuadraticPolynomial) hq ![1,1,1] (by norm_num) (by
      intro j
      rw [partialDerivative_polynomialSmooth]
      apply Subtype.ext
      funext z
      fin_cases j <;> simp [fullRadialQuadraticPolynomial,polynomialSmooth,
        linearFunction,coordinateVector,Fin.sum_univ_three,pow_two] <;> ring)
  have h01 : wong f 0 1=polynomialSmooth (C p.b₀+C p.b₁*X 0+C p.b₂*X 1) := by
    apply Subtype.ext
    funext z
    rw [hp]
    simp [Wong.AffineParameters.matrix,Wong.AffineParameters.w12,polynomialSmooth]
    ring
  have h02 : wong f 0 2=polynomialSmooth (C p.k₀+C p.k₃*X 2) := by
    apply Subtype.ext
    funext z
    rw [hp]
    simp [Wong.AffineParameters.matrix,Wong.AffineParameters.w13,polynomialSmooth,hk1,hk2]
    ring
  have h12 : wong f 1 2=polynomialSmooth (C p.h₀+C p.h₃*X 2) := by
    apply Subtype.ext
    funext z
    rw [hp]
    simp [Wong.AffineParameters.matrix,Wong.AffineParameters.w23,polynomialSmooth,hh1,hh2]
    ring
  obtain ⟨hb1,hb2,hk3,hh3⟩ := full_radial_quadratic_hidden_wong_slopes_zero
    f h hrank hx0 hx1 hq p.b₀ p.b₁ p.b₂ p.k₃ p.h₃ p.k₀ p.h₀ h01 h02 h12
  have hc01 : wong f 0 1=polynomialSmooth (C p.b₀) := by simpa [hb1,hb2] using h01
  have hc02 : wong f 0 2=polynomialSmooth (C p.k₀) := by simpa [hk3] using h02
  have hc12 : wong f 1 2=polynomialSmooth (C p.h₀) := by simpa [hh3] using h12
  obtain ⟨hk0,hh0⟩ := full_radial_quadratic_mixed_wong_constants_zero
    f h hrank hx0 hx1 hq p.b₀ p.k₀ p.h₀ hc01 hc02 hc12
  have hz02 : wong f 0 2=0 := by simpa [hk0] using hc02
  have hz12 : wong f 1 2=0 := by simpa [hh0] using hc12
  refine ⟨⟨fun i j => (wong f i j).1 (0 : State),?_⟩,hz02,hz12⟩
  intro i j z
  fin_cases i <;> fin_cases j
    <;> simp [wong_skew f 0 1,wong_skew f 0 2,wong_skew f 1 2,hc01,hz02,hz12,
      polynomialSmooth]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.full_radial_quadratic_hidden_wong_slopes_zero
#print axioms Wong.SmoothModel.full_radial_quadratic_mixed_wong_constants_zero

#print axioms Wong.SmoothModel.full_radial_affine_wongConstant_and_mixed_zero

/-! Source segment: PureHiddenWongConstancy.lean -/

/-! Case A curvature conclusion. Unlike mere hidden-square membership, the
whole function-space condition supplies the visible Hessian obstruction.
It is kept as an explicit hypothesis here, to be obtained by classification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Wong.SmoothModel
open MvPolynomial

theorem pure_hidden_square_affine_wongConstant_and_mixed_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hsquare : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h)
    (hF : ∀ u : Smooth, multiplication u∈estimationAlgebra f h →
      ∀ i j : Fin 3,i≠2 → j≠2 → partialDerivative i (partialDerivative j u)=0)
    (p : Wong.AffineParameters) (hp : ∀i j z,(wong f i j).1 z=p.matrix z i j) :
    WongConstant f ∧ wong f 0 2=0 ∧ wong f 1 2=0 := by
  obtain ⟨h02,h12⟩ := hidden_square_affine_mixed_entries_zero f h hrank hx0 hx1 hsquare p hp
  have hI : (1 : Operator)∈estimationAlgebra f h := by
    simpa only [multiplication_smoothOne] using smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  let V := eta f h+(1/2 : ℝ) • smoothMul hiddenShearTime (partialDerivative 2 (eta f h))
  have hP : visibleFilteringOperator f V∈estimationAlgebra f h :=
    visible_filtering_member_of_hidden_square_and_mixed_zero f h hI hsquare h02 h12
  have h01 : wong f 0 1=polynomialSmooth (C p.b₀+C p.b₁*X 0+C p.b₂*X 1) := by
    apply Subtype.ext
    funext z
    rw [hp]
    simp [Wong.AffineParameters.matrix,Wong.AffineParameters.w12,polynomialSmooth]
    ring
  obtain ⟨hb1,hb2⟩ := visibleFiltering_wong_slopes_zero_of_visible_hessian_free
    f h V hP (D_mem_of_coordinate_mem f h 0 hx0) (D_mem_of_coordinate_mem f h 1 hx1)
    hF p.b₀ p.b₁ p.b₂ h01
  have hc01 : wong f 0 1=polynomialSmooth (C p.b₀) := by simpa [hb1,hb2] using h01
  refine ⟨⟨fun i j => (wong f i j).1 (0 : State),?_⟩,h02,h12⟩
  intro i j z
  fin_cases i <;> fin_cases j
    <;> simp [wong_skew f 0 1,wong_skew f 0 2,wong_skew f 1 2,hc01,h02,h12,
      polynomialSmooth]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.pure_hidden_square_affine_wongConstant_and_mixed_zero

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

theorem hidden_coordinateEuler_apply (u : Smooth) :
    coordinateEuler {2} u=smoothMul hiddenShearTime (partialDerivative 2 u) := by
  simp [coordinateEuler,Fin.sum_univ_three,hiddenShearTime,Module.End.mul_apply]

theorem hiddenEulerResolvent_eq_coordinateEuler (u : Smooth) :
    hiddenEulerResolvent u=
      (coordinateEuler {2}+(0 : ℝ) • (1 : Operator))
        ((coordinateEuler {2}+(2 : ℝ) • (1 : Operator)) u) := by
  simp only [zero_smul,add_zero,LinearMap.add_apply,LinearMap.smul_apply,
    Module.End.one_apply,hidden_coordinateEuler_apply]
  rfl

theorem hidden_coordinateEuler_eta_resolvent_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hI : (1 : Operator)∈estimationAlgebra f h)
    (hsquare : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h)
    (h02 : wong f 0 2=0) (h12 : wong f 1 2=0) :
    multiplication ((coordinateEuler {2}+(0 : ℝ) • (1 : Operator))
      ((coordinateEuler {2}+(2 : ℝ) • (1 : Operator)) (eta f h)))∈estimationAlgebra f h := by
  rw [← hiddenEulerResolvent_eq_coordinateEuler]
  exact hidden_euler_eta_resolvent_mem f h hI hsquare h02 h12

end Wong.SmoothModel

#print axioms Wong.SmoothModel.hidden_coordinateEuler_eta_resolvent_mem
