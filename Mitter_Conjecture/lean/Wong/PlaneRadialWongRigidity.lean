import Wong.HiddenSquareWongRigidity
import Wong.VisibleWongQuadraticAnalysis
import Wong.QuadraticHiddenLinearTail

/-! Source segment: PlaneRadialWongFunctions.lean -/

/-! Exact function-element words for the B2 plane-radial quadratic case.
Every polynomial operation below is justified by linear or carré-du-champ
closure of the actual operator Lie algebra. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Wong.SmoothModel
open MvPolynomial

def planeRadialPolynomial : RealPoly := X 0^2+X 2^2

def planeCurvatureZero (a g : ℝ) : RealPoly := -C a*X 2^2-C g*X 2

def planeCurvatureOne (c k l b d : ℝ) : RealPoly :=
  C k*X 0^2+C l*X 0*X 1+C c*X 0-C b*X 2^2-C d*X 2

theorem plane_radial_curvature_members {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth planeRadialPolynomial)∈estimationAlgebra f h)
    (c k l a b g d : ℝ)
    (h01 : wong f 0 1=polynomialSmooth (C c+C k*X 0+C l*X 1))
    (h02 : wong f 0 2=polynomialSmooth (C g+C a*X 2))
    (h12 : wong f 1 2=polynomialSmooth (C d+C b*X 2)) :
    planeCurvatureZero a g∈actualPolynomialFunctionSpace (estimationAlgebra f h) ∧
    planeCurvatureOne c k l b d∈actualPolynomialFunctionSpace (estimationAlgebra f h) := by
  let S := actualPolynomialFunctionSpace (estimationAlgebra f h)
  have hm0 := function_curvature_gradient_mem_of_adapted_rank_two f h hrank hx0 hx1
    (polynomialSmooth planeRadialPolynomial) hq 0 (Or.inl rfl)
  have hm1 := function_curvature_gradient_mem_of_adapted_rank_two f h hrank hx0 hx1
    (polynomialSmooth planeRadialPolynomial) hq 1 (Or.inr rfl)
  have he0 : polynomialSmooth ((2 : ℝ) • planeCurvatureZero a g)=
      functionCurvatureGradient f (polynomialSmooth planeRadialPolynomial) 0 := by
    dsimp only [functionCurvatureGradient,planeRadialPolynomial]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext z
    have h20 := congrArg (fun v : Smooth => v.1 z) (wong_skew f 0 2)
    simp [planeCurvatureZero,polynomialSmooth,Fin.sum_univ_three,
      h02,smoothMul,pow_two,Pi.single_apply,smul_eq_C_mul] at *
    rw [h20]
    ring
  have he1 : polynomialSmooth ((2 : ℝ) • planeCurvatureOne c k l b d)=
      functionCurvatureGradient f (polynomialSmooth planeRadialPolynomial) 1 := by
    dsimp only [functionCurvatureGradient,planeRadialPolynomial]
    simp only [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext z
    have h21 := congrArg (fun v : Smooth => v.1 z) (wong_skew f 1 2)
    simp [planeCurvatureOne,polynomialSmooth,Fin.sum_univ_three,
      h01,h12,smoothMul,pow_two,Pi.single_apply,smul_eq_C_mul] at *
    rw [h21]
    ring
  rw [← he0] at hm0
  rw [← he1] at hm1
  have hF : (2 : ℝ) • planeCurvatureZero a g∈S := hm0
  have hG : (2 : ℝ) • planeCurvatureOne c k l b d∈S := hm1
  constructor
  · simpa only [smul_smul,show (1/2 : ℝ)*2=1 by norm_num,one_smul] using S.smul_mem (1/2 : ℝ) hF
  · simpa only [smul_smul,show (1/2 : ℝ)*2=1 by norm_num,one_smul] using S.smul_mem (1/2 : ℝ) hG

theorem planeRadial_hidden_square_filter (a g : ℝ) :
    polynomialGradientPair planeRadialPolynomial (planeCurvatureZero a g)-
      (2 : ℝ) • planeCurvatureZero a g =(-2*a) • (X 2^2 : RealPoly) := by
  apply MvPolynomial.funext
  intro z
  simp [polynomialGradientPair,planeRadialPolynomial,planeCurvatureZero,
    Fin.sum_univ_three,pow_two,Pi.single_apply,smul_eq_C_mul]
  ring

theorem planeRadial_binary_tail_filter (c k l b d : ℝ) :
    (4 : ℝ) • polynomialGradientPair planeRadialPolynomial (planeCurvatureOne c k l b d)-
      polynomialGradientPair planeRadialPolynomial
        (polynomialGradientPair planeRadialPolynomial (planeCurvatureOne c k l b d)) =
      (4 : ℝ) • (C l*X 0*X 1+C c*X 0-C d*X 2) := by
  apply MvPolynomial.funext
  intro z
  simp [polynomialGradientPair,planeRadialPolynomial,planeCurvatureOne,
    Fin.sum_univ_three,pow_two,Pi.single_apply,smul_eq_C_mul]
  ring

/-- The first mixed entry vanishes through an actually recovered hidden
square. No illegal subtraction of x₀² from the given plane square occurs. -/
theorem plane_radial_first_mixed_entry_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth planeRadialPolynomial)∈estimationAlgebra f h)
    (a b g d : ℝ)
    (hF : planeCurvatureZero a g∈actualPolynomialFunctionSpace (estimationAlgebra f h))
    (h02 : wong f 0 2=polynomialSmooth (C g+C a*X 2))
    (h12 : wong f 1 2=polynomialSmooth (C d+C b*X 2)) : a=0 ∧ g=0 := by
  let S := actualPolynomialFunctionSpace (estimationAlgebra f h)
  have hΓ := polynomialGradientPair_mem_actual_function_space f h _ _ hq hF
  have hfilter := S.sub_mem hΓ (S.smul_mem 2 hF)
  rw [planeRadial_hidden_square_filter] at hfilter
  have ha : a=0 := by
    by_contra han
    have hn : -2*a≠0 := mul_ne_zero (by norm_num) han
    have ht : (X 2^2 : RealPoly)∈S := by
      simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using S.smul_mem (-2*a)⁻¹ hfilter
    have ht' : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h := by
      change multiplication (polynomialSmooth (X 2^2))∈estimationAlgebra f h at ht
      simpa [pow_two,polynomialSmooth_mul,polynomialSmooth_coordinate,hiddenShearTime] using ht
    have hI : (1 : Operator)∈estimationAlgebra f h := by
      simpa only [multiplication_smoothOne] using smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
    have hrow (j : Fin 3) : partialDerivative 2 (wong f 2 j)=
        (![-a,-b,0] : Fin 3 → ℝ) j • smoothOne := by
      fin_cases j
      · change partialDerivative 2 (wong f 2 0)=(-a) • smoothOne
        rw [wong_skew f 0 2,map_neg,h02,partialDerivative_polynomialSmooth]
        simp
      · change partialDerivative 2 (wong f 2 1)=(-b) • smoothOne
        rw [wong_skew f 1 2,map_neg,h12,partialDerivative_polynomialSmooth]
        simp
      · simp
    have hz := hidden_coordinate_square_forces_hidden_row_slopes_zero f h hI ht'
      ![-a,-b,0] (by simp) hrow
    exact han (neg_eq_zero.mp hz.1)
  have he : polynomialSmooth (planeCurvatureZero a g)=linearFunction ![0,0,-g] := by
    apply Subtype.ext
    funext z
    simp [planeCurvatureZero,ha,polynomialSmooth,linearFunction,Fin.sum_univ_three]
  have hm : multiplication (linearFunction ![0,0,-g])∈estimationAlgebra f h := by
    change multiplication (polynomialSmooth (planeCurvatureZero a g))∈estimationAlgebra f h at hF
    rwa [he] at hF
  have hg := rank_two_adapted_coefficient_zero (estimationAlgebra f h) hrank hx0 hx1 ![0,0,-g] hm
  exact ⟨ha,neg_eq_zero.mp hg⟩

/-- The second visible slope and the second hidden constant vanish through
an actual binary-quadratic function member and its carré-du-champ square. -/
theorem plane_radial_second_visible_slope_and_hidden_constant_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth planeRadialPolynomial)∈estimationAlgebra f h)
    (c k l b d : ℝ)
    (hF : planeCurvatureOne c k l b d∈actualPolynomialFunctionSpace (estimationAlgebra f h))
    (h01 : wong f 0 1=polynomialSmooth (C c+C k*X 0+C l*X 1)) : l=0 ∧ d=0 := by
  let S := actualPolynomialFunctionSpace (estimationAlgebra f h)
  have hΓ := polynomialGradientPair_mem_actual_function_space f h _ _ hq hF
  have hΓΓ := polynomialGradientPair_mem_actual_function_space f h _ _ hq hΓ
  have hH := S.sub_mem (S.smul_mem 4 hΓ) hΓΓ
  rw [planeRadial_binary_tail_filter] at hH
  have ht : C l*X 0*X 1+C c*X 0-C d*X 2∈S := by
    simpa only [smul_smul,show (1/4 : ℝ)*4=1 by norm_num,one_smul] using S.smul_mem (1/4 : ℝ) hH
  have hx : (X 0 : RealPoly)∈S := by
    change multiplication (polynomialSmooth (X 0))∈estimationAlgebra f h
    rwa [polynomialSmooth_coordinate]
  have htail : visibleBinaryQuadratic 0 (l/2) 0+C (-d)*X 2∈S := by
    have he : (C l*X 0*X 1+C c*X 0-C d*X 2)-c • (X 0 : RealPoly)=
        visibleBinaryQuadratic 0 (l/2) 0+C (-d)*X 2 := by
      apply MvPolynomial.funext
      intro z
      simp [visibleBinaryQuadratic,smul_eq_C_mul]
      ring
    rw [← he]
    exact S.sub_mem ht (S.smul_mem c hx)
  have hd' := hidden_linear_tail_zero_of_visible_binary_quadratic_member
    f h hrank hx0 hx1 0 (l/2) 0 (-d) htail
  have hd : d=0 := neg_eq_zero.mp hd'
  have hl : l=0 := by
    by_contra hln
    have hxy : l • (X 0*X 1 : RealPoly)∈S := by
      convert htail using 1
      apply MvPolynomial.funext
      intro z
      simp [hd,visibleBinaryQuadratic,smul_eq_C_mul]
      ring
    have hxy' : (X 0*X 1 : RealPoly)∈S := by
      simpa only [smul_smul,inv_mul_cancel₀ hln,one_smul] using S.smul_mem l⁻¹ hxy
    have hrad := polynomialGradientPair_mem_actual_function_space f h _ _ hxy' hxy'
    have he : polynomialGradientPair (X 0*X 1 : RealPoly) (X 0*X 1)=X 0^2+X 1^2 := by
      simp [polynomialGradientPair,Fin.sum_univ_three,pow_two,Pi.single_apply]
      ring
    rw [he] at hrad
    have hh := visible_affine_wong_slopes_zero_of_radial_quadratic
      f h hrank hx0 hx1 hrad c k l h01
    exact hln hh.2
  exact ⟨hl,hd⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.plane_radial_first_mixed_entry_zero
#print axioms Wong.SmoothModel.plane_radial_second_visible_slope_and_hidden_constant_zero

/-! Source segment: PlaneRadialWongWords.lean -/

/-! Genuine B2 resonant finite words. No scalar remainder is discarded and
no membership of the hidden covariant derivative is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Wong.SmoothModel

theorem planeOperator_neg_mul (A B : Operator) : (-A)*B=-(A*B) := by
  apply LinearMap.ext
  intro u
  rfl

theorem planeOperator_mul_neg (A B : Operator) : A*(-B)=-(A*B) := by
  apply LinearMap.ext
  intro u
  exact map_neg A (B u)

def planeRadialSmooth : Smooth :=
  smoothMul (linearFunction (coordinateVector 0)) (linearFunction (coordinateVector 0))+
    smoothMul hiddenShearTime hiddenShearTime

def planeCovariantEuler (f : Fin 3 → Smooth) : Operator :=
  multiplication (linearFunction (coordinateVector 0))*D f 0+
    multiplication hiddenShearTime*D f 2

def planeEulerDerivative (u : Smooth) : Smooth :=
  smoothMul (linearFunction (coordinateVector 0)) (partialDerivative 0 u)+
    smoothMul hiddenShearTime (partialDerivative 2 u)

theorem lie_planeCovariantEuler_multiplier (f : Fin 3 → Smooth) (u : Smooth) :
    ⁅planeCovariantEuler f,multiplication u⁆=multiplication (planeEulerDerivative u) := by
  simp only [planeCovariantEuler,add_lie,lie_covariant_monomial_multiplier,
    planeEulerDerivative,multiplication_add]

theorem planeCovariantEuler_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hI : (1 : Operator)∈estimationAlgebra f h)
    (hq : multiplication planeRadialSmooth∈estimationAlgebra f h) :
    planeCovariantEuler f∈estimationAlgebra f h := by
  have hLX (i : Fin 3) : ⁅L0 f h,multiplication (linearFunction (coordinateVector i))⁆=D f i :=
    (lie_L0_linearFunction f h (coordinateVector i)).trans (directionD_coordinate f i)
  have hDX (i : Fin 3) : ⁅D f i,multiplication (linearFunction (coordinateVector i))⁆=1 := by
    simp [lie_D_multiplication,partialDerivative_linearFunction,coordinateVector]
  have he : planeCovariantEuler f=(1/2 : ℝ) • ⁅L0 f h,multiplication planeRadialSmooth⁆-1 := by
    rw [planeCovariantEuler,← c2Z_eq (L0 f h) _ _ (hLX 0) (hDX 0),
      show hiddenShearTime=linearFunction (coordinateVector 2) from rfl,
      ← c2Z_eq (L0 f h) _ _ (hLX 2) (hDX 2)]
    simp only [c2Z,planeRadialSmooth,hiddenShearTime,multiplication_add,
      lie_add,multiplication_mul]
    module
  rw [he]
  exact (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).smul_mem _ ((estimationAlgebra f h).lie_mem
      (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hq)) hI

def planeResonantCoefficient (k c : ℝ) : Smooth :=
  k • planeRadialSmooth+c • linearFunction (coordinateVector 0)

theorem lie_planeCovariantEuler_D_resonant (f : Fin 3 → Smooth) (k c : ℝ)
    (h01 : wong f 0 1=k • linearFunction (coordinateVector 0)+c • smoothOne)
    (h02 : wong f 0 2=0)
    (h12 : wong f 1 2=(-k) • hiddenShearTime) :
    ⁅planeCovariantEuler f,D f 0⁆= -D f 0 ∧
    ⁅planeCovariantEuler f,D f 1⁆= -multiplication (planeResonantCoefficient k c) ∧
    ⁅planeCovariantEuler f,D f 2⁆= -D f 2 := by
  have hM (i j : Fin 3) :
      ⁅multiplication (linearFunction (coordinateVector i)),D f j⁆=
        -multiplication ((coordinateVector i j) • smoothOne) := by
    rw [← lie_skew,lie_D_multiplication,partialDerivative_linearFunction]
  have h10 : wong f 1 0=-(k • linearFunction (coordinateVector 0)+c • smoothOne) := by
    rw [wong_skew f 0 1,h01]
  have h20 : wong f 2 0=0 := by rw [wong_skew f 0 2,h02,neg_zero]
  have h21 : wong f 2 1=-((-k) • hiddenShearTime) := by rw [wong_skew f 1 2,h12]
  constructor
  · simp only [planeCovariantEuler,hiddenShearTime,add_lie,operator_lie_mul_left,
      lie_D_D,hM]
    simp [coordinateVector,h02,planeOperator_neg_mul]
  constructor
  · simp only [planeCovariantEuler,hiddenShearTime,add_lie,operator_lie_mul_left,
      lie_D_D,hM,h10,h12]
    simp only [coordinateVector,Pi.single_apply]
    norm_num
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext z
    simp [Module.End.mul_apply,multiplication_apply,planeResonantCoefficient,
      planeRadialSmooth,hiddenShearTime,smoothMul,coordinateVector]
    ring
  · simp only [planeCovariantEuler,hiddenShearTime,add_lie,operator_lie_mul_left,
      lie_D_D,hM]
    simp [coordinateVector,h20,planeOperator_neg_mul]

theorem planeResonantCoefficient_derivatives (k c : ℝ) :
    partialDerivative 1 (planeResonantCoefficient k c)=0 ∧
    planeEulerDerivative (planeResonantCoefficient k c)=
      (2*k) • planeRadialSmooth+c • linearFunction (coordinateVector 0) := by
  constructor
  · simp only [planeResonantCoefficient,planeRadialSmooth,hiddenShearTime,
      map_add,map_smul,partialDerivative_smoothMul,partialDerivative_linearFunction]
    simp [coordinateVector,smoothMul_eq_mul]
  · simp only [planeEulerDerivative,planeResonantCoefficient,planeRadialSmooth,
      hiddenShearTime,map_add,map_smul,partialDerivative_smoothMul,
      partialDerivative_linearFunction]
    apply Subtype.ext
    funext z
    simp [coordinateVector,smoothMul,smoothOne]
    ring

/-- Exact resonant K, including its full eta scalar. -/
theorem planeResonant_K_exact {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (k c : ℝ)
    (h01 : wong f 0 1=k • linearFunction (coordinateVector 0)+c • smoothOne)
    (h02 : wong f 0 2=0)
    (h12 : wong f 1 2=(-k) • hiddenShearTime) :
    ⁅L0 f h,planeCovariantEuler f⁆-(2 : ℝ) • L0 f h =
      -(D f 1*D f 1)+multiplication (planeResonantCoefficient k c)*D f 1+
        multiplication (eta f h+(1/2 : ℝ) • planeEulerDerivative (eta f h)) := by
  obtain ⟨hZ0,hZ1,hZ2⟩ := lie_planeCovariantEuler_D_resonant f k c h01 h02 h12
  have h0 : ⁅D f 0,planeCovariantEuler f⁆=D f 0 := by rw [← lie_skew,hZ0,neg_neg]
  have h1 : ⁅D f 1,planeCovariantEuler f⁆=multiplication (planeResonantCoefficient k c) := by
    rw [← lie_skew,hZ1,neg_neg]
  have h2 : ⁅D f 2,planeCovariantEuler f⁆=D f 2 := by rw [← lie_skew,hZ2,neg_neg]
  have hV : ⁅multiplication (eta f h),planeCovariantEuler f⁆=
      -multiplication (planeEulerDerivative (eta f h)) := by
    rw [← lie_skew,lie_planeCovariantEuler_multiplier]
  have hDB : D f 1*multiplication (planeResonantCoefficient k c)=
      multiplication (planeResonantCoefficient k c)*D f 1 := by
    have hc := lie_D_multiplication f 1 (planeResonantCoefficient k c)
    rw [(planeResonantCoefficient_derivatives k c).1,multiplication_zero,operator_lie_def] at hc
    exact sub_eq_zero.mp hc
  simp only [L0,sub_lie,smul_lie,Fin.sum_univ_three,add_lie,operator_lie_mul_left,
    h0,h1,h2,hV,hDB,multiplication_add,multiplication_smul]
  module

/-- A universal actual first-order bracket with the complete scalar shown. -/
theorem planeResonant_bracket_firstOrder (f : Fin 3 → Smooth) (B C s : Smooth)
    (hZD : ⁅planeCovariantEuler f,D f 1⁆= -multiplication B) :
    ⁅planeCovariantEuler f,multiplication C*D f 1+multiplication s⁆ =
      multiplication (planeEulerDerivative C)*D f 1+
        multiplication (planeEulerDerivative s-smoothMul C B) := by
  rw [lie_add,operator_lie_mul_right,lie_planeCovariantEuler_multiplier,
    hZD,lie_planeCovariantEuler_multiplier,planeOperator_mul_neg,multiplication_mul,multiplication_sub]
  abel

theorem plane_resonant_quadratic_shear_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hI : (1 : Operator)∈estimationAlgebra f h)
    (hq : multiplication planeRadialSmooth∈estimationAlgebra f h)
    (k c : ℝ)
    (h01 : wong f 0 1=k • linearFunction (coordinateVector 0)+c • smoothOne)
    (h02 : wong f 0 2=0)
    (h12 : wong f 1 2=(-k) • hiddenShearTime) :
    ∃ s : Smooth,firstOrder f ![0,(4*k) • planeRadialSmooth,0] s∈estimationAlgebra f h := by
  let Z := planeCovariantEuler f
  let B := planeResonantCoefficient k c
  let s := eta f h+(1/2 : ℝ) • planeEulerDerivative (eta f h)
  let C := (4*k) • planeRadialSmooth+(3*c) • linearFunction (coordinateVector 0)
  let t := planeEulerDerivative s-smoothMul B B
  have hZD : ⁅Z,D f 1⁆= -multiplication B :=
    (lie_planeCovariantEuler_D_resonant f k c h01 h02 h12).2.1
  have hDB : D f 1*multiplication B=multiplication B*D f 1 := by
    have hc := lie_D_multiplication f 1 B
    rw [(planeResonantCoefficient_derivatives k c).1,multiplication_zero,operator_lie_def] at hc
    exact sub_eq_zero.mp hc
  have hC : (2 : ℝ) • B+planeEulerDerivative B=C := by
    rw [(planeResonantCoefficient_derivatives k c).2]
    dsimp only [B,planeResonantCoefficient,C]
    module
  have hEC : planeEulerDerivative C-C=(4*k) • planeRadialSmooth := by
    change planeEulerDerivative (planeResonantCoefficient (4*k) (3*c)) -
      planeResonantCoefficient (4*k) (3*c) = _
    rw [(planeResonantCoefficient_derivatives (4*k) (3*c)).2]
    dsimp only [planeResonantCoefficient]
    module
  let K := ⁅L0 f h,Z⁆-(2 : ℝ) • L0 f h
  have hK : K= -(D f 1*D f 1)+multiplication B*D f 1+multiplication s :=
    planeResonant_K_exact f h k c h01 h02 h12
  have hJ : ⁅Z,K⁆=multiplication C*D f 1+multiplication t := by
    rw [hK,lie_add,lie_add,lie_neg,operator_lie_mul_right,hZD,
      operator_lie_mul_right,lie_planeCovariantEuler_multiplier,hZD,
      lie_planeCovariantEuler_multiplier]
    simp only [planeOperator_neg_mul,planeOperator_mul_neg,hDB,multiplication_mul]
    rw [← hC,multiplication_add,multiplication_smul,add_mul,smul_mul_assoc]
    dsimp only [t]
    rw [multiplication_sub]
    module
  have hA : ⁅Z,⁅Z,K⁆⁆-⁅Z,K⁆=
      firstOrder f ![0,(4*k) • planeRadialSmooth,0]
        (planeEulerDerivative t-smoothMul C B-t) := by
    rw [hJ,planeResonant_bracket_firstOrder f B C t hZD]
    have he : multiplication (planeEulerDerivative C)*D f 1-multiplication C*D f 1=
        multiplication ((4*k) • planeRadialSmooth)*D f 1 := by
      rw [← sub_mul,← multiplication_sub,hEC]
    simp only [firstOrder,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,multiplication_zero,
      zero_mul,zero_add,add_zero,multiplication_sub]
    rw [← he]
    abel
  have hL : L0 f h∈estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hZ : Z∈estimationAlgebra f h := planeCovariantEuler_mem f h hI hq
  have hKE : K∈estimationAlgebra f h := (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).lie_mem hL hZ) ((estimationAlgebra f h).smul_mem _ hL)
  refine ⟨planeEulerDerivative t-smoothMul C B-t,?_⟩
  rw [← hA]
  exact (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).lie_mem hZ ((estimationAlgebra f h).lie_mem hZ hKE))
    ((estimationAlgebra f h).lie_mem hZ hKE)

/-- The quadratic plane shear is excluded using the one actually admitted
D₀; the orthogonal swap keeps that derivative fixed. -/
theorem actual_plane_radial_transverse_shear_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD0 : D f 0∈estimationAlgebra f h) (b : ℝ) (s : Smooth)
    (hR : firstOrder f ![0,b • planeRadialSmooth,0] s∈estimationAlgebra f h) : b=0 := by
  let f' := coordinateDrift c2AxisSwap f
  let h' := coordinateObservations c2AxisSwap h
  let q' := smoothMul (linearFunction (coordinateVector 0)) (linearFunction (coordinateVector 0))+
    smoothMul (linearFunction (coordinateVector 1)) (linearFunction (coordinateVector 1))
  let a' : Fin 3 → Smooth := ![0,0,b • q']
  let s' := coordinatePullback c2AxisSwap s
  let _ : FiniteDimensional ℝ (estimationAlgebra f' h') :=
    finiteDimensional_coordinateEstimationAlgebra c2AxisSwap c2AxisSwap_orthogonal f h
  have hD' : D f' 0∈estimationAlgebra f' h' := by
    rw [← coordinateAlgebra_estimationAlgebra c2AxisSwap c2AxisSwap_orthogonal]
    refine ⟨D f 0,hD0,?_⟩
    change coordinateConjugation c2AxisSwap (D f 0)=D f' 0
    rw [coordinateConjugation_D,c2AxisSwap_vector_zero,directionD_coordinate]
  have ht : coordinatePullback c2AxisSwap hiddenShearTime=linearFunction (coordinateVector 1) := by
    apply Subtype.ext
    funext z
    simp [coordinatePullback_apply,c2AxisSwap,c2AxisSwapLinear,hiddenShearTime,
      linearFunction,coordinateVector,Fin.sum_univ_three]
  have hq : coordinatePullback c2AxisSwap planeRadialSmooth=q' := by
    rw [planeRadialSmooth,map_add,coordinatePullback_smoothMul,
      coordinatePullback_smoothMul,c2AxisSwap_x,ht]
  have he : coordinateConjugation c2AxisSwap (firstOrder f ![0,b • planeRadialSmooth,0] s)=
      firstOrder f' a' s' := by
    simp only [firstOrder,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,multiplication_zero,zero_mul,zero_add,add_zero,map_add,map_mul,
      coordinateConjugation_multiplication,coordinateConjugation_D,c2AxisSwap_vector_one,
      directionD_coordinate,map_smul,hq,a',s',f']
  have hR' : firstOrder f' a' s'∈estimationAlgebra f' h' := by
    rw [← coordinateAlgebra_estimationAlgebra c2AxisSwap c2AxisSwap_orthogonal]
    exact ⟨_,hR,he⟩
  have hz := actual_one_visible_quadratic_hidden_hessian_zero f' h' hD'
    (normalFirstOrder f' a' s') (normalFirstOrder_degree_le_one f' a' s')
    (by rwa [normalAction_normalFirstOrder]) a' (normalSymbol_one_normalFirstOrder f' a' s')
    0 0 (2*b) (by simp [a']) (by
      change partialDerivative 2 (b • q') = (0 : ℝ) • smoothOne
      simp only [q',map_smul,map_add,partialDerivative_smoothMul,
        partialDerivative_linearFunction]
      simp [coordinateVector,smoothMul_eq_mul]) (by
      change partialDerivative 0 (b • q') = hiddenAxisAffineCoefficient 0 (2*b) 0
      simp only [q',map_smul,map_add,partialDerivative_smoothMul,
        partialDerivative_linearFunction]
      apply Subtype.ext
      funext z
      simp [coordinateVector,hiddenAxisAffineCoefficient,linearFunction,smoothMul,
        smoothOne,Fin.sum_univ_three]
      ring)
  linarith

theorem plane_resonant_wong_slope_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD0 : D f 0∈estimationAlgebra f h)
    (hI : (1 : Operator)∈estimationAlgebra f h)
    (hq : multiplication planeRadialSmooth∈estimationAlgebra f h)
    (k c : ℝ)
    (h01 : wong f 0 1=k • linearFunction (coordinateVector 0)+c • smoothOne)
    (h02 : wong f 0 2=0)
    (h12 : wong f 1 2=(-k) • hiddenShearTime) : k=0 := by
  obtain ⟨s,hs⟩ := plane_resonant_quadratic_shear_member f h hI hq k c h01 h02 h12
  have hz := actual_plane_radial_transverse_shear_zero f h hD0 (4*k) s hs
  linarith

end Wong.SmoothModel

#print axioms Wong.SmoothModel.plane_resonant_quadratic_shear_member

#print axioms Wong.SmoothModel.actual_plane_radial_transverse_shear_zero
#print axioms Wong.SmoothModel.plane_resonant_wong_slope_zero

/-! Source segment: PlaneRadialWongRigidity.lean -/

/-! The complete B2 curvature conclusion. The two coefficient branches are
handled by an actual hidden-square extraction and a genuine resonant Lie
word, respectively. No hidden coordinate or hidden derivative is assumed
to belong to the estimation algebra. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Wong.SmoothModel
open MvPolynomial

theorem plane_radial_affine_wongConstant_and_mixed_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hq : multiplication (polynomialSmooth planeRadialPolynomial)∈estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀i j z,(wong f i j).1 z=p.matrix z i j) :
    WongConstant f ∧ wong f 0 2=0 ∧ wong f 1 2=0 := by
  obtain ⟨hk1,hk2,hh1,hh2⟩ := affine_diagonal_mixed_visible_slopes_zero f h hrank hx0 hx1 p hp
    (polynomialSmooth planeRadialPolynomial) hq ![1,0,1] (by norm_num) (by
      intro j
      rw [partialDerivative_polynomialSmooth]
      apply Subtype.ext
      funext z
      fin_cases j <;> simp [planeRadialPolynomial,polynomialSmooth,
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
  obtain ⟨hF,hG⟩ := plane_radial_curvature_members f h hrank hx0 hx1 hq
    p.b₀ p.b₁ p.b₂ p.k₃ p.h₃ p.k₀ p.h₀ h01 h02 h12
  obtain ⟨hk3,hk0⟩ := plane_radial_first_mixed_entry_zero f h hrank hx0 hx1 hq
    p.k₃ p.h₃ p.k₀ p.h₀ hF h02 h12
  obtain ⟨hb2,hh0⟩ := plane_radial_second_visible_slope_and_hidden_constant_zero
    f h hrank hx0 hx1 hq p.b₀ p.b₁ p.b₂ p.h₃ p.h₀ hG h01
  have hz02 : wong f 0 2=0 := by simpa [hk3,hk0] using h02
  have hI : (1 : Operator)∈estimationAlgebra f h := by
    simpa only [multiplication_smoothOne] using smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have hqS : polynomialSmooth planeRadialPolynomial=planeRadialSmooth := by
    simp [planeRadialPolynomial,planeRadialSmooth,pow_two,polynomialSmooth_add,
      polynomialSmooth_mul,polynomialSmooth_coordinate,hiddenShearTime]
  have hslopes : p.b₁=0 ∧ p.h₃=0 := by
    by_cases hsum : p.b₁+p.h₃=0
    · have hbh : p.h₃= -p.b₁ := by linarith
      have hc01 : wong f 0 1=p.b₁ • linearFunction (coordinateVector 0)+p.b₀ • smoothOne := by
        rw [h01]
        apply Subtype.ext
        funext z
        simp [polynomialSmooth,hb2,linearFunction,coordinateVector,smoothOne,
          Fin.sum_univ_three]
        ring
      have hc12 : wong f 1 2=(-p.b₁) • hiddenShearTime := by
        rw [h12]
        apply Subtype.ext
        funext z
        simp [polynomialSmooth,hh0,hbh,hiddenShearTime,linearFunction,coordinateVector,
          Fin.sum_univ_three]
      have hk := plane_resonant_wong_slope_zero f h
        (D_mem_of_coordinate_mem f h 0 hx0) hI (hqS ▸ hq) p.b₁ p.b₀ hc01 hz02 hc12
      exact ⟨hk,by simpa [hk] using hbh⟩
    · let S := actualPolynomialFunctionSpace (estimationAlgebra f h)
      have hx : (X 0 : RealPoly)∈S := by
        change multiplication (polynomialSmooth (X 0))∈estimationAlgebra f h
        rwa [polynomialSmooth_coordinate]
      have hG' : p.b₁ • (X 0^2 : RealPoly)-p.h₃ • (X 2^2 : RealPoly)∈S := by
        have he : planeCurvatureOne p.b₀ p.b₁ p.b₂ p.h₃ p.h₀-
            p.b₀ • (X 0 : RealPoly)=
            p.b₁ • (X 0^2 : RealPoly)-p.h₃ • (X 2^2 : RealPoly) := by
          simp [planeCurvatureOne,hb2,hh0,smul_eq_C_mul]
          ring
        rw [← he]
        exact S.sub_mem hG (S.smul_mem p.b₀ hx)
      have he : p.b₁ • planeRadialPolynomial-
          (p.b₁ • (X 0^2 : RealPoly)-p.h₃ • (X 2^2 : RealPoly))=
          (p.b₁+p.h₃) • (X 2^2 : RealPoly) := by
        simp [planeRadialPolynomial,smul_add,add_smul]
      have ht := S.sub_mem (S.smul_mem p.b₁ hq) hG'
      rw [he] at ht
      have ht' : (X 2^2 : RealPoly)∈S := by
        simpa only [smul_smul,inv_mul_cancel₀ hsum,one_smul] using
          S.smul_mem (p.b₁+p.h₃)⁻¹ ht
      have hhidden : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h := by
        change multiplication (polynomialSmooth (X 2^2))∈estimationAlgebra f h at ht'
        simpa [pow_two,polynomialSmooth_mul,polynomialSmooth_coordinate,hiddenShearTime,
          smoothMul_eq_mul] using ht'
      have hh := hidden_square_affine_mixed_slopes_zero f h hrank hx0 hx1 hhidden p hp
      have hvisible : (X 0^2 : RealPoly)∈S := by
        convert S.sub_mem hq ht' using 1
        simp [planeRadialPolynomial]
      have hvisible' : multiplication (smoothMul (linearFunction (coordinateVector 0))
          (linearFunction (coordinateVector 0)))∈estimationAlgebra f h := by
        change multiplication (polynomialSmooth (X 0^2))∈estimationAlgebra f h at hvisible
        simpa [pow_two,polynomialSmooth_mul,polynomialSmooth_coordinate] using hvisible
      have hv := coordinate_square_forces_affine_row_slopes_zero f h hrank hx0 hx1
        hvisible' p hp
      exact ⟨hv.1,hh.2.2.2.2.2⟩
  have hc01 : wong f 0 1=polynomialSmooth (C p.b₀) := by simpa [hslopes.1,hb2] using h01
  have hz12 : wong f 1 2=0 := by simpa [hslopes.2,hh0] using h12
  refine ⟨⟨fun i j => (wong f i j).1 (0 : State),?_⟩,hz02,hz12⟩
  intro i j z
  fin_cases i <;> fin_cases j
    <;> simp [wong_skew f 0 1,wong_skew f 0 2,wong_skew f 1 2,hc01,hz02,hz12,
      polynomialSmooth]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.plane_radial_affine_wongConstant_and_mixed_zero
