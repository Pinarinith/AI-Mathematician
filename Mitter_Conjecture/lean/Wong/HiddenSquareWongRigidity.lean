import Wong.C2Complete
import Wong.HiddenQuadraticShearRigidity
import Wong.DiagonalQuadraticCurvature

/-! The pure-hidden square case uses the abstract genuine C2 word with
coordinate index 2. In particular neither M(x₂) nor D₂ is assumed to lie in E. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open MvPolynomial

def coordinateWordUScalar {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3) : Smooth :=
  partialDerivative i (generatorRemainder f h i) +
    ∑ j, smoothMul (wong f i j) (wong f j i)

def coordinateWordVScalar {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3) (a : Fin 3 → ℝ) : Smooth :=
  partialDerivative i (coordinateWordUScalar f h i) +
    ∑ j, smoothMul (a j • smoothOne) (wong f j i)

def coordinateWordRScalar {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3) (a : Fin 3 → ℝ) : Smooth :=
  let x := linearFunction (coordinateVector i)
  smoothMul (smoothMul x x) (coordinateWordUScalar f h i) +
    (1/4 : ℝ) • smoothMul (smoothMul (smoothMul x x) x) (coordinateWordVScalar f h i a)

theorem c2R_firstOrder_coordinate {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3) (a : Fin 3 → ℝ) (hai : a i=0)
    (hrow : ∀j,partialDerivative i (wong f i j)=a j • smoothOne) :
    c2R (L0 f h) (multiplication (linearFunction (coordinateVector i))) =
      firstOrder f (fun j => a j • smoothMul (linearFunction (coordinateVector i))
        (linearFunction (coordinateVector i))) (coordinateWordRScalar f h i a) := by
  let x := linearFunction (coordinateVector i)
  let X := multiplication x
  let d := D f i
  let H := firstOrder f (wong f i) (generatorRemainder f h i)
  let U := firstOrder f (fun j => a j • smoothOne) (coordinateWordUScalar f h i)
  have hLX : ⁅L0 f h,X⁆=d :=
    (lie_L0_linearFunction f h (coordinateVector i)).trans (directionD_coordinate f i)
  have hDX : ⁅d,X⁆=1 := by
    simp [d,X,x,lie_D_multiplication,partialDerivative_linearFunction,coordinateVector]
  have hLD : ⁅L0 f h,d⁆=H := lie_L0_D_eq_firstOrder f h i
  have hHX : ⁅H,X⁆=0 := by
    change commuteWithMultiplier (linearFunction (coordinateVector i)) H=0
    rw [commuteWithLinear_firstOrder,coefficientAlong_coordinate,wong_self,multiplication_zero]
  have hDH : ⁅d,H⁆=U := by
    simp only [d,H,U,lie_D_firstOrder,hrow,coordinateWordUScalar]
  have hUX : ⁅U,X⁆=0 := by
    change commuteWithMultiplier (linearFunction (coordinateVector i)) U=0
    rw [commuteWithLinear_firstOrder,coefficientAlong_coordinate,hai,zero_smul,multiplication_zero]
  have hDU : ⁅d,U⁆=multiplication (coordinateWordVScalar f h i a) := by
    change ⁅D f i,firstOrder f (fun j => a j • smoothOne) (coordinateWordUScalar f h i)⁆=_
    rw [lie_D_firstOrder]
    simp only [partialDerivative_const,coordinateWordVScalar,
      firstOrder,multiplication_zero,zero_mul,Finset.sum_const_zero,zero_add]
  have he := c2R_exact (L0 f h) X d H U (multiplication (coordinateWordVScalar f h i a))
    hLX hDX hLD hHX hDH hUX hDU
  have hc (j : Fin 3) : smoothMul (smoothMul x x) (a j • smoothOne)=
      a j • smoothMul x x := by
    apply Subtype.ext
    funext z
    simp [smoothMul,smoothOne]
    ring
  rw [he]
  change multiplication x * multiplication x *
      firstOrder f (fun j => a j • smoothOne) (coordinateWordUScalar f h i) +
      (1/4 : ℝ) • (multiplication x * multiplication x * multiplication x *
        multiplication (coordinateWordVScalar f h i a)) = _
  rw [multiplication_mul,multiplication_firstOrder]
  simp only [multiplication_mul,hc,firstOrder,coordinateWordRScalar,
    multiplication_add,multiplication_smul]
  abel

/-- Actual admitted t² and affine hidden curvature rows force the entire
hidden row slope to vanish. This is the pure-hidden quadratic branch only. -/
theorem hidden_coordinate_square_forces_hidden_row_slopes_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hI : (1 : Operator)∈estimationAlgebra f h)
    (hsquare : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h)
    (a : Fin 3 → ℝ) (ha2 : a 2=0)
    (hrow : ∀j,partialDerivative 2 (wong f 2 j)=a j • smoothOne) :
    a 0=0 ∧ a 1=0 := by
  have hR : c2R (L0 f h) (multiplication hiddenShearTime)∈estimationAlgebra f h := by
    apply c2R_mem (estimationAlgebra f h) (L0 f h) (multiplication hiddenShearTime)
      (LieSubalgebra.subset_lieSpan (Or.inl rfl)) ?_ hI
    rw [multiplication_mul,smoothMul_eq_mul]
    exact hsquare
  rw [hiddenShearTime,c2R_firstOrder_coordinate f h 2 a ha2 hrow] at hR
  let av : Fin 3 → Smooth := fun j => a j • (hiddenShearTime*hiddenShearTime)
  let scalar := coordinateWordRScalar f h 2 a
  have hR' : normalAction (normalFirstOrder f av scalar)∈estimationAlgebra f h := by
    rw [normalAction_normalFirstOrder]
    exact hR
  have hs : normalSymbol 1 (normalFirstOrder f av scalar)=hiddenShearSymbol (a 0) (a 1) := by
    rw [normalSymbol_one_normalFirstOrder]
    simp only [principalVectorSymbol,Fin.sum_univ_three,av,ha2,zero_smul,
      map_zero,zero_mul,add_zero,shear_C_time_square,hiddenShearSymbol,hiddenShearMomentum]
    ring
  exact actual_hidden_quadratic_transverse_shear_zero f h
    (normalFirstOrder f av scalar) (normalFirstOrder_degree_le_one f av scalar) hR'
    (a 0) (a 1) hs

/-- Exact affine-parameter corollary of the true diagonal-function constraint. -/
theorem affine_diagonal_mixed_visible_slopes_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀i j z,(wong f i j).1 z=p.matrix z i j)
    (u : Smooth) (huE : multiplication u∈estimationAlgebra f h)
    (a : State) (ha : a 2≠0)
    (hu : ∀j,partialDerivative j u=(2*a j) • linearFunction (coordinateVector j)) :
    p.k₁=0 ∧ p.k₂=0 ∧ p.h₁=0 ∧ p.h₂=0 := by
  have hh := diagonal_quadratic_hidden_coefficient_forces_mixed_visible_partials_zero
    f h hrank hx₀ hx₁ u huE a ha hu
    (fun r s i j => VisibleHeads.partial_partial_wong_affine f p hp r s i j)
    (by simp [VisibleHeads.partial_wong_affine f p hp,VisibleHeads.slopes])
  have he (i k : Fin 3) (hi : i=0∨i=1) (hk : k=0∨k=1) :
      VisibleHeads.slopes p 2 i k=0 := by
    have hz := hh i k hi hk
    rw [VisibleHeads.partial_wong_affine f p hp] at hz
    have hv := congrArg (fun u : Smooth => u.1 (0 : State)) hz
    simpa [smoothOne] using hv
  have hk1 := he 0 0 (Or.inl rfl) (Or.inl rfl)
  have hk2 := he 0 1 (Or.inl rfl) (Or.inr rfl)
  have hh1 := he 1 0 (Or.inr rfl) (Or.inl rfl)
  have hh2 := he 1 1 (Or.inr rfl) (Or.inr rfl)
  simp only [VisibleHeads.slopes,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two] at hk1 hk2 hh1 hh2
  exact ⟨neg_eq_zero.mp hk1,neg_eq_zero.mp hk2,neg_eq_zero.mp hh1,neg_eq_zero.mp hh2⟩

/-- Pure t² membership eliminates every affine slope of both mixed Wong entries. -/
theorem hidden_square_affine_mixed_slopes_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hsquare : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀i j z,(wong f i j).1 z=p.matrix z i j) :
    p.k₁=0 ∧ p.k₂=0 ∧ p.k₃=0 ∧ p.h₁=0 ∧ p.h₂=0 ∧ p.h₃=0 := by
  have hI : (1 : Operator)∈estimationAlgebra f h := by
    simpa only [multiplication_smoothOne] using
      smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have hlast := hidden_coordinate_square_forces_hidden_row_slopes_zero f h hI hsquare
    ![-p.k₃,-p.h₃,0] (by simp) (by
      intro j
      rw [VisibleHeads.partial_wong_affine f p hp]
      fin_cases j <;> simp [VisibleHeads.slopes])
  have hfirst := affine_diagonal_mixed_visible_slopes_zero f h hrank hx₀ hx₁ p hp
    (hiddenShearTime*hiddenShearTime) hsquare ![0,0,1] (by norm_num) (by
      intro j
      rw [← smoothMul_eq_mul,partialDerivative_smoothMul,partial_hiddenShearTime]
      fin_cases j <;> simp [smoothMul_eq_mul,smoothOne_eq_one,hiddenShearTime,two_smul])
  exact ⟨hfirst.1,hfirst.2.1,neg_eq_zero.mp hlast.1,hfirst.2.2.1,
    hfirst.2.2.2,neg_eq_zero.mp hlast.2⟩

/-- The remaining constant mixed entries also vanish by the actual
curvature-gradient members and the original rank-two restriction. -/
theorem hidden_square_affine_mixed_entries_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hsquare : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h)
    (p : Wong.AffineParameters) (hp : ∀i j z,(wong f i j).1 z=p.matrix z i j) :
    wong f 0 2=0 ∧ wong f 1 2=0 := by
  obtain ⟨hk1,hk2,hk3,hh1,hh2,hh3⟩ :=
    hidden_square_affine_mixed_slopes_zero f h hrank hx₀ hx₁ hsquare p hp
  have hc02 : wong f 0 2=p.k₀ • smoothOne := by
    apply Subtype.ext
    funext z
    rw [hp]
    simp [Wong.AffineParameters.matrix,Wong.AffineParameters.w13,hk1,hk2,hk3,smoothOne]
  have hc12 : wong f 1 2=p.h₀ • smoothOne := by
    apply Subtype.ext
    funext z
    rw [hp]
    simp [Wong.AffineParameters.matrix,Wong.AffineParameters.w23,hh1,hh2,hh3,smoothOne]
  have hu (j : Fin 3) : partialDerivative j (hiddenShearTime*hiddenShearTime)=
      if j=2 then (2 : ℝ) • hiddenShearTime else 0 := by
    rw [← smoothMul_eq_mul,partialDerivative_smoothMul,partial_hiddenShearTime]
    split_ifs <;> simp [smoothMul_eq_mul,smoothOne_eq_one,two_smul]
  have hshape (i : Fin 3) (v : ℝ) (hi : wong f 2 i=(-v) • smoothOne) :
      functionCurvatureGradient f (hiddenShearTime*hiddenShearTime) i =
        linearFunction ![0,0,-2*v] := by
    simp only [functionCurvatureGradient,hu,Fin.sum_univ_three]
    simp only [show (0 : Fin 3)≠2 from by decide,show (1 : Fin 3)≠2 from by decide,
      ite_false,ite_true,smoothMul_eq_mul,zero_mul,zero_add,hi]
    apply Subtype.ext
    funext z
    simp [hiddenShearTime,linearFunction,coordinateVector,Fin.sum_univ_three,smoothOne]
    ring
  have hm0 := function_curvature_gradient_mem_of_adapted_rank_two f h hrank hx₀ hx₁
    (hiddenShearTime*hiddenShearTime) hsquare 0 (Or.inl rfl)
  have hm1 := function_curvature_gradient_mem_of_adapted_rank_two f h hrank hx₀ hx₁
    (hiddenShearTime*hiddenShearTime) hsquare 1 (Or.inr rfl)
  rw [hshape 0 p.k₀ (by rw [wong_skew f 0 2,hc02,neg_smul])] at hm0
  rw [hshape 1 p.h₀ (by rw [wong_skew f 1 2,hc12,neg_smul])] at hm1
  have hk0 := rank_two_adapted_coefficient_zero (estimationAlgebra f h) hrank hx₀ hx₁
    ![0,0,-2*p.k₀] hm0
  have hh0 := rank_two_adapted_coefficient_zero (estimationAlgebra f h) hrank hx₀ hx₁
    ![0,0,-2*p.h₀] hm1
  have hk : p.k₀=0 := by change -2*p.k₀=0 at hk0; linarith
  have hh : p.h₀=0 := by change -2*p.h₀=0 at hh0; linarith
  simpa [hk,hh] using And.intro hc02 hc12

/-- Hidden square membership supplies the true Euler word, without separately
admitting its coordinate multiplier or its covariant derivative. -/
theorem hiddenEuler_mem_of_hidden_square {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hI : (1 : Operator)∈estimationAlgebra f h)
    (hsquare : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h) :
    multiplication hiddenShearTime*D f 2∈estimationAlgebra f h := by
  have hLX : ⁅L0 f h,multiplication hiddenShearTime⁆=D f 2 :=
    (lie_L0_linearFunction f h (coordinateVector 2)).trans (directionD_coordinate f 2)
  have hDX : ⁅D f 2,multiplication hiddenShearTime⁆=1 := by
    simp [hiddenShearTime,lie_D_multiplication,partialDerivative_linearFunction,coordinateVector]
  rw [← c2Z_eq (L0 f h) (multiplication hiddenShearTime) (D f 2) hLX hDX]
  apply (estimationAlgebra f h).sub_mem
  · apply (estimationAlgebra f h).smul_mem
    apply (estimationAlgebra f h).lie_mem (LieSubalgebra.subset_lieSpan (Or.inl rfl))
    simpa only [multiplication_mul,smoothMul_eq_mul] using hsquare
  · exact (estimationAlgebra f h).smul_mem _ hI

/-- This is an equality of genuine operators with the full scalar retained. -/
theorem lie_L0_hiddenEuler_of_mixed_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (h02 : wong f 0 2=0) (h12 : wong f 1 2=0) :
    ⁅L0 f h,multiplication hiddenShearTime*D f 2⁆ =
      D f 2*D f 2+(1/2 : ℝ) • multiplication
        (smoothMul hiddenShearTime (partialDerivative 2 (eta f h))) := by
  have hrow (j : Fin 3) : wong f 2 j=0 := by
    fin_cases j
    · exact (wong_skew f 0 2).trans (by rw [h02,neg_zero])
    · exact (wong_skew f 1 2).trans (by rw [h12,neg_zero])
    · exact wong_self f 2
  have hLX : ⁅L0 f h,multiplication hiddenShearTime⁆=D f 2 :=
    (lie_L0_linearFunction f h (coordinateVector 2)).trans (directionD_coordinate f 2)
  rw [operator_lie_mul_right,hLX,lie_L0_D_eq_firstOrder]
  simp only [firstOrder,hrow,multiplication_zero,zero_mul,Finset.sum_const_zero,
    zero_add,generatorRemainder,hrow,map_zero,Finset.sum_const_zero,
    zero_add,multiplication_smul,mul_smul_comm,multiplication_mul]

/-- The pure-hidden Euler word extracts an actual visible two-dimensional
filtering operator. Its potential is the transported actual smooth scalar,
not a newly assumed polynomial or a recomputed filtering eta. -/
theorem visible_filtering_member_of_hidden_square_and_mixed_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hI : (1 : Operator)∈estimationAlgebra f h)
    (hsquare : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h)
    (h02 : wong f 0 2=0) (h12 : wong f 1 2=0) :
    (1/2 : ℝ) • (D f 0*D f 0+D f 1*D f 1) -
      (1/2 : ℝ) • multiplication (eta f h+(1/2 : ℝ) •
        smoothMul hiddenShearTime (partialDerivative 2 (eta f h)))∈estimationAlgebra f h := by
  have hL : L0 f h∈estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hZ := hiddenEuler_mem_of_hidden_square f h hI hsquare
  have hP := (estimationAlgebra f h).sub_mem hL
    ((estimationAlgebra f h).smul_mem (1/2 : ℝ) ((estimationAlgebra f h).lie_mem hL hZ))
  rw [lie_L0_hiddenEuler_of_mixed_zero f h h02 h12] at hP
  have he : L0 f h-(1/2 : ℝ) • (D f 2*D f 2+(1/2 : ℝ) •
      multiplication (smoothMul hiddenShearTime (partialDerivative 2 (eta f h)))) =
      (1/2 : ℝ) • (D f 0*D f 0+D f 1*D f 1) -
      (1/2 : ℝ) • multiplication (eta f h+(1/2 : ℝ) •
        smoothMul hiddenShearTime (partialDerivative 2 (eta f h))) := by
    simp only [L0,Fin.sum_univ_three,multiplication_add,multiplication_smul]
    module
  rwa [he] at hP

def hiddenEulerResolvent (u : Smooth) : Smooth :=
  smoothMul hiddenShearTime (partialDerivative 2
    (smoothMul hiddenShearTime (partialDerivative 2 u)+(2 : ℝ) • u))

/-- Twice the exact scalar Lie word equals E_t(E_t+2) eta. -/
theorem hidden_euler_eta_resolvent_word {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (h02 : wong f 0 2=0) (h12 : wong f 1 2=0) :
    (2 : ℝ) • ((2 : ℝ) • ⁅L0 f h,multiplication hiddenShearTime*D f 2⁆ -
      ⁅multiplication hiddenShearTime*D f 2,
        ⁅multiplication hiddenShearTime*D f 2,L0 f h⁆⁆) =
      multiplication (hiddenEulerResolvent (eta f h)) := by
  let Z := multiplication hiddenShearTime*D f 2
  let B := smoothMul hiddenShearTime (partialDerivative 2 (eta f h))
  have hMD : ⁅multiplication hiddenShearTime,D f 2⁆=-(1 : Operator) := by
    rw [← lie_skew,lie_D_multiplication,partial_hiddenShearTime]
    simp
  have hZD : ⁅Z,D f 2⁆= -D f 2 := by
    change ⁅multiplication hiddenShearTime*D f 2,D f 2⁆= _
    rw [operator_lie_mul_left,lie_self,hMD,mul_zero,zero_add]
    apply LinearMap.ext
    intro u
    rfl
  have hZDD : ⁅Z,D f 2*D f 2⁆=(-2 : ℝ) • (D f 2*D f 2) := by
    rw [operator_lie_mul_right,hZD]
    apply LinearMap.ext
    intro u
    change -(D f 2 (D f 2 u))+D f 2 (-(D f 2 u))=(-2 : ℝ) • (D f 2 (D f 2 u))
    rw [map_neg]
    module
  have hZM : ⁅Z,multiplication B⁆=multiplication (smoothMul hiddenShearTime (partialDerivative 2 B)) :=
    lie_covariant_monomial_multiplier f hiddenShearTime B 2
  have hLZ : ⁅L0 f h,Z⁆=D f 2*D f 2+(1/2 : ℝ) • multiplication B :=
    lie_L0_hiddenEuler_of_mixed_zero f h h02 h12
  have hZL : ⁅Z,L0 f h⁆=-(D f 2*D f 2+(1/2 : ℝ) • multiplication B) := by
    rw [← lie_skew,hLZ]
  have he : hiddenEulerResolvent (eta f h)=
      (2 : ℝ) • B+smoothMul hiddenShearTime (partialDerivative 2 B) := by
    simp only [hiddenEulerResolvent,map_add,map_smul,smoothMul_eq_mul,mul_add,mul_smul_comm,B]
    module
  change (2 : ℝ) • ((2 : ℝ) • ⁅L0 f h,Z⁆-⁅Z,⁅Z,L0 f h⁆⁆)=_
  rw [hZL,lie_neg,sub_neg_eq_add,lie_add,lie_smul,hZDD,hZM,hLZ,
    he,multiplication_add,multiplication_smul]
  module

theorem hidden_euler_eta_resolvent_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hI : (1 : Operator)∈estimationAlgebra f h)
    (hsquare : multiplication (hiddenShearTime*hiddenShearTime)∈estimationAlgebra f h)
    (h02 : wong f 0 2=0) (h12 : wong f 1 2=0) :
    multiplication (hiddenEulerResolvent (eta f h))∈estimationAlgebra f h := by
  have hL : L0 f h∈estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hZ := hiddenEuler_mem_of_hidden_square f h hI hsquare
  rw [← hidden_euler_eta_resolvent_word f h h02 h12]
  apply (estimationAlgebra f h).smul_mem
  exact (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).smul_mem _ ((estimationAlgebra f h).lie_mem hL hZ))
    ((estimationAlgebra f h).lie_mem hZ ((estimationAlgebra f h).lie_mem hZ hL))

/-- One admitted covariant derivative is enough to eliminate a quadratic
visible Hessian in a hidden coefficient. The other transverse derivative
is unrestricted: its contribution annihilates the chosen affine eigenfunction. -/
theorem actual_one_visible_quadratic_hidden_hessian_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD₀ : D f 0∈estimationAlgebra f h)
    (p : NormalForm) (hp : NormalDegreeLE 1 p)
    (hpE : normalAction p∈estimationAlgebra f h)
    (a : Fin 3 → Smooth) (hpa : normalSymbol 1 p=axisVectorSymbol a)
    (c e k : ℝ)
    (ha₀ : partialDerivative 2 (a 0)=0)
    (hg₂ : partialDerivative 2 (a 2)=c • smoothOne)
    (hg₀ : partialDerivative 0 (a 2)=hiddenAxisAffineCoefficient e k 0) : k=0 := by
  by_contra hk
  let K := normalBracket (normalL0 f h) p
  let A := normalBracket (normalD f 0) p
  have hl : NormalDegreeLE 2 (normalL0 f h) :=
    normalDegreeLE_of_action_order _ _ (by
      rw [normalAction_normalL0]; exact L0_mem_orderSpace_two f h)
  have hd : NormalDegreeLE 1 (normalD f 0) :=
    normalDegreeLE_of_action_order _ _ (by
      rw [normalAction_normalD]; exact D_mem_orderSpace_one f 0)
  have hK : NormalDegreeLE 2 K := by
    apply normalDegreeLE_of_action_order
    rw [normalAction_bracket,normalAction_normalL0]
    exact lie_mem_orderSpace_sharp (L0_mem_orderSpace_two f h)
      (action_order_of_normalDegreeLE p 1 hp)
  have hA : NormalDegreeLE 1 A := by
    apply normalDegreeLE_of_action_order
    rw [normalAction_bracket,normalAction_normalD]
    exact lie_mem_orderSpace_sharp (D_mem_orderSpace_one f 0)
      (action_order_of_normalDegreeLE p 1 hp)
  have hKE : normalAction K∈estimationAlgebra f h := by
    rw [normalAction_bracket,normalAction_normalL0]
    exact (estimationAlgebra f h).lie_mem (LieSubalgebra.subset_lieSpan (Or.inl rfl)) hpE
  have hAE : normalAction A∈estimationAlgebra f h := by
    rw [normalAction_bracket,normalAction_normalD]
    exact (estimationAlgebra f h).lie_mem hD₀ hpE
  have hKs : normalSymbol 2 K=symbolPoisson axisEuclideanKinetic (axisVectorSymbol a) := by
    rw [show 2=1+0+1 from rfl,normalSymbol_bracket _ _ 1 0 hl hp,
      normalSymbol_normalL0,hpa]
    rfl
  have hAs : normalSymbol 1 A=axisVectorSymbol (fun j => partialDerivative 0 (a j)) := by
    rw [show 1=0+0+1 from rfl,normalSymbol_bracket _ _ 0 0 hd hp,
      normalSymbol_normalD,hpa,poisson_X_axisVectorSymbol]
  have hu : hiddenAxisAffineCoefficient e k 0≠0 := by
    intro hz
    have he := congrArg (partialDerivative 0) hz
    rw [partial_hiddenAxisAffineCoefficient_zero,map_zero] at he
    have he0 := congrArg (fun u : Smooth => u.1 (0 : State)) he
    exact hk (by simpa [smoothOne] using he0)
  apply actual_hiddenAxis_eigen_ladder_obstruction (estimationAlgebra f h) K A 1 0
    (by decide) hKE hAE hK hA c k hk (hiddenAxisAffineCoefficient e k 0)
    (partialDerivative 1 (a 2)+partialDerivative 2 (a 1))
    (hiddenAxisAffineCoefficient e k 0) hu
  · rw [hKs,kinetic_axisVectorSymbol_project,hg₂]
  · simp only [hKs,kinetic_axisVectorSymbol_project_pderiv_zero,hg₀,ha₀,add_zero,pow_one]
  · simp only [hKs,kinetic_axisVectorSymbol_project_pderiv_one,pow_one]
  · simp only [hAs,axisVectorSymbol_project,hg₀,Nat.zero_add,pow_one]
  · exact partial_hiddenAxisAffineCoefficient_two e k 0
  · rw [partial_hiddenAxisAffineCoefficient_zero,partial_hiddenAxisAffineCoefficient_one]
    simp [smoothOne_eq_one,mul_smul_comm]

end Wong.SmoothModel

#print axioms Wong.SmoothModel.hidden_coordinate_square_forces_hidden_row_slopes_zero

#print axioms Wong.SmoothModel.actual_one_visible_quadratic_hidden_hessian_zero

#print axioms Wong.SmoothModel.hidden_square_affine_mixed_slopes_zero

#print axioms Wong.SmoothModel.visible_filtering_member_of_hidden_square_and_mixed_zero

#print axioms Wong.SmoothModel.hidden_square_affine_mixed_entries_zero

#print axioms Wong.SmoothModel.hidden_euler_eta_resolvent_mem
