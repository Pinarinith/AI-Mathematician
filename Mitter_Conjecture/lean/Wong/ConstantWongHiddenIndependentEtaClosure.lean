import Wong.C2Complete
import Wong.CoordinateCubicRiccati
import Wong.HiddenIndependentSectors
import Wong.VisibleGeneratorHeads
import Wong.SmoothPolynomialRegularity
import Wong.ConstantWongHiddenScalarRigidity
import Wong.ConstantWongQuadraticEtaClosure


/-! Genuine C2 scalar words force the first visible eta Hessian coefficient
to be constant. Both scalar functions used below are actual algebra members;
no division by a coordinate or local regular-singular assumption is made. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel

def c2ScalarWord (u : Smooth) : Smooth :=
  smoothMul c2Square u + (1 / 4 : ℝ) •
    smoothMul (smoothMul c2Square (linearFunction (coordinateVector 0))) (partialDerivative 0 u)

theorem c2ScalarWord_basis (c a b q : ℝ) :
    c2ScalarWord (c • smoothOne + a • linearFunction (coordinateVector 0) +
      b • linearFunction (coordinateVector 1) + q • c2Square) =
    c • c2Square + (5 / 4 * a) • smoothMul c2Square (linearFunction (coordinateVector 0)) +
      b • smoothMul c2Square (linearFunction (coordinateVector 1)) +
      (3 / 2 * q) • smoothMul c2Square c2Square := by
  simp only [c2ScalarWord, map_add, map_smul, partial_c2Square,
    partialDerivative_linearFunction, SectorTwo.partial_one]
  apply Subtype.ext
  funext z
  simp [c2Square, smoothMul, smoothOne, coordinateVector]
  ring

/-- The two true C2 members g and x0² g + x0³ g'/4 force g constant. -/
theorem c2ScalarWord_member_forces_constant
    (E : LieSubalgebra ℝ Operator) (hC2 : HiddenIndependent.C2FunctionSpace E)
    (u : Smooth) (hu : multiplication u ∈ E)
    (hR : multiplication (c2ScalarWord u) ∈ E) :
    ∃ c : ℝ, u = c • smoothOne := by
  obtain ⟨c, a, b, q, hshape⟩ := hC2.2 u hu
  obtain ⟨C, A, B, Q, hRshape⟩ := hC2.2 (c2ScalarWord u) hR
  change u = c • smoothOne + a • linearFunction (coordinateVector 0) +
    b • linearFunction (coordinateVector 1) + q • c2Square at hshape
  change c2ScalarWord u = C • smoothOne + A • linearFunction (coordinateVector 0) +
    B • linearFunction (coordinateVector 1) + Q • c2Square at hRshape
  rw [hshape, c2ScalarWord_basis] at hRshape
  have heval (x y : ℝ) :
      c*x^2 + (5/4*a)*x^3 + b*x^2*y + (3/2*q)*x^4 = C+A*x+B*y+Q*x^2 := by
    have hh := congrArg (fun v : Smooth => v.1 ![x,y,0]) hRshape
    simp [c2Square, smoothMul, smoothOne, linearFunction, coordinateVector,
      Fin.sum_univ_three] at hh
    nlinarith [hh]
  have h00 := heval 0 0
  have h01 := heval 0 1
  have h10 := heval 1 0
  have hn10 := heval (-1) 0
  have h20 := heval 2 0
  have hn20 := heval (-2) 0
  have h11 := heval 1 1
  norm_num at h00 h01 h10 hn10 h20 hn20 h11
  have ha : a = 0 := by linarith
  have hb : b = 0 := by linarith
  have hq : q = 0 := by linarith
  exact ⟨c, by simpa only [ha, hb, hq, zero_smul, add_zero] using hshape⟩

theorem c2_eta_zero_zero_constant {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hC2 : HiddenIndependent.C2FunctionSpace (estimationAlgebra f h))
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hW : WongConstant f) :
    ∃ c : ℝ, partialDerivative 0 (partialDerivative 0 (eta f h)) = c • smoothOne := by
  obtain ⟨Ω, hΩ⟩ := hW
  have hw (i j : Fin 3) : wong f i j = Ω i j • smoothOne := by
    apply Subtype.ext
    funext x
    simpa [smoothOne] using hΩ i j x
  have hwd (i j k : Fin 3) : partialDerivative k (wong f i j) = 0 := by
    rw [hw, partialDerivative_const]
  have hD := D_mem_of_coordinate_mem f h 0 hx0
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hI : (1 : Operator) ∈ estimationAlgebra f h := by
    simpa only [multiplication_smoothOne] using
      smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have hUeq : ⁅D f 0, ⁅L0 f h, D f 0⁆⁆ = multiplication (c2UScalar f h) := by
    rw [lie_L0_D_eq_firstOrder, lie_D_firstOrder]
    simp only [hwd, firstOrder, multiplication_zero, zero_mul,
      Finset.sum_const_zero, zero_add, c2UScalar]
  have hU : multiplication (c2UScalar f h) ∈ estimationAlgebra f h := by
    rw [← hUeq]
    exact (estimationAlgebra f h).lie_mem hD ((estimationAlgebra f h).lie_mem hL hD)
  have hR : c2R (L0 f h) (multiplication (linearFunction (coordinateVector 0))) ∈
      estimationAlgebra f h := by
    apply c2R_mem _ _ _ hL ?_ hI
    simpa only [multiplication_mul] using hC2.1
  have hRe : c2R (L0 f h) (multiplication (linearFunction (coordinateVector 0))) =
      multiplication (c2ScalarWord (c2UScalar f h)) := by
    rw [c2R_firstOrder f h (fun _ => 0) rfl (by intro j; simp only [hwd, zero_smul])]
    simp [firstOrder, c2RScalar, c2VScalar, c2ScalarWord, c2Square, smoothMul_eq_mul]
  rw [hRe] at hR
  obtain ⟨c, hc⟩ := c2ScalarWord_member_forces_constant _ hC2 _ hU hR
  let s : ℝ := ∑ j, Ω 0 j * Ω j 0
  have hUformula : c2UScalar f h =
      (1 / 2 : ℝ) • partialDerivative 0 (partialDerivative 0 (eta f h)) + s • smoothOne := by
    simp only [c2UScalar, generatorRemainder, map_smul, map_add, map_sum,
      hwd, map_zero, Finset.sum_const_zero, zero_add]
    congr 1
    apply Subtype.ext
    funext x
    simp [s, smoothMul, hw, smoothOne, Fin.sum_univ_three]
  refine ⟨2*(c-s), ?_⟩
  rw [hUformula] at hc
  apply Subtype.ext
  funext x
  have hv := congrArg (fun u : Smooth => u.1 x) hc
  simp [smoothOne] at hv ⊢
  linarith


/-- Exact scalar of the genuine second generator word for constant Wong. -/
theorem constantWong_D_L0_D {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (Ω : Fin 3 → Fin 3 → ℝ)
    (hw : ∀ i j, wong f i j = Ω i j • smoothOne) (i j : Fin 3) :
    ⁅D f i, ⁅L0 f h, D f j⁆⁆ = multiplication
      ((1/2 : ℝ) • partialDerivative i (partialDerivative j (eta f h)) +
        (∑ k, Ω j k * Ω k i) • smoothOne) := by
  have hd (a b k : Fin 3) : partialDerivative k (wong f a b) = 0 := by
    rw [hw, partialDerivative_const]
  have hs : (∑ k, smoothMul (wong f j k) (wong f k i)) =
      (∑ k, Ω j k * Ω k i) • smoothOne := by
    apply Subtype.ext
    funext x
    simp [hw, smoothMul, smoothOne, Fin.sum_univ_three]
  have hr : partialDerivative i (generatorRemainder f h j) =
      (1/2 : ℝ) • partialDerivative i (partialDerivative j (eta f h)) := by
    simp only [generatorRemainder, hd, Finset.sum_const_zero, zero_add, map_smul]
  rw [lie_L0_D_eq_firstOrder, lie_D_firstOrder]
  simp only [hd, firstOrder, multiplication_zero, zero_mul, Finset.sum_const_zero,
    zero_add, hr, hs]

theorem constantWong_eta_hessian_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (hW : WongConstant f)
    (hI : (1 : Operator) ∈ estimationAlgebra f h) (i j : Fin 3)
    (hi : D f i ∈ estimationAlgebra f h) (hj : D f j ∈ estimationAlgebra f h) :
    multiplication (partialDerivative i (partialDerivative j (eta f h))) ∈
      estimationAlgebra f h := by
  obtain ⟨Ω,hΩ⟩ := hW
  have hw (a b : Fin 3) : wong f a b = Ω a b • smoothOne := by
    apply Subtype.ext
    funext x
    simpa [smoothOne] using hΩ a b x
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hm := (estimationAlgebra f h).lie_mem hi ((estimationAlgebra f h).lie_mem hL hj)
  rw [constantWong_D_L0_D f h Ω hw] at hm
  simp only [multiplication_add, multiplication_smul, multiplication_smoothOne] at hm
  have hh := (estimationAlgebra f h).sub_mem hm
    ((estimationAlgebra f h).smul_mem (∑ k, Ω j k * Ω k i) hI)
  rw [add_sub_cancel_right] at hh
  have he := (estimationAlgebra f h).smul_mem (2 : ℝ) hh
  simpa only [smul_smul, show (2 : ℝ)*(1/2)=1 by norm_num, one_smul] using he


theorem c2_member_coordinate_product_constant
    (E : LieSubalgebra ℝ Operator) (hC2 : HiddenIndependent.C2FunctionSpace E)
    (u : Smooth) (hu : multiplication u ∈ E)
    (hprod : multiplication (smoothMul (linearFunction (coordinateVector 0)) u) ∈ E)
    (hu0 : partialDerivative 0 u=0) : ∃ c : ℝ, u=c•smoothOne := by
  have hx0 : partialDerivative 0 (linearFunction (coordinateVector 0))=smoothOne := by
    simp [partialDerivative_linearFunction,coordinateVector]
  have hx1 : partialDerivative 1 (linearFunction (coordinateVector 0))=0 := by
    simp [partialDerivative_linearFunction,coordinateVector]
  have hfirst : partialDerivative 1 (smoothMul (linearFunction (coordinateVector 0)) u)=
      smoothMul (linearFunction (coordinateVector 0)) (partialDerivative 1 u) := by
    rw [partialDerivative_smoothMul,hx1]
    simp [smoothMul_eq_mul]
  have hzero := c2_function_visible_mixed_zero E hC2 _ hprod
  rw [hfirst,partialDerivative_smoothMul,hx0,partialDerivative_commute_apply 0 1 u,
    hu0,map_zero] at hzero
  have hu1 : partialDerivative 1 u=0 := by
    simpa [smoothMul_eq_mul,smoothOne_eq_one] using hzero
  have hu2 := HiddenIndependent.c2_hiddenIndependent E hC2 u hu
  obtain ⟨c,hc⟩ := (smooth_constant_iff_partials_zero u).mpr (by
    intro i
    fin_cases i <;> assumption)
  refine ⟨c,?_⟩
  apply Subtype.ext
  funext x
  simpa [smoothOne] using hc x

theorem c2_eta_zero_one_constant {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hC2 : HiddenIndependent.C2FunctionSpace (estimationAlgebra f h))
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hW : WongConstant f) :
    ∃ c : ℝ, partialDerivative 0 (partialDerivative 1 (eta f h))=c•smoothOne := by
  obtain ⟨c00,h00⟩ := c2_eta_zero_zero_constant f h hrank hC2 hx0 hW
  obtain ⟨Ω,hΩ⟩ := hW
  have hw (i j : Fin 3) : wong f i j=Ω i j•smoothOne := by
    apply Subtype.ext
    funext x
    simpa [smoothOne] using hΩ i j x
  let s : ℝ := ∑ k, Ω 1 k*Ω k 0
  let u : Smooth := (1/2 : ℝ)•partialDerivative 0 (partialDerivative 1 (eta f h))+s•smoothOne
  have hD0 := D_mem_of_coordinate_mem f h 0 hx0
  have hD1 := D_mem_of_coordinate_mem f h 1 hx1
  have hL : L0 f h∈estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hI : (1 : Operator)∈estimationAlgebra f h := by
    simpa only [multiplication_smoothOne] using smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have hUeq : ⁅D f 0,⁅L0 f h,D f 1⁆⁆=multiplication u :=
    constantWong_D_L0_D f h Ω hw 0 1
  have hU : multiplication u∈estimationAlgebra f h := by
    rw [←hUeq]
    exact (estimationAlgebra f h).lie_mem hD0 ((estimationAlgebra f h).lie_mem hL hD1)
  let X := multiplication (linearFunction (coordinateVector 0))
  have hLX : ⁅L0 f h,X⁆=D f 0 :=
    (lie_L0_linearFunction f h (coordinateVector 0)).trans (directionD_coordinate f 0)
  have hDX : ⁅D f 0,X⁆=1 := by
    simp [X,lie_D_multiplication,partialDerivative_linearFunction,coordinateVector]
  have hZ : X*D f 0∈estimationAlgebra f h := by
    rw [←c2Z_eq (L0 f h) X (D f 0) hLX hDX]
    apply (estimationAlgebra f h).sub_mem
    · apply (estimationAlgebra f h).smul_mem
      apply (estimationAlgebra f h).lie_mem hL
      simpa only [X,multiplication_mul] using hC2.1
    · exact (estimationAlgebra f h).smul_mem _ hI
  have hHX : ⁅X,⁅L0 f h,D f 1⁆⁆=(-Ω 1 0)•(1 : Operator) := by
    rw [←lie_skew,lie_L0_D_eq_firstOrder]
    change -commuteWithMultiplier (linearFunction (coordinateVector 0))
      (firstOrder f (wong f 1) (generatorRemainder f h 1))=_
    rw [commuteWithLinear_firstOrder,coefficientAlong_coordinate,hw,
      multiplication_smul,multiplication_smoothOne,neg_smul]
  have hJeq : ⁅X*D f 0,⁅L0 f h,D f 1⁆⁆=
      multiplication (smoothMul (linearFunction (coordinateVector 0)) u)+(-Ω 1 0)•D f 0 := by
    rw [operator_lie_mul_left,hUeq,hHX,smul_mul_assoc,one_mul]
    exact congrArg (fun A : Operator => A+(-Ω 1 0)•D f 0)
      (multiplication_mul _ _)
  have hJ := (estimationAlgebra f h).lie_mem hZ ((estimationAlgebra f h).lie_mem hL hD1)
  rw [hJeq] at hJ
  have hprod := (estimationAlgebra f h).sub_mem hJ
    ((estimationAlgebra f h).smul_mem (-Ω 1 0) hD0)
  rw [add_sub_cancel_right] at hprod
  have hu0 : partialDerivative 0 u=0 := by
    simp only [u,map_add,map_smul,SectorTwo.partial_one,smul_zero,add_zero]
    rw [partialDerivative_commute_apply 0 1 (eta f h),
      partialDerivative_commute_apply 0 1 (partialDerivative 0 (eta f h)),
      h00,partialDerivative_const,smul_zero]
  obtain ⟨c,hc⟩ := c2_member_coordinate_product_constant _ hC2 u hU hprod hu0
  refine ⟨2*(c-s),?_⟩
  apply Subtype.ext
  funext x
  have hh := congrArg (fun v : Smooth => v.1 x) hc
  simp [u,smoothOne] at hh ⊢
  linarith

theorem c2_function_one_second_zero (E : LieSubalgebra ℝ Operator)
    (hC2 : HiddenIndependent.C2FunctionSpace E) (u : Smooth) (hu : multiplication u∈E) :
    partialDerivative 1 (partialDerivative 1 u)=0 := by
  obtain ⟨c,a,b,q,rfl⟩ := hC2.2 u hu
  simp only [map_add,map_smul,partialDerivative_smoothMul,
    partialDerivative_linearFunction,SectorTwo.partial_one]
  simp [coordinateVector,smoothMul_eq_mul]

theorem c2_eta_one_one_constant {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hC2 : HiddenIndependent.C2FunctionSpace (estimationAlgebra f h))
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hW : WongConstant f) :
    ∃ c : ℝ, partialDerivative 1 (partialDerivative 1 (eta f h))=c•smoothOne := by
  obtain ⟨c01,h01⟩ := c2_eta_zero_one_constant f h hrank hC2 hx0 hx1 hW
  have hI : (1 : Operator)∈estimationAlgebra f h := by
    simpa only [multiplication_smoothOne] using smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have hD1 := D_mem_of_coordinate_mem f h 1 hx1
  have hu := constantWong_eta_hessian_member f h hW hI 1 1 hD1 hD1
  obtain ⟨c,a,b,q,hshape⟩ := hC2.2 _ hu
  have hthird : partialDerivative 1 (partialDerivative 1 (partialDerivative 1 (eta f h)))=
      b•smoothOne := by
    rw [hshape]
    simp only [map_add,map_smul,partialDerivative_smoothMul,
      partialDerivative_linearFunction,SectorTwo.partial_one]
    simp [coordinateVector,smoothMul_eq_mul]
  have hb : b=0 := eta_constant_third_directional_zero_of_observation_second_zero
    f h (coordinateVector 1) b (by
      simpa only [coordinate_directionalDerivative,pow_succ,pow_one,pow_zero,Module.End.mul_apply,Module.End.one_apply]
        using hthird) (by
      intro j
      simpa only [coordinate_directionalDerivative,pow_succ,pow_one,pow_zero,Module.End.mul_apply,Module.End.one_apply] using
        c2_function_one_second_zero _ hC2 (h j)
          (LieSubalgebra.subset_lieSpan (Or.inr ⟨j,rfl⟩)))
  have hzero1 : partialDerivative 1 (partialDerivative 1 (partialDerivative 1 (eta f h)))=0 := by
    simpa only [hb,zero_smul] using hthird
  have hzero0 : partialDerivative 0 (partialDerivative 1 (partialDerivative 1 (eta f h)))=0 := by
    rw [partialDerivative_commute_apply 0 1 (partialDerivative 1 (eta f h)),h01,
      partialDerivative_const]
  have hzero2 := HiddenIndependent.c2_hiddenIndependent _ hC2 _ hu
  obtain ⟨d,hd⟩ := (smooth_constant_iff_partials_zero
    (partialDerivative 1 (partialDerivative 1 (eta f h)))).mpr (by
    intro i
    fin_cases i <;> assumption)
  refine ⟨d,?_⟩
  apply Subtype.ext
  funext x
  simpa [smoothOne] using hd x


def visibleEtaQuadratic (a b c : ℝ) : Smooth :=
  (a/2)•smoothMul (linearFunction (coordinateVector 0)) (linearFunction (coordinateVector 0)) +
    b•smoothMul (linearFunction (coordinateVector 0)) (linearFunction (coordinateVector 1)) +
    (c/2)•smoothMul (linearFunction (coordinateVector 1)) (linearFunction (coordinateVector 1))

theorem visibleEtaQuadratic_partial (a b c : ℝ) (i : Fin 3) :
    partialDerivative i (visibleEtaQuadratic a b c) =
      if i=0 then a•linearFunction (coordinateVector 0)+b•linearFunction (coordinateVector 1)
      else if i=1 then b•linearFunction (coordinateVector 0)+c•linearFunction (coordinateVector 1)
      else 0 := by
  fin_cases i <;>
    simp only [visibleEtaQuadratic,map_add,map_smul,partialDerivative_smoothMul,
      partialDerivative_linearFunction] <;>
    apply Subtype.ext <;> funext x <;>
    simp [coordinateVector,smoothMul,smoothOne] <;> ring

/-- An exact smooth profile from constant visible Hessian. The linear visible
coefficients remain arbitrary smooth hidden functions at this stage. -/
theorem visible_profile_of_constant_hessian (u : Smooth) (a b c : ℝ)
    (h00 : partialDerivative 0 (partialDerivative 0 u)=a•smoothOne)
    (h01 : partialDerivative 0 (partialDerivative 1 u)=b•smoothOne)
    (h11 : partialDerivative 1 (partialDerivative 1 u)=c•smoothOne) :
    ∃ φ0 φ1 φ2 : Smooth,
      (∀ i : Fin 3, i=0 ∨ i=1 →
        partialDerivative i φ0=0 ∧ partialDerivative i φ1=0 ∧ partialDerivative i φ2=0) ∧
      u=visibleEtaQuadratic a b c +
        smoothMul (linearFunction (coordinateVector 0)) φ1 +
        smoothMul (linearFunction (coordinateVector 1)) φ2 + φ0 := by
  let w := u-visibleEtaQuadratic a b c
  have hw00 : partialDerivative 0 (partialDerivative 0 w)=0 := by
    simp [w,map_sub,visibleEtaQuadratic_partial,map_add,map_smul,
      partialDerivative_linearFunction,coordinateVector,h00]
  have hw01 : partialDerivative 0 (partialDerivative 1 w)=0 := by
    simp [w,map_sub,visibleEtaQuadratic_partial,map_add,map_smul,
      partialDerivative_linearFunction,coordinateVector,h01]
  have hw11 : partialDerivative 1 (partialDerivative 1 w)=0 := by
    simp [w,map_sub,visibleEtaQuadratic_partial,map_add,map_smul,
      partialDerivative_linearFunction,coordinateVector,h11]
  have hw10 : partialDerivative 1 (partialDerivative 0 w)=0 := by
    rw [partialDerivative_commute_apply]
    exact hw01
  let φ1 := partialDerivative 0 w
  let φ2 := partialDerivative 1 w
  let φ0 := w-smoothMul (linearFunction (coordinateVector 0)) φ1-
    smoothMul (linearFunction (coordinateVector 1)) φ2
  refine ⟨φ0,φ1,φ2,?_,?_⟩
  · intro i hi
    rcases hi with rfl | rfl
    · refine ⟨?_,hw00,hw01⟩
      dsimp only [φ0,φ1,φ2]
      simp only [map_sub,partialDerivative_smoothMul,partialDerivative_linearFunction,
        hw00,hw01]
      simp [coordinateVector,smoothMul_eq_mul,smoothOne_eq_one]
    · refine ⟨?_,hw10,hw11⟩
      dsimp only [φ0,φ1,φ2]
      simp only [map_sub,partialDerivative_smoothMul,partialDerivative_linearFunction,
        hw10,hw11]
      simp [coordinateVector,smoothMul_eq_mul,smoothOne_eq_one]
  · dsimp only [φ0,w]
    abel

theorem c2_eta_actual_profile {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hC2 : HiddenIndependent.C2FunctionSpace (estimationAlgebra f h))
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hW : WongConstant f) :
    ∃ (a b c : ℝ) (φ0 φ1 φ2 : Smooth),
      (∀ i : Fin 3, i=0 ∨ i=1 →
        partialDerivative i φ0=0 ∧ partialDerivative i φ1=0 ∧ partialDerivative i φ2=0) ∧
      eta f h=visibleEtaQuadratic a b c +
        smoothMul (linearFunction (coordinateVector 0)) φ1 +
        smoothMul (linearFunction (coordinateVector 1)) φ2 + φ0 := by
  obtain ⟨a,ha⟩ := c2_eta_zero_zero_constant f h hrank hC2 hx0 hW
  obtain ⟨b,hb⟩ := c2_eta_zero_one_constant f h hrank hC2 hx0 hx1 hW
  obtain ⟨c,hc⟩ := c2_eta_one_one_constant f h hrank hC2 hx0 hx1 hW
  obtain ⟨φ0,φ1,φ2,hφ,he⟩ := visible_profile_of_constant_hessian (eta f h) a b c ha hb hc
  exact ⟨a,b,c,φ0,φ1,φ2,hφ,he⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.c2ScalarWord_member_forces_constant
#print axioms Wong.SmoothModel.c2_eta_zero_zero_constant
#print axioms Wong.SmoothModel.constantWong_eta_hessian_member
#print axioms Wong.SmoothModel.c2_eta_zero_one_constant
#print axioms Wong.SmoothModel.c2_eta_one_one_constant

#print axioms Wong.SmoothModel.c2_eta_actual_profile


/-! Actual mixed-curvature scalar words and a pure hidden second-order head.
The hidden coordinate multiplier need not belong to the estimation algebra. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Wong.SmoothModel
open VisibleHeads

def hiddenProfileFirst (f : Fin 3 → Smooth) (α : ℝ) (φ : Smooth) : Operator :=
  α • D f 2 + (1/2 : ℝ) • multiplication φ

def hiddenProfileSecond (f : Fin 3 → Smooth) (α : ℝ) (φ q : Smooth) : Operator :=
  multiplication (partialDerivative 2 φ) * D f 2 + α • multiplication q

theorem hiddenProfile_scalar_word (f : Fin 3 → Smooth) (α a : ℝ) (φ q : Smooth)
    (hφ : partialDerivative 2 (partialDerivative 2 φ)=a•smoothOne) :
    ⁅hiddenProfileFirst f α φ, hiddenProfileSecond f α φ q⁆ -
      a • hiddenProfileFirst f α φ = multiplication
        (α^2 • partialDerivative 2 q - (1/2 : ℝ) •
          smoothMul (partialDerivative 2 φ) (partialDerivative 2 φ) - (a/2) • φ) := by
  have hsk : ⁅multiplication φ,D f 2⁆ = -multiplication (partialDerivative 2 φ) := by
    rw [← lie_skew,lie_D_multiplication]
  simp only [hiddenProfileFirst,hiddenProfileSecond,add_lie,lie_add,smul_lie,lie_smul,
    operator_lie_mul_right,lie_D_multiplication,lie_self,
    lie_multiplication_multiplication,hsk,hφ,multiplication_smul,
    multiplication_smoothOne,mul_zero,zero_mul,zero_add,add_zero,smul_zero]
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.neg_apply,Module.End.mul_apply,Module.End.one_apply,
    multiplication_apply,smoothMul_apply,Submodule.coe_add,Submodule.coe_sub,
    Submodule.coe_smul,Submodule.coe_neg,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
    Pi.neg_apply,smul_eq_mul]
  ring

theorem hiddenProfile_second_heat_order_two {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (α a e : ℝ) (φ q : Smooth)
    (hφ : partialDerivative 2 φ=e•smoothOne+a•linearFunction (coordinateVector 2)) :
    ⁅L0 f h,⁅L0 f h,hiddenProfileSecond f α φ q⁆⁆ ∈ orderSpace 2 := by
  let A : Fin 3 → Smooth := fun j => if j=2 then partialDerivative 2 φ else 0
  let S : Fin 3 → State := fun j k => if j=2 ∧ k=2 then a else 0
  have he : hiddenProfileSecond f α φ q=firstOrder f A (α•q) := by
    simp [hiddenProfileSecond,firstOrder,A,Fin.sum_univ_three,multiplication_smul]
  have ha (j k : Fin 3) : partialDerivative k (A j)=S j k•smoothOne := by
    fin_cases j <;> fin_cases k <;>
      simp [A,S,hφ,map_add,map_smul,partialDerivative_const,
        partialDerivative_linearFunction,coordinateVector,SectorTwo.partial_one]
  rw [he,lie_L0_firstOrder_decomposition f h A (α•q) S ha,lie_add]
  exact (orderSpace 2).add_mem
    (lie_L0_constantSecondPart_mem_orderSpace_two f h S)
    (lie_L0_mem_orderSpace f h (lowerPart_mem_orderSpace_one f h A (α•q)))

theorem hiddenProfile_second_heat_head {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (α a e : ℝ) (φ q : Smooth)
    (hφ : partialDerivative 2 φ=e•smoothOne+a•linearFunction (coordinateVector 2)) :
    δ 2 (δ 2 ⁅L0 f h,⁅L0 f h,hiddenProfileSecond f α φ q⁆⁆) =
      (2*α) • multiplication (partialDerivative 2 (partialDerivative 2 q)) := by
  have hpd (i : Fin 3) : partialDerivative i (partialDerivative 2 φ)=
      (if i=2 then a else 0)•smoothOne := by
    fin_cases i <;> simp [hφ,map_add,map_smul,partialDerivative_const,
      partialDerivative_linearFunction,coordinateVector,SectorTwo.partial_one]
  have hself : partialDerivative 2 (partialDerivative 2 φ)=a•smoothOne := by
    simpa only [ite_true] using hpd 2
  have hd : δ 2 (hiddenProfileSecond f α φ q)=multiplication (partialDerivative 2 φ) := by
    change ⁅hiddenProfileSecond f α φ q, multiplication
      (linearFunction (coordinateVector 2))⁆ = _
    simp only [hiddenProfileSecond,add_lie,smul_lie,operator_lie_mul_left,
      lie_multiplication_multiplication,lie_D_multiplication,
      partialDerivative_linearFunction]
    simp [coordinateVector,multiplication_smoothOne]
  have hL : ⁅L0 f h,multiplication (partialDerivative 2 φ)⁆=a•D f 2 := by
    rw [lie_L0_multiplication_affine f h _ (fun i => if i=2 then a else 0) hpd]
    simp [Fin.sum_univ_three]
  have hD : ⁅D f 2,hiddenProfileSecond f α φ q⁆=
      a•D f 2+α•multiplication (partialDerivative 2 q) := by
    simp only [hiddenProfileSecond,lie_add,lie_smul,operator_lie_mul_right,
      lie_D_multiplication,lie_self,hself,multiplication_smul,multiplication_smoothOne,
      one_mul,smul_mul_assoc,mul_zero,add_zero]
  have hK : δ 2 ⁅L0 f h,hiddenProfileSecond f α φ q⁆=
      (2*a)•D f 2+α•multiplication (partialDerivative 2 q) := by
    rw [δ_lie_L0,hd,hL,hD]
    module
  have hKK : δ 2 (δ 2 ⁅L0 f h,hiddenProfileSecond f α φ q⁆)=
      (2*a)•(1:Operator) := by
    simp [hK,δ_D,coordinateVector]
  rw [δ_lie_L0,map_add,δ_lie_L0,δ_lie_D,hKK,lie_scalar_identity,zero_add,hK]
  simp only [lie_add,lie_smul,lie_self,lie_D_multiplication,smul_zero,zero_add]
  module

/-- Two genuine algebra-member profile words, together with actual hidden
independence of every function member, force the quadratic hidden tail to
vanish. No hidden derivative or hidden coordinate membership is assumed. -/
theorem hiddenProfile_quadratic_tail_zero {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (α a e : ℝ) (hα : α≠0) (φ q : Smooth)
    (hφ : partialDerivative 2 φ=e•smoothOne+a•linearFunction (coordinateVector 2))
    (hN1 : hiddenProfileFirst f α φ ∈ estimationAlgebra f h)
    (hN2 : hiddenProfileSecond f α φ q ∈ estimationAlgebra f h) :
    a=0 ∧ partialDerivative 2 (partialDerivative 2 q)=0 := by
  have hφ2 : partialDerivative 2 (partialDerivative 2 φ)=a•smoothOne := by
    simp [hφ,map_add,map_smul,partialDerivative_const,
      partialDerivative_linearFunction,coordinateVector,SectorTwo.partial_one]
  have hmem := (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).lie_mem hN1 hN2)
    ((estimationAlgebra f h).smul_mem a hN1)
  rw [hiddenProfile_scalar_word f α a φ q hφ2] at hmem
  have hz := hHF _ hmem
  have hrel : α^2 • partialDerivative 2 (partialDerivative 2 q)=
      (3*a/2)•partialDerivative 2 φ := by
    simp only [map_sub,map_smul,partialDerivative_smoothMul,hφ2] at hz
    apply Subtype.ext
    funext x
    have he := congrArg (fun z : Smooth => z.1 x) hz
    simp [smoothMul,smoothOne] at he ⊢
    linarith
  let C : Operator := ⁅L0 f h,⁅L0 f h,hiddenProfileSecond f α φ q⁆⁆
  have hL : L0 f h ∈ estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hC : C ∈ estimationAlgebra f h :=
    (estimationAlgebra f h).lie_mem hL ((estimationAlgebra f h).lie_mem hL hN2)
  have hhead : (commuteWithMultiplier (linearFunction (coordinateVector 2))^2) C =
      (2*(3*a*a/(2*α))) • multiplication (linearFunction (coordinateVector 2))+
        (3*a*e/α)•(1:Operator) := by
    change δ 2 (δ 2 C)=_
    rw [hiddenProfile_second_heat_head f h α a e φ q hφ]
    rw [← multiplication_smul,← multiplication_smoothOne,← multiplication_smul,
      ← multiplication_smul,← multiplication_add]
    apply congrArg multiplication
    apply Subtype.ext
    funext x
    have hr := congrArg (fun z : Smooth => z.1 x) hrel
    rw [hφ] at hr
    simp [smoothOne,linearFunction,coordinateVector] at hr ⊢
    field_simp [hα]
    nlinarith [hr]
  have hs := pure_head_slope_zero f h 2 C hC
    (hiddenProfile_second_heat_order_two f h α a e φ q hφ)
    (3*a*a/(2*α)) (3*a*e/α) hhead
  have ha : a=0 := by
    have he := (div_eq_zero_iff).mp hs
    rcases he with he | he
    · nlinarith [sq_nonneg a]
    · exact False.elim (hα (by linarith))
  refine ⟨ha,?_⟩
  simp only [ha,mul_zero,zero_div,zero_smul] at hrel
  exact (smul_eq_zero.mp hrel).resolve_left (pow_ne_zero 2 hα)

end Wong.SmoothModel
#print axioms Wong.SmoothModel.hiddenProfile_quadratic_tail_zero


/-! Genuine six/eight-generator closure from constant Wong, whole hidden
independence of function elements, and constant visible eta Hessians. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Wong.SmoothModel
open MvPolynomial

def etaVisibleProfile {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3) (c0 c1 : ℝ) : Smooth :=
  partialDerivative i (eta f h)-c0•linearFunction (coordinateVector 0)-
    c1•linearFunction (coordinateVector 1)

theorem etaVisibleProfile_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (Ω : Fin 3 → Fin 3 → ℝ)
    (hw : ∀i j, wong f i j=Ω i j•smoothOne)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (i : Fin 3) (hi : i=0 ∨ i=1) (c0 c1 : ℝ) :
    hiddenProfileFirst f (Ω i 2) (etaVisibleProfile f h i c0 c1)∈estimationAlgebra f h := by
  have hD0 := D_mem_of_coordinate_mem f h 0 hx0
  have hD1 := D_mem_of_coordinate_mem f h 1 hx1
  have hDi : D f i∈estimationAlgebra f h := by rcases hi with rfl|rfl <;> assumption
  have hL : L0 f h∈estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hrem : generatorRemainder f h i=(1/2:ℝ)•partialDerivative i (eta f h) := by
    simp only [generatorRemainder,hw,partialDerivative_const,Finset.sum_const_zero,zero_add]
  have he : hiddenProfileFirst f (Ω i 2) (etaVisibleProfile f h i c0 c1)=
      ⁅L0 f h,D f i⁆-(Ω i 0•D f 0+Ω i 1•D f 1)-
        (1/2:ℝ)•(c0•multiplication (linearFunction (coordinateVector 0))+
          c1•multiplication (linearFunction (coordinateVector 1))) := by
    rw [lie_L0_D,hrem]
    simp only [Fin.sum_univ_three,hw,multiplication_smul,multiplication_smoothOne,
      smul_mul_assoc,one_mul,hiddenProfileFirst,etaVisibleProfile,
      multiplication_sub,multiplication_smul]
    module
  rw [he]
  exact (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).sub_mem ((estimationAlgebra f h).lie_mem hL hDi)
      ((estimationAlgebra f h).add_mem ((estimationAlgebra f h).smul_mem _ hD0)
        ((estimationAlgebra f h).smul_mem _ hD1)))
    ((estimationAlgebra f h).smul_mem _ ((estimationAlgebra f h).add_mem
      ((estimationAlgebra f h).smul_mem _ hx0) ((estimationAlgebra f h).smul_mem _ hx1)))

theorem hiddenProfileSecond_mem_of_first {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (Ω : Fin 3 → Fin 3 → ℝ)
    (hw : ∀i j, wong f i j=Ω i j•smoothOne)
    (hD0 : D f 0∈estimationAlgebra f h) (hD1 : D f 1∈estimationAlgebra f h)
    (hI : (1:Operator)∈estimationAlgebra f h)
    (α a : ℝ) (φ : Smooth) (hφ0 : partialDerivative 0 φ=0)
    (hφ1 : partialDerivative 1 φ=0) (hφ2 : partialDerivative 2 (partialDerivative 2 φ)=a•smoothOne)
    (hN1 : hiddenProfileFirst f α φ∈estimationAlgebra f h) :
    hiddenProfileSecond f α φ (partialDerivative 2 (eta f h))∈estimationAlgebra f h := by
  have hΩ22 : Ω 2 2=0 := by
    have hz := hw 2 2
    rw [wong_self] at hz
    have he := congrArg (fun u : Smooth => u.1 (0:State)) hz
    simpa [smoothOne] using he.symm
  have hrem : generatorRemainder f h 2=(1/2:ℝ)•partialDerivative 2 (eta f h) := by
    simp only [generatorRemainder,hw,partialDerivative_const,Finset.sum_const_zero,zero_add]
  have hLM : ⁅L0 f h,multiplication φ⁆=
      multiplication (partialDerivative 2 φ)*D f 2+(a/2)•(1:Operator) := by
    rw [lie_L0_multiplication]
    simp only [Fin.sum_univ_three,hφ0,hφ1,map_zero,hφ2,multiplication_zero,
      zero_mul,zero_add,multiplication_smul,multiplication_smoothOne,smul_smul]
    congr 1
    ring
  have he : hiddenProfileSecond f α φ (partialDerivative 2 (eta f h))=
      (2:ℝ)•⁅L0 f h,hiddenProfileFirst f α φ⁆-
        (2*α)•(Ω 2 0•D f 0+Ω 2 1•D f 1)-(a/2)•(1:Operator) := by
    simp only [hiddenProfileFirst,lie_add,lie_smul,hLM,lie_L0_D,hrem,
      Fin.sum_univ_three,hw,multiplication_smul,multiplication_smoothOne,
      smul_mul_assoc,one_mul,hΩ22,zero_smul,add_zero,hiddenProfileSecond]
    module
  have hL : L0 f h∈estimationAlgebra f h := LieSubalgebra.subset_lieSpan (Or.inl rfl)
  rw [he]
  exact (estimationAlgebra f h).sub_mem
    ((estimationAlgebra f h).sub_mem
      ((estimationAlgebra f h).smul_mem _ ((estimationAlgebra f h).lie_mem hL hN1))
      ((estimationAlgebra f h).smul_mem _ ((estimationAlgebra f h).add_mem
        ((estimationAlgebra f h).smul_mem _ hD0) ((estimationAlgebra f h).smul_mem _ hD1))))
    ((estimationAlgebra f h).smul_mem _ hI)

theorem quadratic_hidden_profile_derivative_affine (φ : Smooth)
    (hφ0 : partialDerivative 0 φ=0) (hφ1 : partialDerivative 1 φ=0)
    (p : RealPoly) (hp : p.totalDegree≤2) (he : polynomialSmooth p=φ) :
    ∃a e : ℝ, partialDerivative 2 φ=e•smoothOne+a•linearFunction (coordinateVector 2) := by
  let a := (partialDerivative 2 (partialDerivative 2 φ)).1 0
  have hsecond : partialDerivative 2 (partialDerivative 2 φ)=a•smoothOne := by
    apply smooth_eq_constant_of_partials_zero
    intro i
    rw [←he]
    exact smooth_polynomial_third_partials_zero p hp i 2 2
  have hgrad (i : Fin 3) : partialDerivative i (partialDerivative 2 φ)=
      (![0,0,a] : State) i•smoothOne := by
    fin_cases i
    · change partialDerivative 0 (partialDerivative 2 φ) = 0 • smoothOne
      rw [partialDerivative_commute_apply,hφ0,map_zero,zero_smul]
    · change partialDerivative 1 (partialDerivative 2 φ) = 0 • smoothOne
      rw [partialDerivative_commute_apply,hφ1,map_zero,zero_smul]
    · exact hsecond
  refine ⟨a,(partialDerivative 2 φ).1 0,?_⟩
  calc
    _ = (partialDerivative 2 φ).1 0 • smoothOne + linearFunction ![0,0,a] :=
      smooth_affine_of_constant_partials _ ![0,0,a] hgrad
    _ = _ := by
      congr 1
      apply Subtype.ext
      funext x
      simp [linearFunction,coordinateVector,Fin.sum_univ_three]

/-- One nonzero constant mixed curvature forces the entire genuine eta
quadratic. Neither a hidden derivative nor a hidden coordinate is admitted
as an additional generator. -/
theorem constant_mixed_hidden_independent_eta_quadratic {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hW : WongConstant f) (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hH : ∀i j : Fin 3,(i=0 ∨ i=1) → (j=0 ∨ j=1) →
      ∃c : ℝ,partialDerivative i (partialDerivative j (eta f h))=c•smoothOne)
    (i : Fin 3) (hi : i=0 ∨ i=1) (hiW : wong f i 2≠0) :
    ∃Q : RealPoly,Q.totalDegree≤2 ∧ polynomialSmooth Q=eta f h := by
  obtain ⟨Ω,hΩ⟩ := hW
  have hw (j k : Fin 3) : wong f j k=Ω j k•smoothOne := by
    apply Subtype.ext
    funext x
    simpa [smoothOne] using hΩ j k x
  have hW' : WongConstant f := ⟨Ω,hΩ⟩
  have hα : Ω i 2≠0 := by intro hz; apply hiW; simp [hw,hz]
  obtain ⟨c0,hc0⟩ := hH 0 i (Or.inl rfl) hi
  obtain ⟨c1,hc1⟩ := hH 1 i (Or.inr rfl) hi
  let φ := etaVisibleProfile f h i c0 c1
  have hφ0 : partialDerivative 0 φ=0 := by
    simp [φ,etaVisibleProfile,map_sub,map_smul,hc0,partialDerivative_linearFunction,coordinateVector]
  have hφ1 : partialDerivative 1 φ=0 := by
    simp [φ,etaVisibleProfile,map_sub,map_smul,hc1,partialDerivative_linearFunction,coordinateVector]
  have hD0 := D_mem_of_coordinate_mem f h 0 hx0
  have hD1 := D_mem_of_coordinate_mem f h 1 hx1
  have hI : (1:Operator)∈estimationAlgebra f h := by
    simpa only [multiplication_smoothOne] using smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have hN1 := etaVisibleProfile_mem f h Ω hw hx0 hx1 i hi c0 c1
  change hiddenProfileFirst f (Ω i 2) φ∈estimationAlgebra f h at hN1
  have h2N : (2*Ω i 2)•D f 2+multiplication φ∈estimationAlgebra f h := by
    have he : (2*Ω i 2)•D f 2+multiplication φ= (2:ℝ)•hiddenProfileFirst f (Ω i 2) φ := by
      simp only [hiddenProfileFirst,smul_add,smul_smul]
      module
    rw [he]
    exact (estimationAlgebra f h).smul_mem _ hN1
  obtain ⟨p,hp,hep⟩ := hidden_scalar_quadratic_of_constant_wong_member f h hD0 hD1 hW'
    (2*Ω i 2) φ hφ0 hφ1 h2N
  obtain ⟨a,e,haff⟩ := quadratic_hidden_profile_derivative_affine φ hφ0 hφ1 p hp hep
  have hφ2 : partialDerivative 2 (partialDerivative 2 φ)=a•smoothOne := by
    simp [haff,map_add,map_smul,partialDerivative_const,
      partialDerivative_linearFunction,coordinateVector,SectorTwo.partial_one]
  have hN2 := hiddenProfileSecond_mem_of_first f h Ω hw hD0 hD1 hI (Ω i 2) a φ hφ0 hφ1 hφ2 hN1
  obtain ⟨ha,h333⟩ := hiddenProfile_quadratic_tail_zero f h hHF (Ω i 2) a e hα φ
    (partialDerivative 2 (eta f h)) haff hN1 hN2
  have haff' : partialDerivative 2 φ=e•smoothOne := by simpa only [ha,zero_smul,add_zero] using haff
  have hmixed (j : Fin 3) (hj : j=0 ∨ j=1) :
      partialDerivative j (partialDerivative 2 (partialDerivative 2 (eta f h)))=0 := by
    have hDj : D f j∈estimationAlgebra f h := by rcases hj with rfl|rfl <;> assumption
    have hbr : ⁅D f j,hiddenProfileSecond f (Ω i 2) φ (partialDerivative 2 (eta f h))⁆=
        multiplication ((e*Ω 2 j)•smoothOne+
          (Ω i 2)•partialDerivative j (partialDerivative 2 (eta f h))) := by
      simp only [hiddenProfileSecond,haff',lie_add,lie_smul,operator_lie_mul_right,
        lie_D_multiplication,partialDerivative_const,multiplication_zero,zero_mul,zero_add,
        lie_D_D,hw,multiplication_smul,multiplication_smoothOne,smul_mul_assoc,
        mul_smul_comm,one_mul,smul_smul,multiplication_add]
    have hmem := (estimationAlgebra f h).lie_mem hDj hN2
    rw [hbr] at hmem
    have hz := hHF _ hmem
    simp only [map_add,map_smul,SectorTwo.partial_one,smul_zero,zero_add] at hz
    rw [partialDerivative_commute_apply 2 j] at hz
    exact (smul_eq_zero.mp hz).resolve_left hα
  apply smooth_quadratic_of_third_partials_zero
  intro r s t
  have hvis (j k l : Fin 3) (hk : k=0 ∨ k=1) (hl : l=0 ∨ l=1) :
      partialDerivative j (partialDerivative k (partialDerivative l (eta f h)))=0 := by
    obtain ⟨c,hc⟩ := hH k l hk hl
    rw [hc,partialDerivative_const]
  have hcases (j : Fin 3) : (j = 0 ∨ j = 1) ∨ j = 2 := by
    fin_cases j <;> simp
  rcases hcases r with hr | rfl
  · rcases hcases s with hs | rfl
    · rw [partialDerivative_commute_apply s t (eta f h),
        partialDerivative_commute_apply r t (partialDerivative s (eta f h))]
      exact hvis t r s hr hs
    · rcases hcases t with ht | rfl
      · rw [partialDerivative_commute_apply r 2 (partialDerivative t (eta f h))]
        exact hvis 2 r t hr ht
      · exact hmixed r hr
  · rcases hcases s with hs | rfl
    · rcases hcases t with ht | rfl
      · exact hvis 2 s t hs ht
      · rw [partialDerivative_commute_apply 2 s (partialDerivative 2 (eta f h))]
        exact hmixed s hs
    · rcases hcases t with ht | rfl
      · rw [partialDerivative_commute_apply 2 t (eta f h),
          partialDerivative_commute_apply 2 t (partialDerivative 2 (eta f h))]
        exact hmixed t ht
      · exact h333


/-- When both mixed constants vanish, eta is a visible quadratic plus a
fully retained arbitrary hidden function. -/
theorem constant_wong_zero_mixed_eta_visible_quadratic {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hW : WongConstant f) (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hH : ∀i j : Fin 3,(i=0 ∨ i=1) → (j=0 ∨ j=1) →
      ∃c : ℝ,partialDerivative i (partialDerivative j (eta f h))=c•smoothOne)
    (hW0 : wong f 0 2=0) (hW1 : wong f 1 2=0) :
    ∃Q : RealPoly,∃ψ : Smooth,Q.totalDegree≤2 ∧ eta f h=polynomialSmooth Q+ψ ∧
      partialDerivative 0 ψ=0 ∧ partialDerivative 1 ψ=0 ∧
      (∀i : Fin 3,i=0 ∨ i=1 → ∃c : ℝ,∃b : State,b 2=0 ∧
        partialDerivative i (eta f h)=c•smoothOne+linearFunction b) := by
  obtain ⟨Ω,hΩ⟩ := hW
  have hw (i j : Fin 3) : wong f i j=Ω i j•smoothOne := by
    apply Subtype.ext
    funext x
    simpa [smoothOne] using hΩ i j x
  have hΩ2 (i : Fin 3) (hi : i=0 ∨ i=1) : Ω i 2=0 := by
    have hz : wong f i 2=0 := by rcases hi with rfl|rfl <;> assumption
    have he := congrArg (fun z : Smooth => z.1 (0:State)) (hw i 2)
    rw [hz] at he
    simpa [smoothOne] using he.symm
  have haff (i : Fin 3) (hi : i=0 ∨ i=1) : ∃c : ℝ,∃b : State,b 2=0 ∧
      partialDerivative i (eta f h)=c•smoothOne+linearFunction b := by
    obtain ⟨c0,hc0⟩ := hH 0 i (Or.inl rfl) hi
    obtain ⟨c1,hc1⟩ := hH 1 i (Or.inr rfl) hi
    let φ := etaVisibleProfile f h i c0 c1
    have hm := etaVisibleProfile_mem f h Ω hw hx0 hx1 i hi c0 c1
    rw [hiddenProfileFirst,hΩ2 i hi,zero_smul,zero_add] at hm
    have hmφ : multiplication φ∈estimationAlgebra f h := by
      have hs := (estimationAlgebra f h).smul_mem (2:ℝ) hm
      simpa only [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] using hs
    have hd : ∀j : Fin 3,partialDerivative j φ=0 := by
      intro j
      fin_cases j
      · simp [φ,etaVisibleProfile,map_sub,map_smul,hc0,partialDerivative_linearFunction,coordinateVector]
      · simp [φ,etaVisibleProfile,map_sub,map_smul,hc1,partialDerivative_linearFunction,coordinateVector]
      · exact hHF φ hmφ
    have hc := smooth_eq_constant_of_partials_zero φ hd
    refine ⟨φ.1 0,![c0,c1,0],rfl,?_⟩
    have hlinear : linearFunction ![c0,c1,0]=c0•linearFunction (coordinateVector 0)+
        c1•linearFunction (coordinateVector 1) := by
      apply Subtype.ext
      funext x
      simp [linearFunction,coordinateVector,Fin.sum_univ_three]
    rw [hlinear]
    change partialDerivative i (eta f h) - c0 • linearFunction (coordinateVector 0) -
      c1 • linearFunction (coordinateVector 1) = φ.1 0 • smoothOne at hc
    calc
      _ = φ.1 0 • smoothOne + (c0 • linearFunction (coordinateVector 0) +
          c1 • linearFunction (coordinateVector 1)) := by
        rw [←hc]
        abel
      _ = _ := rfl
  have hhidden (i : Fin 3) (hi : i=0 ∨ i=1) :
      partialDerivative 2 (partialDerivative i (eta f h))=0 := by
    obtain ⟨c,b,hb,he⟩ := haff i hi
    rw [he,map_add,partialDerivative_const,partialDerivative_linearFunction,hb,zero_smul,zero_add]
  obtain ⟨a,ha⟩ := hH 0 0 (Or.inl rfl) (Or.inl rfl)
  obtain ⟨b,hb⟩ := hH 0 1 (Or.inl rfl) (Or.inr rfl)
  obtain ⟨c,hc⟩ := hH 1 1 (Or.inr rfl) (Or.inr rfl)
  obtain ⟨ψ,φ0,φ1,hφ,hrep⟩ := visible_profile_of_constant_hessian (eta f h) a b c ha hb hc
  have hgrad0 : partialDerivative 0 (eta f h)=
      a•linearFunction (coordinateVector 0)+b•linearFunction (coordinateVector 1)+φ0 := by
    rw [hrep]
    simp only [map_add,visibleEtaQuadratic_partial,partialDerivative_smoothMul,
      partialDerivative_linearFunction,(hφ 0 (Or.inl rfl)).1,
      (hφ 0 (Or.inl rfl)).2.1,(hφ 0 (Or.inl rfl)).2.2]
    simp [coordinateVector,smoothMul_eq_mul,smoothOne_eq_one]
  have hgrad1 : partialDerivative 1 (eta f h)=
      b•linearFunction (coordinateVector 0)+c•linearFunction (coordinateVector 1)+φ1 := by
    rw [hrep]
    simp only [map_add,visibleEtaQuadratic_partial,partialDerivative_smoothMul,
      partialDerivative_linearFunction,(hφ 1 (Or.inr rfl)).1,
      (hφ 1 (Or.inr rfl)).2.1,(hφ 1 (Or.inr rfl)).2.2]
    simp [coordinateVector,smoothMul_eq_mul,smoothOne_eq_one]
  have hφ0hidden : partialDerivative 2 φ0=0 := by
    have hz := hhidden 0 (Or.inl rfl)
    simpa [hgrad0,map_add,map_smul,partialDerivative_linearFunction,coordinateVector] using hz
  have hφ1hidden : partialDerivative 2 φ1=0 := by
    have hz := hhidden 1 (Or.inr rfl)
    simpa [hgrad1,map_add,map_smul,partialDerivative_linearFunction,coordinateVector] using hz
  have hφ0 : φ0=φ0.1 0•smoothOne := by
    apply smooth_eq_constant_of_partials_zero
    intro i
    fin_cases i
    · exact (hφ 0 (Or.inl rfl)).2.1
    · exact (hφ 1 (Or.inr rfl)).2.1
    · exact hφ0hidden
  have hφ1 : φ1=φ1.1 0•smoothOne := by
    apply smooth_eq_constant_of_partials_zero
    intro i
    fin_cases i
    · exact (hφ 0 (Or.inl rfl)).2.2
    · exact (hφ 1 (Or.inr rfl)).2.2
    · exact hφ1hidden
  let Q : RealPoly := C (a/2)*X 0^2+C b*X 0*X 1+C (c/2)*X 1^2+
    C (φ0.1 0)*X 0+C (φ1.1 0)*X 1
  have hQ : Q.totalDegree≤2 := by
    have hquad (d : ℝ) (i : Fin 3) : (C d * X i ^ 2 : RealPoly).totalDegree ≤ 2 :=
      (totalDegree_mul _ _).trans (by simp)
    have hlin (d : ℝ) (i : Fin 3) : (C d * X i : RealPoly).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by simp)
    have hcross : (C b * X 0 * X 1 : RealPoly).totalDegree ≤ 2 := by
      apply (totalDegree_mul _ _).trans
      simpa only [totalDegree_X] using Nat.add_le_add_right (hlin b 0) 1
    exact (totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le
        ((totalDegree_add _ _).trans (max_le
          ((totalDegree_add _ _).trans (max_le (hquad (a/2) 0) hcross))
          (hquad (c/2) 1)))
        ((hlin (φ0.1 0) 0).trans (by omega))))
      ((hlin (φ1.1 0) 1).trans (by omega)))
  refine ⟨Q,ψ,hQ,?_,(hφ 0 (Or.inl rfl)).1,(hφ 1 (Or.inr rfl)).1,haff⟩
  rw [hrep,hφ0,hφ1]
  apply Subtype.ext
  funext x
  simp [Q,visibleEtaQuadratic,polynomialSmooth,smoothMul,smoothOne,
    linearFunction,coordinateVector,Fin.sum_univ_three]
  ring

/-- Shared exact-model conclusion for the whole hidden-independent branch.
The two curvature alternatives are discharged internally. -/
theorem functionElementsAffine_of_constant_wong_hidden_independent_visible_hessians {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx0 : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hW : WongConstant f) (hHF : HiddenIndependentFunctionSpace (estimationAlgebra f h))
    (hH : ∀i j : Fin 3,(i=0 ∨ i=1) → (j=0 ∨ j=1) →
      ∃c : ℝ,partialDerivative i (partialDerivative j (eta f h))=c•smoothOne) :
    FunctionElementsAffine (estimationAlgebra f h) := by
  by_cases hW0 : wong f 0 2=0
  · by_cases hW1 : wong f 1 2=0
    · obtain ⟨Q,ψ,hQ,heta,hψ0,hψ1,haff⟩ := constant_wong_zero_mixed_eta_visible_quadratic
        f h hx0 hx1 hW hHF hH hW0 hW1
      have hobsHidden (j : Fin m) : partialDerivative 2 (h j)=0 :=
        hHF _ (LieSubalgebra.subset_lieSpan (Or.inr ⟨j,rfl⟩))
      have hobs := observations_affine_of_visible_quadratic_eta f h Q ψ hQ heta hobsHidden hψ0 hψ1
      apply visible_constant_wong_affine_eta_functionElementsAffine f h hW hW0 hW1
      · intro i hi
        have hvis : i=0 ∨ i=1 := by fin_cases i <;> simp_all
        exact haff i hvis
      · intro j
        obtain ⟨p,hp,he⟩ := hobs j
        obtain ⟨c,b,hb⟩ := polynomialSmooth_exists_affine_of_degree_le_one p hp
        have hb2 : b 2=0 := by
          have hz := hobsHidden j
          rw [←he,hb,map_add,partialDerivative_const,partialDerivative_linearFunction,zero_add] at hz
          have heq := congrArg (fun u : Smooth => u.1 (0:State)) hz
          simpa [smoothOne] using heq
        exact ⟨c,b,hb2,he.symm.trans hb⟩
    · obtain ⟨Q,hQ,heta⟩ := constant_mixed_hidden_independent_eta_quadratic
        f h hrank hx0 hx1 hW hHF hH 1 (Or.inr rfl) hW1
      exact functionElementsAffine_of_constant_wong_quadratic_eta f h hW Q hQ heta
  · obtain ⟨Q,hQ,heta⟩ := constant_mixed_hidden_independent_eta_quadratic
      f h hrank hx0 hx1 hW hHF hH 0 (Or.inl rfl) hW0
    exact functionElementsAffine_of_constant_wong_quadratic_eta f h hW Q hQ heta

end Wong.SmoothModel
#print axioms Wong.SmoothModel.constant_mixed_hidden_independent_eta_quadratic

#print axioms Wong.SmoothModel.functionElementsAffine_of_constant_wong_hidden_independent_visible_hessians
