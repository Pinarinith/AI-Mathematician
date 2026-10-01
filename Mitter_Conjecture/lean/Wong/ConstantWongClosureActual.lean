import Wong.ConstantWongFiniteClosure

/-! All closure hypotheses are derived from the genuine Wong commutators and
the genuine original eta. A coordinate subset specializes to eight or six
generators, while the original L0 retains its complete scalar potential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Wong.SmoothModel

def closureCoordinateSpace (s : Finset (Fin 3)) : Submodule ℝ State where
  carrier := {a | ∀i, i∉s → a i=0}
  zero_mem' := by intro i _; rfl
  add_mem' := by intro a b ha hb i hi; simp only [Pi.add_apply,ha i hi,hb i hi,add_zero]
  smul_mem' := by intro r a ha i hi; simp only [Pi.smul_apply,ha i hi,smul_zero]

theorem closureCoordinateSpace_coordinate (s : Finset (Fin 3)) (i : Fin 3) (hi : i∈s) :
    coordinateVector i∈closureCoordinateSpace s := by
  intro j hj
  have hji : j≠i := by rintro rfl; exact hj hi
  simp [coordinateVector, hji]

/-- The complete coordinate-subset closure theorem.  Every displayed operator
commutator follows from the actual filtering generator; no new finite Lie
algebra is substituted for the original estimation algebra. -/
theorem coordinate_constant_wong_estimationAlgebra_le {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (s : Finset (Fin 3))
    (Ω : Fin 3 → Fin 3 → ℝ)
    (hW : ∀i∈s, ∀j, wong f i j=Ω i j•smoothOne)
    (hrow : ∀i∈s, ∀j, j∉s → Ω i j=0)
    (heta : ∀i∈s, ∃(c : ℝ) (b : State), b∈closureCoordinateSpace s ∧
      partialDerivative i (eta f h)=c•smoothOne+linearFunction b)
    (hobs : ∀j, ∃(c : ℝ) (b : State), b∈closureCoordinateSpace s ∧
      h j=c•smoothOne+linearFunction b) :
    (estimationAlgebra f h).toSubmodule ≤ finiteClosureSpace f h (closureCoordinateSpace s) := by
  let V := closureCoordinateSpace s
  let S := finiteClosureSpace f h V
  have hD (i : Fin 3) (hi : i∈s) : D f i∈S := by
    simpa only [finiteClosure_direction_coordinate] using
      finiteClosure_direction_mem f h V (coordinateVector i)
        (closureCoordinateSpace_coordinate s i hi)
  have hLDcoordinate (i : Fin 3) (hi : i∈s) : ⁅L0 f h,D f i⁆∈S := by
    have hder (j : Fin 3) : partialDerivative j (wong f i j)=0 := by
      rw [hW i hi j]
      exact partialDerivative_const j (Ω i j)
    have hrem : generatorRemainder f h i=(1/2:ℝ)•partialDerivative i (eta f h) := by
      simp only [generatorRemainder,hder,Finset.sum_const_zero,zero_add]
    rw [lie_L0_D,hrem,multiplication_smul]
    apply S.add_mem
    · apply S.sum_mem
      intro j _
      rw [hW i hi j,multiplication_smul,multiplication_smoothOne,smul_mul_assoc,one_mul]
      by_cases hj : j∈s
      · exact S.smul_mem _ (hD j hj)
      · rw [hrow i hi j hj,zero_smul]
        exact S.zero_mem
    · apply S.smul_mem
      obtain ⟨c,b,hb,he⟩ := heta i hi
      rw [he]
      exact finiteClosure_affine_mem f h V c b hb
  have hLD (a : State) (ha : a∈V) : ⁅L0 f h,directionD f a⁆∈S := by
    simp only [directionD,lie_sum,lie_smul]
    apply S.sum_mem
    intro i _
    by_cases hi : i∈s
    · exact S.smul_mem _ (hLDcoordinate i hi)
    · rw [ha i hi,zero_smul]
      exact S.zero_mem
  have hDD (a : State) (ha : a∈V) (b : State) (hb : b∈V) :
      ⁅directionD f a,directionD f b⁆∈S := by
    simp only [directionD,sum_lie,lie_sum,smul_lie,lie_smul]
    apply S.sum_mem
    intro i _
    by_cases hi : i∈s
    · apply S.smul_mem
      apply S.sum_mem
      intro j _
      by_cases hj : j∈s
      · apply S.smul_mem
        rw [lie_D_D,hW i hi j,multiplication_smul,multiplication_smoothOne]
        exact finiteClosure_scalar_mem f h V _
      · rw [ha j hj,zero_smul]
        exact S.zero_mem
    · rw [hb i hi,zero_smul]
      exact S.zero_mem
  have hobs' (j : Fin m) : multiplication (h j)∈S := by
    obtain ⟨c,b,hb,he⟩ := hobs j
    rw [he]
    exact finiteClosure_affine_mem f h V c b hb
  exact estimationAlgebra_le_finiteClosure_of_brackets f h V hLD hDD hobs'

theorem coordinate_constant_wong_functionElementsAffine {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (s : Finset (Fin 3))
    (Ω : Fin 3 → Fin 3 → ℝ)
    (hW : ∀i∈s, ∀j, wong f i j=Ω i j•smoothOne)
    (hrow : ∀i∈s, ∀j, j∉s → Ω i j=0)
    (heta : ∀i∈s, ∃(c : ℝ) (b : State), b∈closureCoordinateSpace s ∧
      partialDerivative i (eta f h)=c•smoothOne+linearFunction b)
    (hobs : ∀j, ∃(c : ℝ) (b : State), b∈closureCoordinateSpace s ∧
      h j=c•smoothOne+linearFunction b) :
    FunctionElementsAffine (estimationAlgebra f h) :=
  finiteClosure_functionElementsAffine f h (closureCoordinateSpace s) (estimationAlgebra f h)
    (coordinate_constant_wong_estimationAlgebra_le f h s Ω hW hrow heta hobs)

/-- Eight-generator closure for the actual constant-Wong model.  The eta
derivatives and observations are assumed affine as functions, while every
function element of the original estimation algebra is proved affine. -/
theorem constant_wong_affine_eta_functionElementsAffine {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (hW : WongConstant f)
    (heta : ∀i, ∃(c : ℝ) (b : State), partialDerivative i (eta f h)=c•smoothOne+linearFunction b)
    (hobs : ∀j, ∃(c : ℝ) (b : State), h j=c•smoothOne+linearFunction b) :
    FunctionElementsAffine (estimationAlgebra f h) := by
  obtain ⟨Ω,hΩ⟩ := hW
  apply coordinate_constant_wong_functionElementsAffine f h Finset.univ Ω
  · intro i _ j
    apply Subtype.ext
    funext x
    change (wong f i j).1 x=Ω i j*1
    rw [hΩ,mul_one]
  · intro i _ j hj
    exact False.elim (hj (Finset.mem_univ j))
  · intro i _
    obtain ⟨c,b,hb⟩ := heta i
    exact ⟨c,b,by intro j hj; exact False.elim (hj (Finset.mem_univ j)),hb⟩
  · intro j
    obtain ⟨c,b,hb⟩ := hobs j
    exact ⟨c,b,by intro i hi; exact False.elim (hi (Finset.mem_univ i)),hb⟩

theorem constant_wong_polynomial_eta_functionElementsAffine {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (hW : WongConstant f)
    (heta : ∀i, ∃p : RealPoly, p.totalDegree≤1 ∧
      polynomialSmooth p=partialDerivative i (eta f h))
    (hobs : ∀j, ∃p : RealPoly, p.totalDegree≤1 ∧ polynomialSmooth p=h j) :
    FunctionElementsAffine (estimationAlgebra f h) := by
  apply constant_wong_affine_eta_functionElementsAffine f h hW
  · intro i
    obtain ⟨p,hp,he⟩ := heta i
    exact ⟨p.coeff 0,fun j => p.coeff (Finsupp.single j 1),
      he.symm.trans (polynomialSmooth_affine_of_degree_le_one p hp)⟩
  · intro j
    obtain ⟨p,hp,he⟩ := hobs j
    exact ⟨p.coeff 0,fun i => p.coeff (Finsupp.single i 1),
      he.symm.trans (polynomialSmooth_affine_of_degree_le_one p hp)⟩

theorem closureCoordinateSpace_visible_iff (a : State) :
    a∈closureCoordinateSpace ({0,1} : Finset (Fin 3)) ↔ a 2=0 := by
  constructor
  · intro ha
    exact ha 2 (by decide)
  · intro ha i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · exact ha

/-- Six-generator closure.  No D2 is placed in the envelope and no condition
is imposed on the hidden derivative of eta or its hidden-only remainder. -/
theorem visible_constant_wong_affine_eta_functionElementsAffine {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (hW : WongConstant f)
    (hW₀₂ : wong f 0 2=0) (hW₁₂ : wong f 1 2=0)
    (heta : ∀i : Fin 3, i≠2 → ∃(c : ℝ) (b : State), b 2=0 ∧
      partialDerivative i (eta f h)=c•smoothOne+linearFunction b)
    (hobs : ∀j, ∃(c : ℝ) (b : State), b 2=0 ∧ h j=c•smoothOne+linearFunction b) :
    FunctionElementsAffine (estimationAlgebra f h) := by
  obtain ⟨Ω,hΩ⟩ := hW
  have hΩ₀₂ : Ω 0 2=0 := by
    have he := hΩ 0 2 (0 : State)
    rw [hW₀₂] at he
    exact he.symm
  have hΩ₁₂ : Ω 1 2=0 := by
    have he := hΩ 1 2 (0 : State)
    rw [hW₁₂] at he
    exact he.symm
  apply coordinate_constant_wong_functionElementsAffine f h {0,1} Ω
  · intro i _ j
    apply Subtype.ext
    funext x
    change (wong f i j).1 x=Ω i j*1
    rw [hΩ,mul_one]
  · intro i hi j hj
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i hi
    have hi₂ : i≠2 := by rintro rfl; simp at hi
    obtain ⟨c,b,hb,he⟩ := heta i hi₂
    exact ⟨c,b,(closureCoordinateSpace_visible_iff b).mpr hb,he⟩
  · intro j
    obtain ⟨c,b,hb,he⟩ := hobs j
    exact ⟨c,b,(closureCoordinateSpace_visible_iff b).mpr hb,he⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.constant_wong_polynomial_eta_functionElementsAffine
#print axioms Wong.SmoothModel.visible_constant_wong_affine_eta_functionElementsAffine
