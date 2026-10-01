import Wong.GeneratorCommutator
import Wong.FunctionQuadraticRankConstraints
import Wong.PublishedAffineStatement

/-! A genuine operator envelope spanned by L0, the identity, the admitted
constant covariant directions, and their linear multipliers.  Multiplier
classification uses coordinate commutators on actual smooth test functions.
No finite-dimensionality or formal-symbol assumption is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Wong.SmoothModel

def finiteClosureForm {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (z : ℝ) (a : State) (c : ℝ) (b : State) : Operator :=
  z • L0 f h + directionD f a + c • (1 : Operator) + linearMultiplication b

theorem finiteClosure_linearMultiplication_apply (b : State) :
    linearMultiplication b = multiplication (linearFunction b) := rfl

theorem finiteClosure_direction_add (f : Fin 3 → Smooth) (a b : State) :
    directionD f (a+b)=directionD f a+directionD f b := by
  simp [directionD, add_smul, Finset.sum_add_distrib]

theorem finiteClosure_direction_smul (f : Fin 3 → Smooth) (r : ℝ) (a : State) :
    directionD f (r•a)=r•directionD f a := by
  simp only [directionD, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

@[simp] theorem finiteClosure_direction_zero (f : Fin 3 → Smooth) : directionD f 0=0 := by
  simp [directionD]

@[simp] theorem finiteClosure_direction_coordinate (f : Fin 3 → Smooth) (i : Fin 3) :
    directionD f (coordinateVector i)=D f i := by
  simp [directionD, coordinateVector, Pi.single_apply, ite_smul]

theorem finiteClosureForm_add {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (z z' : ℝ) (a a' : State) (c c' : ℝ) (b b' : State) :
    finiteClosureForm f h (z+z') (a+a') (c+c') (b+b')=
      finiteClosureForm f h z a c b+finiteClosureForm f h z' a' c' b' := by
  simp only [finiteClosureForm, add_smul, finiteClosure_direction_add, map_add]
  abel

theorem finiteClosureForm_smul {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (r z : ℝ) (a : State) (c : ℝ) (b : State) :
    finiteClosureForm f h (r*z) (r•a) (r*c) (r•b)=r•finiteClosureForm f h z a c b := by
  simp only [finiteClosureForm, mul_smul, finiteClosure_direction_smul, map_smul, smul_add]

/-- Exactly the real operator combinations of L0, I, D(a), and M(linear b),
with both coefficient vectors in V.  V=top has the eight indicated generators. -/
def finiteClosureSpace {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (V : Submodule ℝ State) : Submodule ℝ Operator where
  carrier := {A | ∃ z a c b, a∈V ∧ b∈V ∧ A=finiteClosureForm f h z a c b}
  zero_mem' := ⟨0,0,0,0,V.zero_mem,V.zero_mem,by simp [finiteClosureForm]⟩
  add_mem' := by
    rintro A B ⟨z,a,c,b,ha,hb,rfl⟩ ⟨z',a',c',b',ha',hb',rfl⟩
    exact ⟨z+z',a+a',c+c',b+b',V.add_mem ha ha',V.add_mem hb hb',
      (finiteClosureForm_add f h z z' a a' c c' b b').symm⟩
  smul_mem' := by
    rintro r A ⟨z,a,c,b,ha,hb,rfl⟩
    exact ⟨r*z,r•a,r*c,r•b,V.smul_mem r ha,V.smul_mem r hb,
      (finiteClosureForm_smul f h r z a c b).symm⟩

theorem finiteClosure_L0_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (V : Submodule ℝ State) : L0 f h ∈ finiteClosureSpace f h V :=
  ⟨1,0,0,0,V.zero_mem,V.zero_mem,by simp [finiteClosureForm]⟩

theorem finiteClosure_scalar_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (V : Submodule ℝ State) (c : ℝ) : c • (1 : Operator) ∈ finiteClosureSpace f h V :=
  ⟨0,0,c,0,V.zero_mem,V.zero_mem,by simp [finiteClosureForm]⟩

theorem finiteClosure_direction_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (V : Submodule ℝ State) (a : State) (ha : a∈V) :
    directionD f a ∈ finiteClosureSpace f h V :=
  ⟨0,a,0,0,ha,V.zero_mem,by simp [finiteClosureForm]⟩

theorem finiteClosure_linear_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (V : Submodule ℝ State) (b : State) (hb : b∈V) :
    linearMultiplication b ∈ finiteClosureSpace f h V :=
  ⟨0,0,0,b,V.zero_mem,hb,by simp [finiteClosureForm]⟩

theorem finiteClosure_affine_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (V : Submodule ℝ State) (c : ℝ) (b : State) (hb : b∈V) :
    multiplication (c•smoothOne+linearFunction b) ∈ finiteClosureSpace f h V := by
  rw [multiplication_add, multiplication_smul, multiplication_smoothOne]
  exact (finiteClosureSpace f h V).add_mem (finiteClosure_scalar_mem f h V c)
    (finiteClosure_linear_mem f h V b hb)

@[simp] theorem finiteClosure_lie_one (A : Operator) : ⁅A,(1 : Operator)⁆=0 := by
  simpa only [one_smul] using lie_scalar_identity A 1

@[simp] theorem finiteClosure_one_lie (A : Operator) : ⁅(1 : Operator),A⁆=0 := by
  simpa only [one_smul] using scalar_identity_lie 1 A

theorem finiteClosure_lie_direction_linear (f : Fin 3 → Smooth) (a b : State) :
    ⁅directionD f a,linearMultiplication b⁆=(∑i : Fin 3,a i*b i)•(1 : Operator) := by
  simp only [directionD, finiteClosure_linearMultiplication_apply, sum_lie, smul_lie,
    lie_D_multiplication, partialDerivative_linearFunction, multiplication_smul,
    multiplication_smoothOne, smul_smul, Finset.sum_smul]

@[simp] theorem finiteClosure_lie_linear_linear (a b : State) :
    ⁅linearMultiplication a,linearMultiplication b⁆=0 :=
  lie_multiplication_multiplication _ _

theorem finiteClosure_lie_L0_linear {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (b : State) :
    ⁅L0 f h,linearMultiplication b⁆=directionD f b := lie_L0_linearFunction f h b

/-- Two directional bracket conditions give actual Lie closure of the stated
operator envelope.  They are discharged below from constant Wong and affine eta. -/
theorem finiteClosureSpace_lie_closed {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (V : Submodule ℝ State)
    (hLD : ∀a∈V, ⁅L0 f h,directionD f a⁆∈finiteClosureSpace f h V)
    (hDD : ∀a∈V, ∀b∈V, ⁅directionD f a,directionD f b⁆∈finiteClosureSpace f h V)
    {A B : Operator} (hA : A∈finiteClosureSpace f h V)
    (hB : B∈finiteClosureSpace f h V) : ⁅A,B⁆∈finiteClosureSpace f h V := by
  rcases hA with ⟨z,a,c,b,ha,hb,rfl⟩
  rcases hB with ⟨z',a',c',b',ha',hb',rfl⟩
  let S := finiteClosureSpace f h V
  have hLD' := hLD a' ha'
  have hDL : ⁅directionD f a,L0 f h⁆∈S := by
    rw [← lie_skew]
    exact S.neg_mem (hLD a ha)
  have hDD' := hDD a ha a' ha'
  have hLM : ⁅L0 f h,linearMultiplication b'⁆∈S := by
    rw [finiteClosure_lie_L0_linear]
    exact finiteClosure_direction_mem f h V b' hb'
  have hML : ⁅linearMultiplication b,L0 f h⁆∈S := by
    rw [← lie_skew, finiteClosure_lie_L0_linear]
    exact S.neg_mem (finiteClosure_direction_mem f h V b hb)
  have hDM : ⁅directionD f a,linearMultiplication b'⁆∈S := by
    rw [finiteClosure_lie_direction_linear]
    exact finiteClosure_scalar_mem f h V _
  have hMD : ⁅linearMultiplication b,directionD f a'⁆∈S := by
    rw [← lie_skew, finiteClosure_lie_direction_linear]
    exact S.neg_mem (finiteClosure_scalar_mem f h V _)
  change ⁅finiteClosureForm f h z a c b,finiteClosureForm f h z' a' c' b'⁆∈S
  simp only [finiteClosureForm, add_lie, lie_add, smul_lie, lie_smul,
    lie_self, finiteClosure_lie_one, finiteClosure_one_lie,
    finiteClosure_lie_linear_linear, smul_zero, zero_add, add_zero]
  repeat' first | assumption | exact S.zero_mem | apply S.add_mem | apply S.smul_mem

/-- Coordinate testing detects the genuine order-two and order-one terms. -/
theorem finiteClosureForm_coordinate_commutator {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (z : ℝ) (a : State) (c : ℝ) (b : State) (i : Fin 3) :
    ⁅finiteClosureForm f h z a c b,linearMultiplication (coordinateVector i)⁆=
      z•D f i+a i•(1 : Operator) := by
  simp only [finiteClosureForm, add_lie, smul_lie,
    finiteClosure_lie_L0_linear, finiteClosure_direction_coordinate,
    finiteClosure_lie_direction_linear, finiteClosure_one_lie,
    finiteClosure_lie_linear_linear, smul_zero, add_zero]
  congr 1
  simp [coordinateVector, Pi.single_apply, mul_ite]

theorem finiteClosure_scalar_identity_zero (c : ℝ) (hc : c•(1 : Operator)=0) : c=0 := by
  have he := congrArg (fun A : Operator => (A smoothOne).1 (0 : State)) hc
  change c*1=0 at he
  simpa using he

theorem finiteClosure_multiplier_affine {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (V : Submodule ℝ State) (u : Smooth)
    (hu : multiplication u∈finiteClosureSpace f h V) :
    ∃(c : ℝ) (b : State), b∈V ∧ u=c•smoothOne+linearFunction b := by
  rcases hu with ⟨z,a,c,b,ha,hb,hu⟩
  have he (i : Fin 3) : z•D f i+a i•(1 : Operator)=0 := by
    rw [← finiteClosureForm_coordinate_commutator f h z a c b i, ← hu]
    exact lie_multiplication_multiplication _ _
  have hz : z=0 := by
    have hd := congrArg (fun A : Operator => ⁅A,linearMultiplication (coordinateVector 0)⁆) (he 0)
    simp only [add_lie, smul_lie, finiteClosure_one_lie, smul_zero, add_zero, zero_lie,
      finiteClosure_linearMultiplication_apply, lie_D_multiplication, partialDerivative_linearFunction,
      multiplication_smul, multiplication_smoothOne] at hd
    have hz' : z•(1 : Operator)=0 := by simpa [coordinateVector] using hd
    exact finiteClosure_scalar_identity_zero z hz'
  have ha0 : a=0 := by
    funext i
    have hh := he i
    rw [hz, zero_smul, zero_add] at hh
    exact finiteClosure_scalar_identity_zero (a i) hh
  refine ⟨c,b,hb,?_⟩
  apply multiplication_injective
  rw [hu, hz, ha0]
  simp only [finiteClosureForm, zero_smul, finiteClosure_direction_zero, zero_add,
    multiplication_add, multiplication_smul, multiplication_smoothOne,
    finiteClosure_linearMultiplication_apply]

theorem finiteClosure_functionElementsAffine {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (V : Submodule ℝ State)
    (E : LieSubalgebra ℝ Operator) (hE : E.toSubmodule ≤ finiteClosureSpace f h V) :
    FunctionElementsAffine E := by
  intro u hu
  obtain ⟨c,b,_,he⟩ := finiteClosure_multiplier_affine f h V u (hE hu)
  exact ⟨affineScalarPolynomial c b,affineScalarPolynomial_degree_le_one c b,
    (polynomialSmooth_affineScalarPolynomial c b).trans he.symm⟩

/-- Actual minimality of the filtering Lie algebra, once the explicit
envelope brackets and observation multipliers have been checked. -/
theorem estimationAlgebra_le_finiteClosure_of_brackets {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (V : Submodule ℝ State)
    (hLD : ∀a∈V, ⁅L0 f h,directionD f a⁆∈finiteClosureSpace f h V)
    (hDD : ∀a∈V, ∀b∈V, ⁅directionD f a,directionD f b⁆∈finiteClosureSpace f h V)
    (hobs : ∀j,multiplication (h j)∈finiteClosureSpace f h V) :
    (estimationAlgebra f h).toSubmodule ≤ finiteClosureSpace f h V := by
  let E : LieSubalgebra ℝ Operator :=
    { finiteClosureSpace f h V with
      lie_mem' := fun hA hB => finiteClosureSpace_lie_closed f h V hLD hDD hA hB }
  have he : estimationAlgebra f h ≤ E := by
    apply LieSubalgebra.lieSpan_le.mpr
    intro A hA
    rcases hA with rfl | ⟨j,rfl⟩
    · exact finiteClosure_L0_mem f h V
    · exact hobs j
  exact he

end Wong.SmoothModel

#print axioms Wong.SmoothModel.finiteClosure_multiplier_affine
#print axioms Wong.SmoothModel.estimationAlgebra_le_finiteClosure_of_brackets
