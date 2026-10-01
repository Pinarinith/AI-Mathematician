import Wong.QuadraticFunctionClassification

/-! Exhaustive whole-function case reductions. All coordinate changes act
on the actual original model; singularity is transported for every genuine
quadratic member, rather than inferred from one admitted square. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Wong.SmoothModel
open MvPolynomial
open scoped Matrix

def ClassificationVisibleSingular {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) : Prop :=
  ∀a b c : ℝ, visibleBinaryQuadratic a b c∈polynomialFunctionElements f h → a*c-b^2=0

theorem classification_planeRotation_symm_apply (r s : ℝ) (hrs : r^2+s^2=1) (x : State) :
    (VisibleHeads.planeRotation r s hrs).symm x=
      ![r*x 0-s*x 1,s*x 0+r*x 1,x 2] := rfl

theorem classification_binary_inverse_pullback (r s : ℝ) (hrs : r^2+s^2=1)
    (a b c : ℝ) :
    coordinatePullback (VisibleHeads.planeRotation r s hrs).symm
      (polynomialSmooth (visibleBinaryQuadratic a b c))=
      polynomialSmooth (visibleBinaryQuadratic
        (a*r^2+2*b*r*s+c*s^2) (-a*r*s+b*(r^2-s^2)+c*r*s)
        (a*s^2-2*b*r*s+c*r^2)) := by
  apply Subtype.ext
  funext x
  simp only [coordinatePullback_apply]
  change eval ((VisibleHeads.planeRotation r s hrs).symm x) (visibleBinaryQuadratic a b c)=_
  rw [classification_planeRotation_symm_apply]
  simp [polynomialSmooth,visibleBinaryQuadratic]
  ring

theorem classification_binary_inverse_det (r s : ℝ) (hrs : r^2+s^2=1) (a b c : ℝ) :
    (a*r^2+2*b*r*s+c*s^2)*(a*s^2-2*b*r*s+c*r^2)-
      (-a*r*s+b*(r^2-s^2)+c*r*s)^2=a*c-b^2 := by
  calc
    _ = (a*c-b^2)*(r^2+s^2)^2 := by ring
    _ = _ := by rw [hrs]; ring

/-- The whole quadratic-space determinant condition survives the genuine
visible rotation, including quadratics other than the one diagonalized. -/
theorem classification_visible_singular_rotation {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hS : ClassificationVisibleSingular f h) (r s : ℝ) (hrs : r^2+s^2=1) :
    ClassificationVisibleSingular (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
      (coordinateObservations (VisibleHeads.planeRotation r s hrs) h) := by
  intro a b c hq
  let e := VisibleHeads.planeRotation r s hrs
  have he : CoordinateOrthogonal e := VisibleHeads.planeRotation_orthogonal r s hrs
  have hsource : multiplication (coordinatePullback e.symm
      (polynomialSmooth (visibleBinaryQuadratic a b c)))∈estimationAlgebra f h := by
    apply (multiplication_pullback_mem_coordinateAlgebra e (estimationAlgebra f h) _).mp
    change multiplication (coordinatePullback e ((coordinatePullback e).symm
      (polynomialSmooth (visibleBinaryQuadratic a b c))))∈_
    rw [LinearEquiv.apply_symm_apply,coordinateAlgebra_estimationAlgebra e he]
    exact hq
  change multiplication (coordinatePullback (VisibleHeads.planeRotation r s hrs).symm
    (polynomialSmooth (visibleBinaryQuadratic a b c)))∈_ at hsource
  rw [classification_binary_inverse_pullback] at hsource
  have hz := hS _ _ _ hsource
  rwa [classification_binary_inverse_det r s hrs a b c] at hz

/-- With genuine hidden independence, the entire quadratic remainder is a
visible binary quadratic and is itself genuinely admitted. -/
theorem actual_hidden_independent_visible_quadratic_representation {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hHF : ∀u : Smooth, multiplication u∈estimationAlgebra f h → partialDerivative 2 u=0)
    (u : Smooth) (hu : multiplication u∈estimationAlgebra f h) :
    ∃a b c ell₀ ell₁ r : ℝ, visibleBinaryQuadratic a b c∈polynomialFunctionElements f h ∧
      u=polynomialSmooth (visibleBinaryQuadratic a b c)+
        ell₀•linearFunction (coordinateVector 0)+ell₁•linearFunction (coordinateVector 1)+
        r•smoothOne := by
  obtain ⟨a,b,c,d,g,ell₀,ell₁,r,hq,hrep,hsecond⟩ :=
    actual_function_quadratic_tail_representation f h hrank hx₀ hx₁ u hu
  have hd : d=0 := by
    rw [hHF u hu,map_zero] at hsecond
    have he := congrArg (fun v : Smooth => v.1 (0 : State)) hsecond
    simp [smoothOne] at he
    linarith
  subst d
  have htail : multiplication (polynomialSmooth (visibleBinaryQuadratic a b c+C g*X 2))∈
      estimationAlgebra f h := by
    have hqtail : visibleBinaryQuadratic a b c+C g*X 2∈polynomialFunctionElements f h := by
      simpa [classificationQuadraticTail] using hq
    exact hqtail
  have hg := hidden_linear_tail_zero_of_visible_binary_quadratic_member
    f h hrank hx₀ hx₁ a b c g htail
  subst g
  refine ⟨a,b,c,ell₀,ell₁,r,?_,?_⟩
  · simpa [classificationQuadraticTail] using hq
  · simpa [classificationQuadraticTail] using hrep

/-- An actual degree-two witness cannot disappear into the admitted affine
remainder. This derives the nonzero visible matrix from the original witness. -/
theorem actual_hidden_independent_visible_quadratic_witness {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hHF : ∀u : Smooth, multiplication u∈estimationAlgebra f h → partialDerivative 2 u=0)
    (p : RealPoly) (hp : p.totalDegree=2) (hpE : p∈polynomialFunctionElements f h) :
    ∃a b c : ℝ, (a≠0 ∨ b≠0 ∨ c≠0) ∧ visibleBinaryQuadratic a b c∈polynomialFunctionElements f h := by
  obtain ⟨a,b,c,ell₀,ell₁,r,hq,hrep⟩ :=
    actual_hidden_independent_visible_quadratic_representation f h hrank hx₀ hx₁ hHF
      (polynomialSmooth p) hpE
  refine ⟨a,b,c,?_,hq⟩
  by_contra! hz
  rcases hz with ⟨ha,hb,hc⟩
  have haff : polynomialSmooth p=r•smoothOne+linearFunction ![ell₀,ell₁,0] := by
    rw [hrep]
    apply Subtype.ext
    funext x
    simp [ha,hb,hc,visibleBinaryQuadratic,polynomialSmooth,smoothOne,linearFunction,
      coordinateVector,Fin.sum_univ_three]
    ring
  have hd := totalDegree_le_one_of_polynomialSmooth_affine p r ![ell₀,ell₁,0] haff
  omega


def ClassificationVisibleOutcome (E : LieSubalgebra ℝ Operator) : Prop :=
  multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 1 0))∈E ∨
    HiddenIndependent.C2FunctionSpace E

/-- Exhaustive visible classification in the hidden-independent branch:
there is a genuine radial member or the entire function space has C2 form. -/
theorem actual_hidden_independent_quadratic_model {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hHF : ∀u : Smooth, multiplication u∈estimationAlgebra f h → partialDerivative 2 u=0)
    (p : RealPoly) (hp : p.totalDegree=2) (hpE : p∈polynomialFunctionElements f h) :
    ∃(r s : ℝ) (hrs : r^2+s^2=1),
      FiniteDimensional ℝ (estimationAlgebra
        (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
        (coordinateObservations (VisibleHeads.planeRotation r s hrs) h)) ∧
      linearRank (estimationAlgebra (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
        (coordinateObservations (VisibleHeads.planeRotation r s hrs) h))=2 ∧
      multiplication (linearFunction (coordinateVector 0))∈
        estimationAlgebra (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
          (coordinateObservations (VisibleHeads.planeRotation r s hrs) h) ∧
      multiplication (linearFunction (coordinateVector 1))∈
        estimationAlgebra (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
          (coordinateObservations (VisibleHeads.planeRotation r s hrs) h) ∧
      HiddenIndependentFunctionSpace
        (estimationAlgebra (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
          (coordinateObservations (VisibleHeads.planeRotation r s hrs) h)) ∧
      ClassificationVisibleOutcome
        (estimationAlgebra (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
          (coordinateObservations (VisibleHeads.planeRotation r s hrs) h)) := by
  have hex : ∃a b c : ℝ, (a≠0 ∨ b≠0 ∨ c≠0) ∧
      visibleBinaryQuadratic a b c∈polynomialFunctionElements f h ∧
      (ClassificationVisibleSingular f h ∨ a*c-b^2≠0) := by
    by_cases hs : ClassificationVisibleSingular f h
    · obtain ⟨a,b,c,hne,hq⟩ := actual_hidden_independent_visible_quadratic_witness
        f h hrank hx₀ hx₁ hHF p hp hpE
      exact ⟨a,b,c,hne,hq,Or.inl hs⟩
    · have hnon : ∃a b c : ℝ, visibleBinaryQuadratic a b c∈polynomialFunctionElements f h ∧
          a*c-b^2≠0 := by
        by_contra! hn
        apply hs
        intro a b c hq
        exact hn a b c hq
      obtain ⟨a,b,c,hq,hdet⟩ := hnon
      have hne : a≠0 ∨ b≠0 ∨ c≠0 := by
        by_contra! hz
        apply hdet
        simp [hz.1,hz.2.1,hz.2.2]
      exact ⟨a,b,c,hne,hq,Or.inr hdet⟩
  obtain ⟨a,b,c,hne,hq,hmode⟩ := hex
  have htail : classificationQuadraticTail a b c 0 0∈polynomialFunctionElements f h := by
    simpa [classificationQuadraticTail] using hq
  obtain ⟨r,s,hrs,A,B,hA,hdet,hdiag⟩ :=
    actual_classification_visible_diagonalization f h a b c 0 htail
  let e := VisibleHeads.planeRotation r s hrs
  let fe := coordinateDrift e f
  let heobs := coordinateObservations e h
  have he : CoordinateOrthogonal e := VisibleHeads.planeRotation_orthogonal r s hrs
  letI : FiniteDimensional ℝ (estimationAlgebra fe heobs) :=
    finiteDimensional_coordinateEstimationAlgebra e he f h
  have hranke : linearRank (estimationAlgebra fe heobs)=2 :=
    (linearRank_coordinateEstimationAlgebra e he f h).trans hrank
  have hx₀e : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra fe heobs :=
    VisibleHeads.planeRotation_coordinate_mem r s hrs f h hx₀ hx₁ 0 (Or.inl rfl)
  have hx₁e : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra fe heobs :=
    VisibleHeads.planeRotation_coordinate_mem r s hrs f h hx₀ hx₁ 1 (Or.inr rfl)
  have he₂ : e (coordinateVector 2)=coordinateVector 2 := by
    funext i
    fin_cases i <;> simp [e,VisibleHeads.planeRotation_apply,coordinateVector]
  have hHFe : HiddenIndependentFunctionSpace (estimationAlgebra fe heobs) :=
    HiddenIndependent.coordinate_model_hiddenIndependent e he he₂ f h hHF
  refine ⟨r,s,hrs,inferInstance,hranke,hx₀e,hx₁e,hHFe,?_⟩
  change ClassificationVisibleOutcome (estimationAlgebra fe heobs)
  rcases hmode with hsing | hnon
  · right
    have hAne : A≠0 := hA hne
    have hB : B=0 := by
      have hz : A*B=0 := hdet.trans (hsing a b c hq)
      exact (mul_eq_zero.mp hz).resolve_left hAne
    have hsquare : classificationDiagonalQuadratic 1 0 0∈polynomialFunctionElements fe heobs := by
      have heq : classificationDiagonalQuadratic 1 0 0=
          A⁻¹•classificationDiagonalQuadratic A B 0 := by
        apply MvPolynomial.funext
        intro x
        simp [classificationDiagonalQuadratic,smul_eq_C_mul,hB]
        field_simp [hAne]
      rw [heq]
      exact (polynomialFunctionElements fe heobs).smul_mem _ hdiag
    exact actual_classification_c2_of_all_visible_singular fe heobs hranke hx₀e hx₁e
      hHFe hsquare (classification_visible_singular_rotation f h hsing r s hrs)
  · left
    have hAB : A*B≠0 := by simpa only [hdet] using hnon
    have ha := (mul_ne_zero_iff.mp hAB).1
    have hb := (mul_ne_zero_iff.mp hAB).2
    exact classification_visible_radial_mem (polynomialFunctionElements fe heobs)
      (polynomialFunctionElements_gradient_pair_closed fe heobs) A B ha hb hdiag


def ClassificationVisibleHessianFree (E : LieSubalgebra ℝ Operator) : Prop :=
  ∀u : Smooth, multiplication u∈E → ∀i j : Fin 3, i≠2 → j≠2 →
    partialDerivative i (partialDerivative j u)=0

def ClassificationHiddenRadialOutcome (E : LieSubalgebra ℝ Operator) : Prop :=
  multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 0 1))∈E ∨
    multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 1 1))∈E

/-- The missing whole-A refinement: a mere hidden-square member gives either
the required whole-function visible-Hessian condition, or a further actual
visible rotation with a genuine B2/B1 member. -/
theorem actual_hidden_square_refined_model {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (ht : classificationDiagonalQuadratic 0 0 1∈polynomialFunctionElements f h) :
    ClassificationVisibleHessianFree (estimationAlgebra f h) ∨
    ∃(r s : ℝ) (hrs : r^2+s^2=1),
      FiniteDimensional ℝ (estimationAlgebra
        (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
        (coordinateObservations (VisibleHeads.planeRotation r s hrs) h)) ∧
      linearRank (estimationAlgebra (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
        (coordinateObservations (VisibleHeads.planeRotation r s hrs) h))=2 ∧
      multiplication (linearFunction (coordinateVector 0))∈
        estimationAlgebra (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
          (coordinateObservations (VisibleHeads.planeRotation r s hrs) h) ∧
      multiplication (linearFunction (coordinateVector 1))∈
        estimationAlgebra (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
          (coordinateObservations (VisibleHeads.planeRotation r s hrs) h) ∧
      ClassificationHiddenRadialOutcome
        (estimationAlgebra (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
          (coordinateObservations (VisibleHeads.planeRotation r s hrs) h)) := by
  by_cases hfree : ClassificationVisibleHessianFree (estimationAlgebra f h)
  · exact Or.inl hfree
  right
  change ¬(∀u : Smooth, multiplication u∈estimationAlgebra f h → ∀i j : Fin 3,
    i≠2 → j≠2 → partialDerivative i (partialDerivative j u)=0) at hfree
  push Not at hfree
  obtain ⟨u,hu,i,j,hi,hj,hij⟩ := hfree
  obtain ⟨a,b,c,d,g,ell₀,ell₁,t,hq,hrep,_⟩ :=
    actual_function_quadratic_tail_representation f h hrank hx₀ hx₁ u hu
  obtain ⟨_hg,hvis⟩ := actual_classification_visible_part_of_hidden_square
    f h hrank hx₀ hx₁ ht a b c d g hq
  have hne : a≠0 ∨ b≠0 ∨ c≠0 := by
    by_contra! hz
    rcases hz with ⟨ha,hb,hc⟩
    apply hij
    rw [hrep]
    simp only [map_add,map_smul,partialDerivative_linearFunction,
      partialDerivative_polynomialSmooth]
    fin_cases i <;> fin_cases j <;>
      simp_all [classificationQuadraticTail,visibleBinaryQuadratic,
        pderiv_X,polynomialSmooth,coordinateVector] <;> rfl
  have htail : classificationQuadraticTail a b c 0 0∈polynomialFunctionElements f h := by
    simpa [classificationQuadraticTail] using hvis
  obtain ⟨r,s,hrs,A,B,hA,_,hdiag⟩ :=
    actual_classification_visible_diagonalization f h a b c 0 htail
  let e := VisibleHeads.planeRotation r s hrs
  let fe := coordinateDrift e f
  let heobs := coordinateObservations e h
  let E := estimationAlgebra fe heobs
  let S := polynomialFunctionElements fe heobs
  have he : CoordinateOrthogonal e := VisibleHeads.planeRotation_orthogonal r s hrs
  letI : FiniteDimensional ℝ E := finiteDimensional_coordinateEstimationAlgebra e he f h
  have hranke : linearRank E=2 := (linearRank_coordinateEstimationAlgebra e he f h).trans hrank
  have hx₀e : multiplication (linearFunction (coordinateVector 0))∈E :=
    VisibleHeads.planeRotation_coordinate_mem r s hrs f h hx₀ hx₁ 0 (Or.inl rfl)
  have hx₁e : multiplication (linearFunction (coordinateVector 1))∈E :=
    VisibleHeads.planeRotation_coordinate_mem r s hrs f h hx₀ hx₁ 1 (Or.inr rfl)
  have htE : classificationDiagonalQuadratic 0 0 1∈S := by
    have himage := (multiplication_pullback_mem_coordinateAlgebra e (estimationAlgebra f h)
      (polynomialSmooth (classificationDiagonalQuadratic 0 0 1))).mpr ht
    rw [coordinateAlgebra_estimationAlgebra e he] at himage
    have hshape : coordinatePullback e (polynomialSmooth (classificationDiagonalQuadratic 0 0 1))=
        polynomialSmooth (classificationDiagonalQuadratic 0 0 1) := by
      apply Subtype.ext
      funext x
      simp [e,coordinatePullback_apply,VisibleHeads.planeRotation_apply,
        polynomialSmooth,classificationDiagonalQuadratic]
    rw [hshape] at himage
    exact himage
  refine ⟨r,s,hrs,inferInstance,hranke,hx₀e,hx₁e,?_⟩
  change ClassificationHiddenRadialOutcome E
  have hAne : A≠0 := hA hne
  by_cases hB : B=0
  · left
    have hsquare : classificationDiagonalQuadratic 1 0 0∈S := by
      have heq : classificationDiagonalQuadratic 1 0 0=A⁻¹•classificationDiagonalQuadratic A B 0 := by
        apply MvPolynomial.funext
        intro x
        simp [classificationDiagonalQuadratic,smul_eq_C_mul,hB]
        field_simp [hAne]
      rw [heq]
      exact S.smul_mem _ hdiag
    have heq : classificationDiagonalQuadratic 1 0 1=
        classificationDiagonalQuadratic 1 0 0+classificationDiagonalQuadratic 0 0 1 := by
      simp [classificationDiagonalQuadratic]
    rw [heq]
    exact S.add_mem hsquare htE
  · right
    have hradial : classificationDiagonalQuadratic 1 1 0∈S :=
      classification_visible_radial_mem S (polynomialFunctionElements_gradient_pair_closed fe heobs)
        A B hAne hB hdiag
    have heq : classificationDiagonalQuadratic 1 1 1=
        classificationDiagonalQuadratic 1 1 0+classificationDiagonalQuadratic 0 0 1 := by
      simp [classificationDiagonalQuadratic]
    rw [heq]
    exact S.add_mem hradial htE


/-- A quarter-turn exchanges the two visible squares and leaves the hidden
square fixed, within the actual orthogonally transformed filtering model. -/
theorem actual_classification_other_B2_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hq : classificationDiagonalQuadratic 0 1 1∈polynomialFunctionElements f h) :
    classificationDiagonalQuadratic 1 0 1∈polynomialFunctionElements
      (coordinateDrift (VisibleHeads.planeRotation 0 1 (by norm_num)) f)
      (coordinateObservations (VisibleHeads.planeRotation 0 1 (by norm_num)) h) := by
  let e := VisibleHeads.planeRotation 0 1 (by norm_num)
  have he : CoordinateOrthogonal e := VisibleHeads.planeRotation_orthogonal 0 1 (by norm_num)
  have himage := (multiplication_pullback_mem_coordinateAlgebra e (estimationAlgebra f h)
    (polynomialSmooth (classificationDiagonalQuadratic 0 1 1))).mpr hq
  rw [coordinateAlgebra_estimationAlgebra e he] at himage
  have hshape : coordinatePullback e (polynomialSmooth (classificationDiagonalQuadratic 0 1 1))=
      polynomialSmooth (classificationDiagonalQuadratic 1 0 1) := by
    apply Subtype.ext
    funext x
    simp [e,coordinatePullback_apply,VisibleHeads.planeRotation_apply,
      polynomialSmooth,classificationDiagonalQuadratic]
  rw [hshape] at himage
  exact himage

/-- The actual five-case conclusion. A and C2 include their necessary whole
function-space restrictions. B1/B2/C1 assert genuine quadratic members. -/
def ClassificationModelCase {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth) : Prop :=
  (classificationDiagonalQuadratic 0 0 1∈polynomialFunctionElements f h ∧
      ClassificationVisibleHessianFree (estimationAlgebra f h)) ∨
  classificationDiagonalQuadratic 1 0 1∈polynomialFunctionElements f h ∨
  classificationDiagonalQuadratic 1 1 1∈polynomialFunctionElements f h ∨
  (HiddenIndependentFunctionSpace (estimationAlgebra f h) ∧
      classificationDiagonalQuadratic 1 1 0∈polynomialFunctionElements f h) ∨
  HiddenIndependent.C2FunctionSpace (estimationAlgebra f h)

/-- Affine function elements have zero genuine second derivatives. -/
theorem classification_affine_function_second_partial_zero
    (E : LieSubalgebra ℝ Operator) (hE : FunctionElementsAffine E)
    (u : Smooth) (hu : multiplication u∈E) (i j : Fin 3) :
    partialDerivative i (partialDerivative j u)=0 := by
  obtain ⟨p,hp,hpu⟩ := hE u hu
  obtain ⟨c,b,hpaff⟩ := polynomialSmooth_exists_affine_of_degree_le_one p hp
  rw [←hpu,hpaff]
  simp only [map_add,partialDerivative_const,partialDerivative_linearFunction,
    zero_add]

/-- The canonical diagonal members retain their actual nonzero Hessian. -/
theorem classification_diagonal_second_partial (a b c : ℝ) (i : Fin 3) :
    partialDerivative i (partialDerivative i
      (polynomialSmooth (classificationDiagonalQuadratic a b c)))=
      (2*(![a,b,c] i))•smoothOne := by
  have htwo (j : Fin 3) : pderiv j (2 : RealPoly)=0 := by
    rw [show (2 : RealPoly)=1+1 by norm_num,map_add,pderiv_one,zero_add]
  simp only [partialDerivative_polynomialSmooth]
  apply Subtype.ext
  funext x
  fin_cases i <;>
    simp [classificationDiagonalQuadratic,htwo,polynomialSmooth,smoothOne] <;> ring

/-- Each complete case contains a genuinely non-affine function member;
this includes the square explicitly present in the whole-C2 definition. -/
theorem classification_model_case_not_functionElementsAffine {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hcase : ClassificationModelCase f h) :
    ¬FunctionElementsAffine (estimationAlgebra f h) := by
  intro hE
  have hh : ∀a b : ℝ,
      classificationDiagonalQuadratic a b 1∈polynomialFunctionElements f h → False := by
    intro a b hu
    have hz := classification_affine_function_second_partial_zero _ hE
      (polynomialSmooth (classificationDiagonalQuadratic a b 1)) hu 2 2
    rw [classification_diagonal_second_partial] at hz
    have hv := congrArg (fun u : Smooth => u.1 (0 : State)) hz
    norm_num [smoothOne] at hv
  have hv : ∀b c : ℝ,
      classificationDiagonalQuadratic 1 b c∈polynomialFunctionElements f h → False := by
    intro b c hu
    have hz := classification_affine_function_second_partial_zero _ hE
      (polynomialSmooth (classificationDiagonalQuadratic 1 b c)) hu 0 0
    rw [classification_diagonal_second_partial] at hz
    have hval := congrArg (fun u : Smooth => u.1 (0 : State)) hz
    norm_num [smoothOne] at hval
  rcases hcase with hA | hB2 | hB1 | hC1 | hC2
  · exact hh 0 0 hA.1
  · exact hh 1 0 hB2
  · exact hh 1 1 hB1
  · exact hv 1 0 hC1.2
  · have hshape : polynomialSmooth (classificationDiagonalQuadratic 1 0 0)=
        smoothMul (linearFunction (coordinateVector 0)) (linearFunction (coordinateVector 0)) := by
      apply Subtype.ext
      funext x
      simp [classificationDiagonalQuadratic,polynomialSmooth,smoothMul,linearFunction,
        coordinateVector,pow_two,Fin.sum_univ_three]
    apply hv 0 0
    change multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 0 0))∈
      estimationAlgebra f h
    rw [hshape]
    exact hC2.1

/-- Complete actual quadratic-function case reduction. Every witness model
in this proof is explicitly obtained by the proved translations and visible
orthogonal rotations of the input model. No case restriction is a premise. -/
theorem actual_quadratic_function_cases {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (p : RealPoly) (hp : p.totalDegree=2) (hpE : p∈polynomialFunctionElements f h) :
    ∃(f' : Fin 3 → Smooth) (h' : Fin m → Smooth),
      FiniteDimensional ℝ (estimationAlgebra f' h') ∧ linearRank (estimationAlgebra f' h')=2 ∧
      multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f' h' ∧
      multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f' h' ∧
      ClassificationModelCase f' h' := by
  by_cases hhidden : ∀u : Smooth, multiplication u∈estimationAlgebra f h →
      partialDerivative 2 (partialDerivative 2 u)=0
  · have hHF := function_elements_hidden_independent_of_hidden_second_partials_zero
      f h hrank hx₀ hx₁ hhidden
    obtain ⟨r,s,hrs,hfd,hr,hx0,hx1,hHF',hcase⟩ :=
      actual_hidden_independent_quadratic_model f h hrank hx₀ hx₁ hHF p hp hpE
    refine ⟨coordinateDrift (VisibleHeads.planeRotation r s hrs) f,
      coordinateObservations (VisibleHeads.planeRotation r s hrs) h,hfd,hr,hx0,hx1,?_⟩
    rcases hcase with hrad | hC2
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hHF',hrad⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hC2)))
  · push_neg at hhidden
    obtain ⟨u,hu,hzz⟩ := hhidden
    obtain ⟨z,e,_he,hfd,hr,hx0,hx1,hprojection⟩ :=
      actual_hidden_curvature_projection_model f h hrank hx₀ hx₁ u hu hzz
    let f₁ := coordinateDrift e (translationDrift z f)
    let h₁ := coordinateObservations e (translationObservations z h)
    letI : FiniteDimensional ℝ (estimationAlgebra f₁ h₁) := hfd
    change ClassificationHiddenProjection (estimationAlgebra f₁ h₁) at hprojection
    rcases hprojection with ht | hB20 | hB21 | hB1
    · rcases actual_hidden_square_refined_model f₁ h₁ hr hx0 hx1 ht with hA | hmore
      · exact ⟨f₁,h₁,hfd,hr,hx0,hx1,Or.inl ⟨ht,hA⟩⟩
      · obtain ⟨r,s,hrs,hfd₂,hr₂,hx0₂,hx1₂,hcase₂⟩ := hmore
        refine ⟨coordinateDrift (VisibleHeads.planeRotation r s hrs) f₁,
          coordinateObservations (VisibleHeads.planeRotation r s hrs) h₁,
          hfd₂,hr₂,hx0₂,hx1₂,?_⟩
        rcases hcase₂ with hB2 | hB1
        · exact Or.inr (Or.inl hB2)
        · exact Or.inr (Or.inr (Or.inl hB1))
    · exact ⟨f₁,h₁,hfd,hr,hx0,hx1,Or.inr (Or.inl hB20)⟩
    · let e₂ := VisibleHeads.planeRotation 0 1 (by norm_num)
      have he₂ : CoordinateOrthogonal e₂ := VisibleHeads.planeRotation_orthogonal 0 1 (by norm_num)
      refine ⟨coordinateDrift e₂ f₁,coordinateObservations e₂ h₁,
        finiteDimensional_coordinateEstimationAlgebra e₂ he₂ f₁ h₁,
        (linearRank_coordinateEstimationAlgebra e₂ he₂ f₁ h₁).trans hr,
        VisibleHeads.planeRotation_coordinate_mem 0 1 (by norm_num) f₁ h₁ hx0 hx1 0 (Or.inl rfl),
        VisibleHeads.planeRotation_coordinate_mem 0 1 (by norm_num) f₁ h₁ hx0 hx1 1 (Or.inr rfl),
        Or.inr (Or.inl (actual_classification_other_B2_mem f₁ h₁ hB21))⟩
    · exact ⟨f₁,h₁,hfd,hr,hx0,hx1,Or.inr (Or.inr (Or.inl hB1))⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.classification_visible_singular_rotation
#print axioms Wong.SmoothModel.actual_hidden_independent_visible_quadratic_witness

#print axioms Wong.SmoothModel.actual_hidden_independent_quadratic_model

#print axioms Wong.SmoothModel.actual_hidden_square_refined_model

#print axioms Wong.SmoothModel.actual_quadratic_function_cases

#print axioms Wong.SmoothModel.classification_model_case_not_functionElementsAffine
