import Wong.QuadraticHiddenLinearTail
import Wong.FunctionHiddenIndependence
import Wong.RootAnalyticBridges
import Wong.SectorTwoDiagonalization
import Wong.HiddenIndependentSectors

/-! Explicit finite gradient filters for quadratic function classification.
All membership conclusions concern the genuine polynomial function-element
submodule.  Coordinate normalization is a separate actual-model bridge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Wong.SmoothModel
open MvPolynomial

def classificationDiagonalQuadratic (a b c : ℝ) : RealPoly :=
  C a*X 0^2+C b*X 1^2+C c*X 2^2

theorem classificationDiagonalQuadratic_gradient (a b c d e g : ℝ) :
    quadraticGradientPair (classificationDiagonalQuadratic a b c)
      (classificationDiagonalQuadratic d e g)=
      classificationDiagonalQuadratic (4*a*d) (4*b*e) (4*c*g) := by
  apply MvPolynomial.funext
  intro x
  simp [quadraticGradientPair,classificationDiagonalQuadratic,
    Fin.sum_univ_three,pderiv_X]
  ring

theorem classificationDiagonalQuadratic_square_mem (S : Submodule ℝ RealPoly)
    (hΓ : ∀{p q : RealPoly}, p∈S → q∈S → quadraticGradientPair p q∈S)
    (a b c : ℝ) (hq : classificationDiagonalQuadratic a b c∈S) :
    classificationDiagonalQuadratic (a^2) (b^2) (c^2)∈S := by
  have he : classificationDiagonalQuadratic (a^2) (b^2) (c^2)=
      (1/4 : ℝ)•quadraticGradientPair (classificationDiagonalQuadratic a b c)
        (classificationDiagonalQuadratic a b c) := by
    rw [classificationDiagonalQuadratic_gradient]
    apply MvPolynomial.funext
    intro x
    simp [classificationDiagonalQuadratic,smul_eq_C_mul]
    ring
  rw [he]
  exact S.smul_mem _ (hΓ hq hq)

theorem classificationDiagonalQuadratic_cube_mem (S : Submodule ℝ RealPoly)
    (hΓ : ∀{p q : RealPoly}, p∈S → q∈S → quadraticGradientPair p q∈S)
    (a b c : ℝ) (hq : classificationDiagonalQuadratic a b c∈S) :
    classificationDiagonalQuadratic (a^3) (b^3) (c^3)∈S := by
  have he : classificationDiagonalQuadratic (a^3) (b^3) (c^3)=
      (1/4 : ℝ)•quadraticGradientPair (classificationDiagonalQuadratic a b c)
        (classificationDiagonalQuadratic (a^2) (b^2) (c^2)) := by
    rw [classificationDiagonalQuadratic_gradient]
    apply MvPolynomial.funext
    intro x
    simp [classificationDiagonalQuadratic,smul_eq_C_mul]
    ring
  rw [he]
  exact S.smul_mem _ (hΓ hq (classificationDiagonalQuadratic_square_mem S hΓ a b c hq))

/-- The hidden eigenspace is extracted using at most three genuine gradient
words.  Repeated eigenvalues and zero visible eigenvalues are included. -/
theorem classification_hidden_projection_mem (S : Submodule ℝ RealPoly)
    (hΓ : ∀{p q : RealPoly}, p∈S → q∈S → quadraticGradientPair p q∈S)
    (a b c : ℝ) (hc : c≠0) (hq : classificationDiagonalQuadratic a b c∈S) :
    classificationDiagonalQuadratic 0 0 1∈S ∨
    classificationDiagonalQuadratic 1 0 1∈S ∨
    classificationDiagonalQuadratic 0 1 1∈S ∨
    classificationDiagonalQuadratic 1 1 1∈S := by
  have hF := classificationDiagonalQuadratic_square_mem S hΓ a b c hq
  have hG := classificationDiagonalQuadratic_cube_mem S hΓ a b c hq
  by_cases ha : a=c
  · subst a
    by_cases hb : b=c
    · subst b
      right; right; right
      have he : classificationDiagonalQuadratic 1 1 1=
          c⁻¹•classificationDiagonalQuadratic c c c := by
        apply MvPolynomial.funext
        intro x
        simp [classificationDiagonalQuadratic,smul_eq_C_mul]
        field_simp [hc]
      rw [he]
      exact S.smul_mem _ hq
    · right; left
      have hcb : c-b≠0 := sub_ne_zero.mpr (Ne.symm hb)
      have he : classificationDiagonalQuadratic 1 0 1=
          (c*(c-b))⁻¹•(classificationDiagonalQuadratic (c^2) (b^2) (c^2)-
            b•classificationDiagonalQuadratic c b c) := by
        apply MvPolynomial.funext
        intro x
        simp [classificationDiagonalQuadratic,smul_eq_C_mul]
        field_simp [hc,hcb]; ring
      rw [he]
      exact S.smul_mem _ (S.sub_mem hF (S.smul_mem _ hq))
  · by_cases hb : b=c
    · subst b
      right; right; left
      have hca : c-a≠0 := sub_ne_zero.mpr (Ne.symm ha)
      have he : classificationDiagonalQuadratic 0 1 1=
          (c*(c-a))⁻¹•(classificationDiagonalQuadratic (a^2) (c^2) (c^2)-
            a•classificationDiagonalQuadratic a c c) := by
        apply MvPolynomial.funext
        intro x
        simp [classificationDiagonalQuadratic,smul_eq_C_mul]
        field_simp [hc,hca]; ring
      rw [he]
      exact S.smul_mem _ (S.sub_mem hF (S.smul_mem _ hq))
    · left
      have hca : c-a≠0 := sub_ne_zero.mpr (Ne.symm ha)
      have hcb : c-b≠0 := sub_ne_zero.mpr (Ne.symm hb)
      have he : classificationDiagonalQuadratic 0 0 1=
          (c*(c-a)*(c-b))⁻¹•(classificationDiagonalQuadratic (a^3) (b^3) (c^3)-
            (a+b)•classificationDiagonalQuadratic (a^2) (b^2) (c^2)+
            (a*b)•classificationDiagonalQuadratic a b c) := by
        apply MvPolynomial.funext
        intro x
        simp [classificationDiagonalQuadratic,smul_eq_C_mul]
        field_simp [hc,hca,hcb]; ring
      rw [he]
      exact S.smul_mem _ (S.add_mem (S.sub_mem hG (S.smul_mem _ hF)) (S.smul_mem _ hq))

/-- A nonsingular visible quadratic produces the actual visible radial
quadratic, including repeated or oppositely signed nonzero eigenvalues. -/
theorem classification_visible_radial_mem (S : Submodule ℝ RealPoly)
    (hΓ : ∀{p q : RealPoly}, p∈S → q∈S → quadraticGradientPair p q∈S)
    (a b : ℝ) (ha : a≠0) (hb : b≠0)
    (hq : classificationDiagonalQuadratic a b 0∈S) :
    classificationDiagonalQuadratic 1 1 0∈S := by
  have hF := classificationDiagonalQuadratic_square_mem S hΓ a b 0 hq
  have he : classificationDiagonalQuadratic 1 1 0=
      (a*b)⁻¹•((a+b)•classificationDiagonalQuadratic a b 0-
        classificationDiagonalQuadratic (a^2) (b^2) (0^2)) := by
    apply MvPolynomial.funext
    intro x
    simp [classificationDiagonalQuadratic,smul_eq_C_mul]
    field_simp [ha,hb]; ring
  rw [he]
  exact S.smul_mem _ (S.sub_mem (S.smul_mem _ hq) hF)

/-- The entire singular quadratic subspace shares the selected rank-one axis.
Both B and A+B must be singular; one admitted square alone is insufficient. -/
theorem classification_singular_binary_common_axis (lam a b c : ℝ)
    (hlam : lam≠0) (hB : a*c-b^2=0) (hAB : (lam+a)*c-b^2=0) :
    b=0 ∧ c=0 := by
  have he : lam*c=0 := by nlinarith [hB,hAB]
  have hc : c=0 := (mul_eq_zero.mp he).resolve_left hlam
  have hb : b=0 := by rw [hc] at hB; nlinarith [sq_nonneg b]
  exact ⟨hb,hc⟩

/-- Specialization to genuine multipliers and the actual double commutator. -/
theorem actual_classification_hidden_projection_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (a b c : ℝ) (hc : c≠0)
    (hq : classificationDiagonalQuadratic a b c∈polynomialFunctionElements f h) :
    classificationDiagonalQuadratic 0 0 1∈polynomialFunctionElements f h ∨
    classificationDiagonalQuadratic 1 0 1∈polynomialFunctionElements f h ∨
    classificationDiagonalQuadratic 0 1 1∈polynomialFunctionElements f h ∨
    classificationDiagonalQuadratic 1 1 1∈polynomialFunctionElements f h :=
  classification_hidden_projection_mem (polynomialFunctionElements f h)
    (polynomialFunctionElements_gradient_pair_closed f h) a b c hc hq


/-- A hidden linear term is retained until a genuine translation or rank
argument removes it.  Only admitted visible affine terms are separated. -/
def classificationQuadraticTail (a b c d g : ℝ) : RealPoly :=
  visibleBinaryQuadratic a b c+C d*X 2^2+C g*X 2

/-- Actual smooth normal form for every function element in adapted rank two.
The displayed quadratic-with-hidden-tail is itself a genuine member, and the
remaining terms are exactly admitted visible affine functions. -/
theorem actual_function_quadratic_tail_representation {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u∈estimationAlgebra f h) :
    ∃a b c d g ell₀ ell₁ r : ℝ,
      classificationQuadraticTail a b c d g∈polynomialFunctionElements f h ∧
      u=polynomialSmooth (classificationQuadraticTail a b c d g)+
        ell₀•linearFunction (coordinateVector 0)+ell₁•linearFunction (coordinateVector 1)+
        r•smoothOne ∧
      partialDerivative 2 (partialDerivative 2 u)=(2*d)•smoothOne := by
  obtain ⟨c₀,a₀,h₀⟩ := function_element_partial_affine f h u hu 0
  obtain ⟨c₁,a₁,h₁⟩ := function_element_partial_affine f h u hu 1
  obtain ⟨hz₀,hz₁⟩ := function_element_visible_hidden_mixed_partials f h hrank hx₀ hx₁ u hu
  have ha₀ : a₀ 2=0 := by
    rw [h₀,map_add,partialDerivative_const,partialDerivative_linearFunction,zero_add] at hz₀
    simpa [smoothOne] using congrArg (fun v : Smooth => v.1 (0 : State)) hz₀
  have ha₁ : a₁ 2=0 := by
    rw [h₁,map_add,partialDerivative_const,partialDerivative_linearFunction,zero_add] at hz₁
    simpa [smoothOne] using congrArg (fun v : Smooth => v.1 (0 : State)) hz₁
  have hcross : a₁ 0=a₀ 1 := by
    have he := partialDerivative_commute_apply 0 1 u
    simp only [h₀,h₁,map_add,partialDerivative_const,partialDerivative_linearFunction,zero_add] at he
    simpa [smoothOne] using congrArg (fun v : Smooth => v.1 (0 : State)) he
  obtain ⟨g,k,hhidden⟩ := function_element_hidden_partial_affine_hidden f h hrank hx₀ hx₁ u hu
  let q := classificationQuadraticTail (a₀ 0/2) (a₀ 1/2) (a₁ 1/2) (k/2) g
  have hq₀ : partialDerivative 0 (polynomialSmooth q)=linearFunction a₀ := by
    rw [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    simp [q,classificationQuadraticTail,visibleBinaryQuadratic,polynomialSmooth,
      pderiv_X,linearFunction,Fin.sum_univ_three,ha₀]; ring
  have hq₁ : partialDerivative 1 (polynomialSmooth q)=linearFunction a₁ := by
    rw [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    simp [q,classificationQuadraticTail,visibleBinaryQuadratic,polynomialSmooth,
      pderiv_X,linearFunction,Fin.sum_univ_three,ha₁,hcross]; ring
  have hq₂ : partialDerivative 2 (polynomialSmooth q)=
      g•smoothOne+k•linearFunction (coordinateVector 2) := by
    rw [partialDerivative_polynomialSmooth]
    apply Subtype.ext
    funext x
    simp [q,classificationQuadraticTail,visibleBinaryQuadratic,polynomialSmooth,
      pderiv_X,smoothOne,linearFunction,Fin.sum_univ_three,coordinateVector]; ring
  let w := u-polynomialSmooth q-c₀•linearFunction (coordinateVector 0)-
    c₁•linearFunction (coordinateVector 1)
  have hwpartials : ∀i : Fin 3, partialDerivative i w=0 := by
    intro i
    fin_cases i <;>
      simp [w,map_sub,map_smul,partialDerivative_linearFunction,h₀,h₁,hhidden,
        hq₀,hq₁,hq₂,coordinateVector]
  obtain ⟨r,hr⟩ := (smooth_constant_iff_partials_zero w).mpr hwpartials
  have hw : w=r•smoothOne := by
    apply Subtype.ext
    funext x
    simpa [smoothOne] using hr x
  have heq : u-c₀•linearFunction (coordinateVector 0)-
      c₁•linearFunction (coordinateVector 1)-r•smoothOne=polynomialSmooth q := by
    calc
      _ = polynomialSmooth q+(w-r•smoothOne) := by dsimp [w]; abel
      _ = _ := by rw [hw]; simp
  have hqE : q∈polynomialFunctionElements f h := by
    change multiplication (polynomialSmooth q)∈estimationAlgebra f h
    rw [← heq,multiplication_sub,multiplication_sub,multiplication_sub,multiplication_smul,
      multiplication_smul,multiplication_smul]
    exact (estimationAlgebra f h).sub_mem
      ((estimationAlgebra f h).sub_mem
        ((estimationAlgebra f h).sub_mem hu ((estimationAlgebra f h).smul_mem c₀ hx₀))
        ((estimationAlgebra f h).smul_mem c₁ hx₁))
      ((estimationAlgebra f h).smul_mem r (smoothOne_mem_estimationAlgebra_of_rank_two f h hrank))
  refine ⟨a₀ 0/2,a₀ 1/2,a₁ 1/2,k/2,g,c₀,c₁,r,hqE,?_,?_⟩
  · change u=polynomialSmooth q+c₀•linearFunction (coordinateVector 0)+
        c₁•linearFunction (coordinateVector 1)+r•smoothOne
    rw [← heq]
    abel
  · rw [hhidden,map_add,partialDerivative_const,map_smul,partialDerivative_linearFunction]
    have hk : (2 : ℝ)*(k/2)=k := by ring
    simp [coordinateVector,hk]


/-- The true pullback uses x+b; the negative sign completes the hidden square. -/
def classificationHiddenCenter (d g : ℝ) : State :=
  (-g/(2*d))•coordinateVector 2

theorem classification_hidden_center_pullback (a b c d g : ℝ) (hd : d≠0) :
    translationPullback (classificationHiddenCenter d g)
      (polynomialSmooth (classificationQuadraticTail a b c d g))=
      polynomialSmooth (classificationQuadraticTail a b c d 0)-
        (g^2/(4*d))•smoothOne := by
  apply Subtype.ext
  funext x
  simp [translationPullback,affinePullback_apply,classificationHiddenCenter,
    classificationQuadraticTail,visibleBinaryQuadratic,polynomialSmooth,
    coordinateVector,smoothOne]
  field_simp [hd]; ring

/-- Completing the hidden square transports the original filtering model and
subtracts only an admitted constant in its actual translated algebra. -/
theorem actual_classification_hidden_center_mem {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h)=2)
    (a b c d g : ℝ) (hd : d≠0)
    (hq : classificationQuadraticTail a b c d g∈polynomialFunctionElements f h) :
    classificationQuadraticTail a b c d 0∈polynomialFunctionElements
      (translationDrift (classificationHiddenCenter d g) f)
      (translationObservations (classificationHiddenCenter d g) h) := by
  let z := classificationHiddenCenter d g
  let E := estimationAlgebra (translationDrift z f) (translationObservations z h)
  have himage : multiplication (translationPullback z
      (polynomialSmooth (classificationQuadraticTail a b c d g)))∈E := by
    change multiplication (translationPullback z
      (polynomialSmooth (classificationQuadraticTail a b c d g)))∈
      estimationAlgebra (translationDrift z f) (translationObservations z h)
    rw [← translationAlgebra_estimationAlgebra,multiplication_mem_affineAlgebra_iff]
    change multiplication ((translationPullback z).symm (translationPullback z
      (polynomialSmooth (classificationQuadraticTail a b c d g))))∈estimationAlgebra f h
    rw [LinearEquiv.symm_apply_apply]
    exact hq
  have hshape := classification_hidden_center_pullback a b c d g hd
  change translationPullback z (polynomialSmooth (classificationQuadraticTail a b c d g))=_
    at hshape
  rw [hshape,multiplication_sub,multiplication_smul] at himage
  have hconstant : multiplication ((g^2/(4*d))•smoothOne)∈E := by
    rw [multiplication_smul]
    exact E.smul_mem _ (smoothOne_mem_estimationAlgebra_of_rank_two _ _
      (linearRank_translationEstimationAlgebra z f h hrank))
  rw [multiplication_smul] at hconstant
  have hsum := E.add_mem himage hconstant
  change multiplication (polynomialSmooth (classificationQuadraticTail a b c d 0))∈E
  simpa only [sub_add_cancel] using hsum


/-- A genuine visible rotation diagonalizes every binary real quadratic.
The hidden square is fixed; the determinant and nonzero visible mode are
recorded for the later exhaustive rank-two/rank-one split. -/
theorem classification_visible_diagonalization (a b c : ℝ) :
    ∃(r s : ℝ) (hrs : r^2+s^2=1) (A B : ℝ),
      ((a≠0 ∨ b≠0 ∨ c≠0) → A≠0) ∧ A*B=a*c-b^2 ∧
      ∀d : ℝ, coordinatePullback (VisibleHeads.planeRotation r s hrs)
        (polynomialSmooth (classificationQuadraticTail a b c d 0))=
        polynomialSmooth (classificationDiagonalQuadratic A B d) := by
  by_cases hz : a=0 ∧ b=0 ∧ c=0
  · rcases hz with ⟨rfl,rfl,rfl⟩
    refine ⟨1,0,by norm_num,0,0,by tauto,by ring,?_⟩
    intro d
    apply Subtype.ext
    funext x
    simp [coordinatePullback_apply,VisibleHeads.planeRotation_apply,
      classificationQuadraticTail,classificationDiagonalQuadratic,visibleBinaryQuadratic,
      polynomialSmooth]
  · have hne : a≠0 ∨ b≠0 ∨ c≠0 := by tauto
    obtain ⟨r,s,lam,hrs,hlam,h₀,h₁⟩ :=
      VisibleHeads.symmetric_two_nonzero_unit_eigenvector a b c hne
    let B := a*s^2+2*b*r*s+c*r^2
    have hA : a*r^2-2*b*r*s+c*s^2=lam := by
      linear_combination r*h₀-s*h₁+lam*hrs
    have hcross : a*r*s+b*(r^2-s^2)-c*r*s=0 := by
      linear_combination s*h₀+r*h₁
    have hdet : lam*B=a*c-b^2 := by
      calc
        lam*B=(a*r^2-2*b*r*s+c*s^2)*(a*s^2+2*b*r*s+c*r^2)-
            (a*r*s+b*(r^2-s^2)-c*r*s)^2 := by rw [hA,hcross]; dsimp [B]; ring
        _ = (a*c-b^2)*(r^2+s^2)^2 := by ring
        _ = a*c-b^2 := by rw [hrs]; ring
    refine ⟨r,s,hrs,lam,B,fun _ => hlam,hdet,?_⟩
    intro d
    apply Subtype.ext
    funext x
    simp only [coordinatePullback_apply]
    change eval (VisibleHeads.planeRotation r s hrs x)
        (classificationQuadraticTail a b c d 0)=
      eval x (classificationDiagonalQuadratic lam B d)
    simp [classificationQuadraticTail,classificationDiagonalQuadratic,visibleBinaryQuadratic,
      VisibleHeads.planeRotation_apply,B]
    linear_combination (x 0)^2*hA+(2*x 0*x 1)*hcross

/-- The diagonal quadratic remains an actual multiplier after the same
orthogonal pullback of the drift, observations, potential, and Lie algebra. -/
theorem actual_classification_visible_diagonalization {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) (a b c d : ℝ)
    (hq : classificationQuadraticTail a b c d 0∈polynomialFunctionElements f h) :
    ∃(r s : ℝ) (hrs : r^2+s^2=1) (A B : ℝ),
      ((a≠0 ∨ b≠0 ∨ c≠0) → A≠0) ∧ A*B=a*c-b^2 ∧
      classificationDiagonalQuadratic A B d∈polynomialFunctionElements
        (coordinateDrift (VisibleHeads.planeRotation r s hrs) f)
        (coordinateObservations (VisibleHeads.planeRotation r s hrs) h) := by
  obtain ⟨r,s,hrs,A,B,hA,hdet,hshape⟩ := classification_visible_diagonalization a b c
  refine ⟨r,s,hrs,A,B,hA,hdet,?_⟩
  let e := VisibleHeads.planeRotation r s hrs
  have he := VisibleHeads.planeRotation_orthogonal r s hrs
  have hmem := (multiplication_pullback_mem_coordinateAlgebra e (estimationAlgebra f h)
    (polynomialSmooth (classificationQuadraticTail a b c d 0))).mpr hq
  rw [coordinateAlgebra_estimationAlgebra e he] at hmem
  change multiplication (coordinatePullback (VisibleHeads.planeRotation r s hrs)
    (polynomialSmooth (classificationQuadraticTail a b c d 0)))∈_ at hmem
  rw [hshape d] at hmem
  exact hmem


/-- The whole-function C2 conclusion uses singularity of every actual visible
quadratic, including the sum with the admitted square.  It is not inferred
from the square member alone. -/
theorem actual_classification_c2_of_all_visible_singular {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (hHF : ∀u : Smooth, multiplication u∈estimationAlgebra f h → partialDerivative 2 u=0)
    (hsquare : classificationDiagonalQuadratic 1 0 0∈polynomialFunctionElements f h)
    (hsingular : ∀a b c : ℝ, visibleBinaryQuadratic a b c∈polynomialFunctionElements f h →
      a*c-b^2=0) : HiddenIndependent.C2FunctionSpace (estimationAlgebra f h) := by
  constructor
  · have he : polynomialSmooth (classificationDiagonalQuadratic 1 0 0)=
        smoothMul (linearFunction (coordinateVector 0)) (linearFunction (coordinateVector 0)) := by
      apply Subtype.ext
      funext x
      simp [classificationDiagonalQuadratic,polynomialSmooth,smoothMul,linearFunction,
        coordinateVector,pow_two,Fin.sum_univ_three]
    change multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 0 0))∈
      estimationAlgebra f h at hsquare
    rwa [he] at hsquare
  · intro u hu
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
    have hq' : visibleBinaryQuadratic a b c∈polynomialFunctionElements f h := by
      simpa [classificationQuadraticTail] using hq
    have hsquare' : visibleBinaryQuadratic 1 0 0∈polynomialFunctionElements f h := by
      simpa [classificationDiagonalQuadratic,visibleBinaryQuadratic] using hsquare
    have hsum : visibleBinaryQuadratic (1+a) b c∈polynomialFunctionElements f h := by
      have he : visibleBinaryQuadratic (1+a) b c=
          visibleBinaryQuadratic 1 0 0+visibleBinaryQuadratic a b c := by
        apply MvPolynomial.funext
        intro x
        simp [visibleBinaryQuadratic]
        ring
      rw [he]
      exact (polynomialFunctionElements f h).add_mem hsquare' hq'
    obtain ⟨hb,hc⟩ := classification_singular_binary_common_axis 1 a b c (by norm_num)
      (hsingular a b c hq') (hsingular (1+a) b c hsum)
    subst b
    subst c
    refine ⟨r,ell₀,ell₁,a,?_⟩
    rw [hrep]
    apply Subtype.ext
    funext x
    simp [classificationQuadraticTail,visibleBinaryQuadratic,polynomialSmooth,smoothMul,
      linearFunction,coordinateVector,smoothOne,Fin.sum_univ_three]
    ring


/-- Once the hidden square is genuinely admitted, it can be subtracted from
another function member. Gradient recovery then removes the hidden linear
tail by rank two, leaving the genuine visible quadratic for the B1/B2 split. -/
theorem actual_classification_visible_part_of_hidden_square {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (ht : classificationDiagonalQuadratic 0 0 1∈polynomialFunctionElements f h)
    (a b c d g : ℝ)
    (hq : classificationQuadraticTail a b c d g∈polynomialFunctionElements f h) :
    g=0 ∧ visibleBinaryQuadratic a b c∈polynomialFunctionElements f h := by
  have he : classificationQuadraticTail a b c d g-
      d•classificationDiagonalQuadratic 0 0 1=visibleBinaryQuadratic a b c+C g*X 2 := by
    apply MvPolynomial.funext
    intro x
    simp [classificationQuadraticTail,classificationDiagonalQuadratic,
      visibleBinaryQuadratic,smul_eq_C_mul]
    ring
  have hrest := (polynomialFunctionElements f h).sub_mem hq
    ((polynomialFunctionElements f h).smul_mem d ht)
  rw [he] at hrest
  have hg := hidden_linear_tail_zero_of_visible_binary_quadratic_member
    f h hrank hx₀ hx₁ a b c g hrest
  refine ⟨hg,?_⟩
  simpa [hg] using hrest


/-- This records members only. The first alternative is deliberately not
called the whole A function-space classification. -/
def ClassificationHiddenProjection (E : LieSubalgebra ℝ Operator) : Prop :=
  multiplication (polynomialSmooth (classificationDiagonalQuadratic 0 0 1))∈E ∨
  multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 0 1))∈E ∨
  multiplication (polynomialSmooth (classificationDiagonalQuadratic 0 1 1))∈E ∨
  multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 1 1))∈E

/-- Nonzero hidden quadratic curvature in an original genuine function
constructs the translated and rotated original model with a genuine hidden
projection. Finite-dimensionality, rank and both admitted coordinates are
proved for that exact model, rather than supplied as new premises. -/
theorem actual_hidden_curvature_projection_model {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h)=2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u∈estimationAlgebra f h)
    (hzz : partialDerivative 2 (partialDerivative 2 u)≠0) :
    ∃(z : State) (e : State ≃L[ℝ] State), CoordinateOrthogonal e ∧
      FiniteDimensional ℝ (estimationAlgebra (coordinateDrift e (translationDrift z f))
        (coordinateObservations e (translationObservations z h))) ∧
      linearRank (estimationAlgebra (coordinateDrift e (translationDrift z f))
        (coordinateObservations e (translationObservations z h)))=2 ∧
      multiplication (linearFunction (coordinateVector 0))∈
        estimationAlgebra (coordinateDrift e (translationDrift z f))
          (coordinateObservations e (translationObservations z h)) ∧
      multiplication (linearFunction (coordinateVector 1))∈
        estimationAlgebra (coordinateDrift e (translationDrift z f))
          (coordinateObservations e (translationObservations z h)) ∧
      ClassificationHiddenProjection
        (estimationAlgebra (coordinateDrift e (translationDrift z f))
          (coordinateObservations e (translationObservations z h))) := by
  obtain ⟨a,b,c,d,g,_,_,_,hq,_,hsecond⟩ :=
    actual_function_quadratic_tail_representation f h hrank hx₀ hx₁ u hu
  have hd : d≠0 := by
    intro hd
    apply hzz
    simpa only [hd,mul_zero,zero_smul] using hsecond
  let z := classificationHiddenCenter d g
  let ft := translationDrift z f
  let ht := translationObservations z h
  letI : FiniteDimensional ℝ (estimationAlgebra ft ht) :=
    finiteDimensional_translationEstimationAlgebra z f h
  have hrankt : linearRank (estimationAlgebra ft ht)=2 :=
    linearRank_translationEstimationAlgebra z f h hrank
  have ht₀ : multiplication (linearFunction (coordinateVector 0))∈estimationAlgebra ft ht :=
    coordinate_mem_translationEstimationAlgebra z f h hrank 0 hx₀
  have ht₁ : multiplication (linearFunction (coordinateVector 1))∈estimationAlgebra ft ht :=
    coordinate_mem_translationEstimationAlgebra z f h hrank 1 hx₁
  have hqt : classificationQuadraticTail a b c d 0∈polynomialFunctionElements ft ht :=
    actual_classification_hidden_center_mem f h hrank a b c d g hd hq
  obtain ⟨r,s,hrs,A,B,_,_,hdiag⟩ :=
    actual_classification_visible_diagonalization ft ht a b c d hqt
  let e := VisibleHeads.planeRotation r s hrs
  have he : CoordinateOrthogonal e := VisibleHeads.planeRotation_orthogonal r s hrs
  refine ⟨z,e,he,finiteDimensional_coordinateEstimationAlgebra e he ft ht,
    (linearRank_coordinateEstimationAlgebra e he ft ht).trans hrankt,
    VisibleHeads.planeRotation_coordinate_mem r s hrs ft ht ht₀ ht₁ 0 (Or.inl rfl),
    VisibleHeads.planeRotation_coordinate_mem r s hrs ft ht ht₀ ht₁ 1 (Or.inr rfl),?_⟩
  exact actual_classification_hidden_projection_mem
    (coordinateDrift e ft) (coordinateObservations e ht) A B d hd hdiag

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_classification_hidden_projection_mem
#print axioms Wong.SmoothModel.classification_visible_radial_mem
#print axioms Wong.SmoothModel.classification_singular_binary_common_axis

#print axioms Wong.SmoothModel.actual_function_quadratic_tail_representation

#print axioms Wong.SmoothModel.actual_classification_hidden_center_mem

#print axioms Wong.SmoothModel.actual_classification_visible_diagonalization

#print axioms Wong.SmoothModel.actual_classification_c2_of_all_visible_singular

#print axioms Wong.SmoothModel.actual_classification_visible_part_of_hidden_square

#print axioms Wong.SmoothModel.actual_hidden_curvature_projection_model
