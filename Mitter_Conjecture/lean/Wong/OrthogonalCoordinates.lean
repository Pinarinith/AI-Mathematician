import Wong.FirstOrderExtraction
import Wong.SmoothGeometry
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual changes of orthogonal coordinates

`State` carries the product (supremum) norm, so Euclidean rotations must not
be represented by isometries for that norm. We use genuine continuous
linear equivalences and express Euclidean orthogonality by preservation of
the ordinary coordinate dot product. Pullback and operator conjugation are
defined on the original smooth-function model.
-/

noncomputable section
namespace Wong.SmoothModel
open scoped ContDiff Matrix

/-- Euclidean orthogonality, independent of the chosen equivalent norm on `State`. -/
def CoordinateOrthogonal (e : State ≃L[ℝ] State) : Prop :=
  ∀ v w : State, (e v) ⬝ᵥ (e w) = v ⬝ᵥ w

theorem CoordinateOrthogonal.symm {e : State ≃L[ℝ] State}
    (he : CoordinateOrthogonal e) : CoordinateOrthogonal e.symm := by
  intro v w
  simpa using (he (e.symm v) (e.symm w)).symm

/-- Pullback by an actual invertible linear coordinate transformation. -/
def coordinatePullback (e : State ≃L[ℝ] State) : Smooth ≃ₗ[ℝ] Smooth where
  toFun u := ⟨u.1 ∘ e, (smooth u).comp e.contDiff⟩
  invFun u := ⟨u.1 ∘ e.symm, (smooth u).comp e.symm.contDiff⟩
  left_inv u := by
    apply Subtype.ext
    funext x
    simp
  right_inv u := by
    apply Subtype.ext
    funext x
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinatePullback_apply (e : State ≃L[ℝ] State) (u : Smooth) (x : State) :
    (coordinatePullback e u).1 x = u.1 (e x) := rfl

@[simp] theorem coordinatePullback_symm (e : State ≃L[ℝ] State) :
    (coordinatePullback e).symm = coordinatePullback e.symm := rfl

@[simp] theorem coordinatePullback_smoothOne (e : State ≃L[ℝ] State) :
    coordinatePullback e smoothOne = smoothOne := rfl

@[simp] theorem coordinatePullback_smoothMul (e : State ≃L[ℝ] State) (u v : Smooth) :
    coordinatePullback e (smoothMul u v) =
      smoothMul (coordinatePullback e u) (coordinatePullback e v) := rfl

/-- Conjugation on the actual algebra of smooth-function operators. -/
def coordinateConjugation (e : State ≃L[ℝ] State) : Operator ≃ₐ[ℝ] Operator :=
  (coordinatePullback e).conjAlgEquiv ℝ

def coordinateLieEquiv (e : State ≃L[ℝ] State) : Operator ≃ₗ⁅ℝ⁆ Operator :=
  (coordinateConjugation e).toLieEquiv

@[simp] theorem coordinateConjugation_apply (e : State ≃L[ℝ] State)
    (A : Operator) (u : Smooth) :
    coordinateConjugation e A u =
      coordinatePullback e (A (coordinatePullback e.symm u)) := rfl

@[simp] theorem coordinateConjugation_multiplication (e : State ≃L[ℝ] State) (u : Smooth) :
    coordinateConjugation e (multiplication u) = multiplication (coordinatePullback e u) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext x
  change u.1 (e x) * v.1 (e.symm (e x)) = u.1 (e x) * v.1 x
  rw [e.symm_apply_apply]

/-- The ordinary chain rule on genuine globally smooth functions. -/
theorem directionalDerivative_coordinatePullback (e : State ≃L[ℝ] State)
    (v : State) (u : Smooth) :
    directionalDerivative v (coordinatePullback e u) =
      coordinatePullback e (directionalDerivative (e v) u) := by
  apply Subtype.ext
  funext x
  rw [directionalDerivative_apply, coordinatePullback_apply, directionalDerivative_apply]
  change fderiv ℝ (u.1 ∘ e) x v = _
  rw [fderiv_comp x (((smooth u).differentiable (by simp)).differentiableAt)
    e.differentiableAt, e.fderiv]
  rfl

@[simp] theorem coordinateConjugation_directionalDerivative (e : State ≃L[ℝ] State)
    (v : State) :
    coordinateConjugation e (directionalDerivative v) = directionalDerivative (e.symm v) := by
  apply LinearMap.ext
  intro u
  rw [coordinateConjugation_apply, directionalDerivative_coordinatePullback]
  exact (coordinatePullback e).apply_symm_apply _

/-- View a smooth coefficient tuple as its actual linear combination in a direction. -/
def coefficientAlongLinear (a : Fin 3 → Smooth) : State →ₗ[ℝ] Smooth where
  toFun := coefficientAlong a
  map_add' := coefficientAlong_add a
  map_smul' := coefficientAlong_smul a

theorem coordinateVector_expansion (v : State) :
    (∑ i, v i • coordinateVector i) = v := by
  funext j
  simp [coordinateVector, Pi.single_apply]

/-- Pullback of the drift one-form. For orthogonal coordinates this is the
    ordinary rotated vector drift as well. -/
def coordinateDrift (e : State ≃L[ℝ] State) (f : Fin 3 → Smooth) : Fin 3 → Smooth :=
  fun i => coordinatePullback e (coefficientAlong f (e (coordinateVector i)))

theorem coefficientAlong_coordinateDrift (e : State ≃L[ℝ] State)
    (f : Fin 3 → Smooth) (v : State) :
    coefficientAlong (coordinateDrift e f) v =
      coordinatePullback e (coefficientAlong f (e v)) := by
  have hev : (∑ i, v i • e (coordinateVector i)) = e v := by
    calc
      _ = e (∑ i, v i • coordinateVector i) := by simp only [map_sum, map_smul]
      _ = e v := by rw [coordinateVector_expansion]
  change (∑ i, v i • coordinatePullback e
    (coefficientAlongLinear f (e (coordinateVector i)))) =
      coordinatePullback e (coefficientAlongLinear f (e v))
  rw [← hev, map_sum, map_sum]
  simp only [map_smul]

theorem coordinateDrift_symm (e : State ≃L[ℝ] State) (f : Fin 3 → Smooth) :
    coordinateDrift e.symm (coordinateDrift e f) = f := by
  funext i
  simp only [coordinateDrift, coefficientAlong_coordinateDrift, e.apply_symm_apply,
    coefficientAlong_coordinate]
  exact (coordinatePullback e).symm_apply_apply (f i)

theorem directionD_eq_directionalDerivative_sub (f : Fin 3 → Smooth) (v : State) :
    directionD f v = directionalDerivative v - multiplication (coefficientAlong f v) := by
  simp only [directionD, D, smul_sub, Finset.sum_sub_distrib,
    directionalDerivative, coefficientAlong, multiplication_sum, multiplication_smul]

theorem coordinateConjugation_directionD (e : State ≃L[ℝ] State)
    (f : Fin 3 → Smooth) (v : State) :
    coordinateConjugation e (directionD f (e v)) = directionD (coordinateDrift e f) v := by
  simp only [directionD_eq_directionalDerivative_sub, map_sub,
    coordinateConjugation_directionalDerivative, e.symm_apply_apply,
    coordinateConjugation_multiplication, coefficientAlong_coordinateDrift]

theorem coordinateConjugation_directionD_coordinate (e : State ≃L[ℝ] State)
    (f : Fin 3 → Smooth) (i : Fin 3) :
    coordinateConjugation e (directionD f (e (coordinateVector i))) =
      D (coordinateDrift e f) i := by
  rw [coordinateConjugation_directionD, directionD_eq_directionalDerivative_sub]
  simp only [coordinate_directionalDerivative, coefficientAlong_coordinate, D]

/-- The actual curvature two-form applied to two constant directions. -/
def wongBilinear (f : Fin 3 → Smooth) (v w : State) : Smooth :=
  ∑ i, ∑ j, (v i * w j) • wong f i j

theorem lie_directionD_directionD (f : Fin 3 → Smooth) (v w : State) :
    ⁅directionD f w, directionD f v⁆ = multiplication (wongBilinear f v w) := by
  simp only [directionD, sum_lie, lie_sum, smul_lie, lie_smul, lie_D_D,
    wongBilinear, multiplication_sum, multiplication_smul, Finset.smul_sum, smul_smul]

/-- Tensorial transformation of the genuine Wong functions, proved by
    conjugating genuine covariant-derivative commutators. -/
theorem wong_coordinateDrift (e : State ≃L[ℝ] State) (f : Fin 3 → Smooth)
    (i j : Fin 3) :
    wong (coordinateDrift e f) i j = coordinatePullback e
      (wongBilinear f (e (coordinateVector i)) (e (coordinateVector j))) := by
  apply multiplication_injective
  calc
    multiplication (wong (coordinateDrift e f) i j) =
        ⁅D (coordinateDrift e f) j, D (coordinateDrift e f) i⁆ := (lie_D_D _ _ _).symm
    _ = ⁅coordinateConjugation e (directionD f (e (coordinateVector j))),
        coordinateConjugation e (directionD f (e (coordinateVector i)))⁆ := by
      rw [coordinateConjugation_directionD_coordinate, coordinateConjugation_directionD_coordinate]
    _ = coordinateConjugation e
        ⁅directionD f (e (coordinateVector j)), directionD f (e (coordinateVector i))⁆ :=
      ((coordinateLieEquiv e).map_lie _ _).symm
    _ = _ := by rw [lie_directionD_directionD, coordinateConjugation_multiplication]

theorem WongConstant_coordinateDrift (e : State ≃L[ℝ] State) (f : Fin 3 → Smooth)
    (hf : WongConstant f) : WongConstant (coordinateDrift e f) := by
  obtain ⟨Ω, hΩ⟩ := hf
  refine ⟨fun i j => ∑ k, ∑ l,
    (e (coordinateVector i) k * e (coordinateVector j) l) * Ω k l, ?_⟩
  intro i j x
  rw [wong_coordinateDrift, coordinatePullback_apply]
  simp [wongBilinear, hΩ]

/-- Constancy is invariant under this genuine coordinate transformation.
    Orthogonality is not needed for this two-form statement. -/
theorem WongConstant_coordinateDrift_iff (e : State ≃L[ℝ] State) (f : Fin 3 → Smooth) :
    WongConstant (coordinateDrift e f) ↔ WongConstant f := by
  constructor
  · intro hf
    have hback := WongConstant_coordinateDrift e.symm (coordinateDrift e f) hf
    rwa [coordinateDrift_symm] at hback
  · exact WongConstant_coordinateDrift e f

/-- The Euclidean Hilbert-space model used solely to choose rotations. -/
abbrev EuclideanState := EuclideanSpace ℝ (Fin 3)

/-- Transport a genuine Euclidean isometry to the original product-norm state space. -/
def coordinatesOfEuclideanIsometry (q : EuclideanState ≃ₗᵢ[ℝ] EuclideanState) :
    State ≃L[ℝ] State :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.trans
    (q.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 3) ℝ))

theorem coordinatesOfEuclideanIsometry_orthogonal
    (q : EuclideanState ≃ₗᵢ[ℝ] EuclideanState) :
    CoordinateOrthogonal (coordinatesOfEuclideanIsometry q) := by
  intro v w
  have hi := q.inner_map_map
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm w)
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm v)
  change WithLp.ofLp (q (WithLp.toLp 2 v)) ⬝ᵥ WithLp.ofLp (q (WithLp.toLp 2 w)) = v ⬝ᵥ w
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp] using hi

/-- A two-dimensional Euclidean subspace extends to an orthonormal basis
    with its first two vectors inside that subspace. -/
theorem euclidean_orthonormalBasis_adapted (S : Submodule ℝ EuclideanState)
    (hS : Module.finrank ℝ S = 2) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ EuclideanState, b 0 ∈ S ∧ b 1 ∈ S := by
  let bS : OrthonormalBasis (Fin 2) ℝ S :=
    (stdOrthonormalBasis ℝ S).reindex (finCongr hS)
  let v : Fin 3 → EuclideanState := ![(bS 0).1, (bS 1).1, 0]
  let s : Set (Fin 3) := {0, 1}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = 0 ∨ i = 1 := by simpa [s] using hi
    have hj' : j = 0 ∨ j = 1 := by simpa [s] using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · change inner ℝ (bS 0) (bS 0) = 1
      exact orthonormal_iff_ite.mp bS.orthonormal 0 0
    · change inner ℝ (bS 0) (bS 1) = 0
      exact orthonormal_iff_ite.mp bS.orthonormal 0 1
    · change inner ℝ (bS 1) (bS 0) = 0
      exact orthonormal_iff_ite.mp bS.orthonormal 1 0
    · change inner ℝ (bS 1) (bS 1) = 1
      exact orthonormal_iff_ite.mp bS.orthonormal 1 1
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ EuclideanState = Fintype.card (Fin 3)) hv
  refine ⟨b, ?_, ?_⟩
  · rw [hb 0 (by simp [s])]
    exact (bS 0).property
  · rw [hb 1 (by simp [s])]
    exact (bS 1).property

/-- A rank-two subspace of the original state space admits actual orthogonal
    coordinates whose first two coordinate directions lie in that subspace. -/
theorem exists_orthogonal_coordinates_adapted (S : Submodule ℝ State)
    (hS : Module.finrank ℝ S = 2) :
    ∃ e : State ≃L[ℝ] State, CoordinateOrthogonal e ∧
      e (coordinateVector 0) ∈ S ∧ e (coordinateVector 1) ∈ S := by
  let l := EuclideanSpace.equiv (Fin 3) ℝ
  let T : Submodule ℝ EuclideanState := S.map l.symm.toLinearMap
  have hT : Module.finrank ℝ T = 2 :=
    (l.symm.toLinearEquiv.submoduleMap S).finrank_eq.symm.trans hS
  obtain ⟨b, hb₀, hb₁⟩ := euclidean_orthonormalBasis_adapted T hT
  have hmem (z : EuclideanState) (hz : z ∈ T) : l z ∈ S := by
    obtain ⟨x, hx, he⟩ := hz
    rw [← he]
    simpa using hx
  let e := coordinatesOfEuclideanIsometry b.repr.symm
  have hb (i : Fin 3) : e (coordinateVector i) = l (b i) := by
    change l (b.repr.symm (EuclideanSpace.single i (1 : ℝ))) = l (b i)
    rw [b.repr_symm_single]
  refine ⟨e, coordinatesOfEuclideanIsometry_orthogonal _, ?_, ?_⟩
  · rw [hb]
    exact hmem _ hb₀
  · rw [hb]
    exact hmem _ hb₁

theorem coordinatePullback_linearFunction_orthogonal (e : State ≃L[ℝ] State)
    (he : CoordinateOrthogonal e) (v : State) :
    coordinatePullback e (linearFunction (e v)) = linearFunction v := by
  apply Subtype.ext
  funext x
  exact he v x

/-- Transport of the actual Lie algebra by coordinate conjugation. -/
abbrev coordinateAlgebra (e : State ≃L[ℝ] State) (E : LieSubalgebra ℝ Operator) :
    LieSubalgebra ℝ Operator := E.map (coordinateLieEquiv e).toLieHom

def coordinateAlgebraEquiv (e : State ≃L[ℝ] State) (E : LieSubalgebra ℝ Operator) :
    E ≃ₗ⁅ℝ⁆ coordinateAlgebra e E :=
  (coordinateLieEquiv e).ofSubalgebras E (coordinateAlgebra e E) rfl

theorem coordinateAlgebra_finiteDimensional (e : State ≃L[ℝ] State)
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (coordinateAlgebra e E) :=
  (coordinateAlgebraEquiv e E).toLinearEquiv.finiteDimensional

/-- The original rank-two hypothesis, with no chosen-coordinate assumption,
    supplies a genuine conjugate algebra containing the first two coordinates. -/
theorem exists_coordinateAlgebra_adapted (E : LieSubalgebra ℝ Operator)
    (hrank : linearRank E = 2) :
    ∃ e : State ≃L[ℝ] State, CoordinateOrthogonal e ∧
      multiplication (linearFunction (coordinateVector 0)) ∈ coordinateAlgebra e E ∧
      multiplication (linearFunction (coordinateVector 1)) ∈ coordinateAlgebra e E := by
  obtain ⟨e, he, h₀, h₁⟩ := exists_orthogonal_coordinates_adapted (linearCoefficientSpace E) hrank
  have hmem (v : State) (hv : multiplication (linearFunction (e v)) ∈ E) :
      multiplication (linearFunction v) ∈ coordinateAlgebra e E := by
    refine ⟨multiplication (linearFunction (e v)), hv, ?_⟩
    change coordinateConjugation e (multiplication (linearFunction (e v))) = _
    rw [coordinateConjugation_multiplication, coordinatePullback_linearFunction_orthogonal e he]
  exact ⟨e, he, hmem _ h₀, hmem _ h₁⟩

end Wong.SmoothModel
