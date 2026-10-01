import Wong.FunctionQuadraticRankConstraints
import Wong.CoordinateGenerators
import Wong.PublishedAffineStatement

/-! Exact supplied-paper main proposition definitions and proved coordinate equivalence. No 2020 main assertion is assumed here. -/


/-! Source segment: ShiYau2020MainStatement -/

/-! Exact mathematical main targets of the supplied 2020 article.
These are definitions of propositions, not assumed results. They use the
same actual filtering model as mainClaim and have no quadratic-freeness
premise. Their proofs are independent of the main constancy theorem. -/

noncomputable section
namespace Wong.SmoothModel

/-- Theorem 1.2 / 3.10: every actual function element is affine. -/
def ShiYau2020MitterClaim : Prop :=
  ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    FunctionElementsAffine (estimationAlgebra f h)

/-- Theorem 1.1 / 3.7: the existence of an actual degree-two function
element implies constant Wong entries and affine observations. -/
def ShiYau2020QuadraticClaim : Prop :=
  ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    (∃ p : RealPoly, p.totalDegree = 2 ∧
      multiplication (polynomialSmooth p) ∈ estimationAlgebra f h) →
    WongConstant f ∧
      (∀ j : Fin m, ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = h j)

end Wong.SmoothModel


/-! Source segment: ShiYau2020CoordinateReduction -/

/-! Exact coordinate reduction for the supplied paper's Mitter assertion.
Adapted coordinates are obtained from the original rank, with no quadratic
freeness premise; affine function elements are transported in both directions. -/

noncomputable section
namespace Wong.SmoothModel

theorem functionElementsAffine_coordinateEstimationAlgebra
    {m : ℕ} (e : State ≃L[ℝ] State) (he : CoordinateOrthogonal e)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (haff : FunctionElementsAffine (estimationAlgebra f h)) :
    FunctionElementsAffine (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) := by
  intro u hu
  have hsource : multiplication (coordinatePullback e.symm u) ∈ estimationAlgebra f h := by
    apply (multiplication_pullback_mem_coordinateAlgebra e (estimationAlgebra f h) _).mp
    change multiplication (coordinatePullback e ((coordinatePullback e).symm u)) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    rwa [coordinateAlgebra_estimationAlgebra e he]
  obtain ⟨p, hp, hpu⟩ := haff _ hsource
  obtain ⟨c, a, ha⟩ := polynomialSmooth_exists_affine_of_degree_le_one p hp
  have hsourceAffine : coordinatePullback e.symm u = c • smoothOne + linearFunction a :=
    hpu.symm.trans ha
  have htrans := congrArg (coordinatePullback e) hsourceAffine
  have hlin : coordinatePullback e (linearFunction a) = linearFunction (e.symm a) := by
    simpa only [e.apply_symm_apply] using
      coordinatePullback_linearFunction_orthogonal e he (e.symm a)
  have huAffine : u = c • smoothOne + linearFunction (e.symm a) := by
    simpa only [← coordinatePullback_symm, LinearEquiv.apply_symm_apply,
      map_add, map_smul, coordinatePullback_smoothOne, hlin] using htrans
  exact ⟨affineScalarPolynomial c (e.symm a), affineScalarPolynomial_degree_le_one _ _,
    (polynomialSmooth_affineScalarPolynomial _ _).trans huAffine.symm⟩

theorem functionElementsAffine_coordinateEstimationAlgebra_iff
    {m : ℕ} (e : State ≃L[ℝ] State) (he : CoordinateOrthogonal e)
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) :
    FunctionElementsAffine (estimationAlgebra (coordinateDrift e f) (coordinateObservations e h)) ↔
      FunctionElementsAffine (estimationAlgebra f h) := by
  constructor
  · intro haff
    have hback := functionElementsAffine_coordinateEstimationAlgebra e.symm he.symm
      (coordinateDrift e f) (coordinateObservations e h) haff
    simpa only [coordinateDrift_symm, coordinateObservations_symm] using hback
  · exact functionElementsAffine_coordinateEstimationAlgebra e he f h

/-- The adapted statement retains exactly the original finite-dimensional
rank-two hypotheses, adding only coordinates whose existence is proved. -/
def ShiYau2020AdaptedMitterClaim : Prop :=
  ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h →
    multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h →
    FunctionElementsAffine (estimationAlgebra f h)

theorem shiYau2020MitterClaim_iff_adapted :
    ShiYau2020MitterClaim ↔ ShiYau2020AdaptedMitterClaim := by
  constructor
  · intro hmain m f h hfd hrank _hx0 _hx1
    exact hmain m f h hfd hrank
  · intro hadapted m f h hfd hrank
    letI := hfd
    obtain ⟨e, he, hx0, hx1⟩ := exists_coordinateAlgebra_adapted (estimationAlgebra f h) hrank
    have hfd' := finiteDimensional_coordinateEstimationAlgebra e he f h
    have hrank' := (linearRank_coordinateEstimationAlgebra e he f h).trans hrank
    have hx0' : multiplication (linearFunction (coordinateVector 0)) ∈
        estimationAlgebra (coordinateDrift e f) (coordinateObservations e h) := by
      rwa [← coordinateAlgebra_estimationAlgebra e he]
    have hx1' : multiplication (linearFunction (coordinateVector 1)) ∈
        estimationAlgebra (coordinateDrift e f) (coordinateObservations e h) := by
      rwa [← coordinateAlgebra_estimationAlgebra e he]
    exact (functionElementsAffine_coordinateEstimationAlgebra_iff e he f h).mp
      (hadapted m _ _ hfd' hrank' hx0' hx1')

end Wong.SmoothModel

#print axioms Wong.SmoothModel.shiYau2020MitterClaim_iff_adapted
