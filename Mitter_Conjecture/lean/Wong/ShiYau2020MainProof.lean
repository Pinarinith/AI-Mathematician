import Wong.QuadraticFunctionCaseSplit
import Wong.HiddenRadialEtaConclusion
import Wong.PlaneRadialWongRigidity
import Wong.B2EtaAnalysis
import Wong.C1EtaConclusion
import Wong.ConstantWongHiddenIndependentEtaClosure
import Wong.C2Complete
import Wong.PublishedAffineInput
import Wong.ShiYau2020IntroductionStatement

/-! Exact mathematical main results of the supplied 2020 article.
The exhaustive actual five-case reduction is proved independently of the
original quadratic-free Main. Every case gives actual affine function
members, contradicting its genuine quadratic member. No literature result
is introduced as an axiom and no case restriction is an initial premise. -/
noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open MvPolynomial

 theorem classification_model_functionElementsAffine {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx0 : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx1 : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (hcase : ClassificationModelCase f h) :
    FunctionElementsAffine (estimationAlgebra f h) := by
  obtain ⟨p, hp⟩ := shi_yau_affine_structure f h hrank hx0 hx1
  rcases hcase with hA | hB2 | hB1 | hC1 | hC2
  · have hq : multiplication (hiddenShearTime * hiddenShearTime) ∈ estimationAlgebra f h := by
      have ht := hA.1
      change multiplication (polynomialSmooth (classificationDiagonalQuadratic 0 0 1)) ∈
        estimationAlgebra f h at ht
      simpa [classificationDiagonalQuadratic, pow_two, polynomialSmooth_mul,
        polynomialSmooth_coordinate, hiddenShearTime, smoothMul_eq_mul] using ht
    exact functionElementsAffine_of_pure_hidden_square_whole_hessian_free
      f h hrank hx0 hx1 hq hA.2 p hp
  · have hq : multiplication (polynomialSmooth planeRadialPolynomial) ∈ estimationAlgebra f h := by
      have ht := hB2
      change multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 0 1)) ∈
        estimationAlgebra f h at ht
      simpa [classificationDiagonalQuadratic, planeRadialPolynomial] using ht
    obtain ⟨hW, h02, h12⟩ := plane_radial_affine_wongConstant_and_mixed_zero
      f h hrank hx0 hx1 hq p hp
    have hq' : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 2)^2)) ∈
        estimationAlgebra f h := hq
    exact functionElementsAffine_of_constant_wong_plane_radial_member
      f h hrank hx0 hx1 hW h02 h12 hq'
  · have hq : multiplication (polynomialSmooth fullRadialQuadraticPolynomial) ∈
        estimationAlgebra f h := by
      have ht := hB1
      change multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 1 1)) ∈
        estimationAlgebra f h at ht
      simpa [classificationDiagonalQuadratic, fullRadialQuadraticPolynomial] using ht
    exact functionElementsAffine_of_full_radial_quadratic_member f h hrank hx0 hx1 hq p hp
  · have hq : multiplication (polynomialSmooth ((X 0 : RealPoly)^2 + (X 1)^2)) ∈
        estimationAlgebra f h := by
      have ht := hC1.2
      change multiplication (polynomialSmooth (classificationDiagonalQuadratic 1 1 0)) ∈
        estimationAlgebra f h at ht
      simpa [classificationDiagonalQuadratic] using ht
    have hW := c1_wongConstant_of_actual_affine_shape f h hrank hx0 hx1 hC1.1 hq p hp
    have hH := c1_eta_visible_hessians_constant f h hrank hx0 hx1 hW hC1.1 hq
    exact functionElementsAffine_of_constant_wong_hidden_independent_visible_hessians
      f h hrank hx0 hx1 hW hC1.1 (by
        intro i j hi hj
        exact hH i j (by rcases hi with rfl | rfl <;> decide)
          (by rcases hj with rfl | rfl <;> decide))
  · have hW := c2_wongConstant_of_affine f h hrank hC2 hx0 hx1 p hp
    have hHF := HiddenIndependent.c2_hiddenIndependent _ hC2
    have h00 := c2_eta_zero_zero_constant f h hrank hC2 hx0 hW
    have h01 := c2_eta_zero_one_constant f h hrank hC2 hx0 hx1 hW
    have h11 := c2_eta_one_one_constant f h hrank hC2 hx0 hx1 hW
    exact functionElementsAffine_of_constant_wong_hidden_independent_visible_hessians
      f h hrank hx0 hx1 hW hHF (by
        intro i j hi hj
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · exact h00
        · exact h01
        · simpa only [partialDerivative_commute_apply] using h01
        · exact h11)

 theorem shiYau2020_adapted_mitter_theorem : ShiYau2020AdaptedMitterClaim := by
  intro m f h hfd hrank hx0 hx1
  letI := hfd
  apply (quadraticFree_iff_functionElementsAffine f h).mp
  intro q hq hactual
  obtain ⟨A, hA, haction⟩ := hactual
  have hAeq : A = multiplication (polynomialSmooth q) := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    exact haction u x
  have hqE : q ∈ polynomialFunctionElements f h := by
    change multiplication (polynomialSmooth q) ∈ estimationAlgebra f h
    rw [← hAeq]
    exact hA
  obtain ⟨f', h', hfd', hrank', hx0', hx1', hcase⟩ :=
    actual_quadratic_function_cases f h hrank hx0 hx1 q hq hqE
  letI := hfd'
  exact classification_model_case_not_functionElementsAffine f' h' hcase
    (classification_model_functionElementsAffine f' h' hrank' hx0' hx1' hcase)

/-- Theorem 1.2 / 3.10 of the supplied paper, with precisely its original
finite-dimensional, state-three, rank-two smooth estimation-algebra scope. -/
 theorem shiYau2020_mitter_theorem : ShiYau2020MitterClaim :=
  shiYau2020MitterClaim_iff_adapted.mpr shiYau2020_adapted_mitter_theorem

/-- Theorem 3.7 follows from the stronger independently proved absence
of actual quadratic function elements. The proof is a valid alternative to
the paper's ordering of the two main results. -/
 theorem shiYau2020_quadratic_theorem : ShiYau2020QuadraticClaim := by
  intro m f h hfd hrank hq
  obtain ⟨q, hqdeg, hqE⟩ := hq
  have haff := shiYau2020_mitter_theorem m f h hfd hrank
  obtain ⟨p, hp, hpq⟩ := haff (polynomialSmooth q) hqE
  have heq := polynomialSmooth_injective hpq
  rw [heq, hqdeg] at hp
  omega

/-- Literal Wong-only conclusion of introduction Theorem1.1. -/
 theorem shiYau2020_wong_quadratic_theorem : ShiYau2020WongQuadraticClaim := by
  intro m f h hfd hrank hq
  exact (shiYau2020_quadratic_theorem m f h hfd hrank hq).1

end Wong.SmoothModel

#print axioms Wong.SmoothModel.shiYau2020_wong_quadratic_theorem
#print axioms Wong.SmoothModel.shiYau2020_mitter_theorem
#print axioms Wong.SmoothModel.shiYau2020_quadratic_theorem
