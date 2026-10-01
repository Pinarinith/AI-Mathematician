import Wong.FunctionQuadraticRankConstraints

/-!
# The hidden linear tail of a genuine visible quadratic function element

Carré-du-champ words isolate the visible quadratic part even when the two
visible eigenvalues agree or one vanishes.  Subtraction then produces the
hidden linear multiplier genuinely inside the estimation algebra; adapted
rank two forces its coefficient to vanish.  No Wong affinity or quadratic-free
hypothesis is used, and finite dimensionality is not needed for this lemma.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Wong.SmoothModel
open MvPolynomial

/-- The bilinear polynomial carré-du-champ. -/
def quadraticGradientPair (p q : RealPoly) : RealPoly :=
  ∑ i : Fin 3, pderiv i p * pderiv i q

/-- Bilinear gradient closure comes from an actual double Lie commutator. -/
theorem polynomialFunctionElements_gradient_pair_closed {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth) {p q : RealPoly}
    (hp : p ∈ polynomialFunctionElements f h)
    (hq : q ∈ polynomialFunctionElements f h) :
    quadraticGradientPair p q ∈ polynomialFunctionElements f h := by
  change multiplication (polynomialSmooth (quadraticGradientPair p q)) ∈
    estimationAlgebra f h
  have he : polynomialSmooth (quadraticGradientPair p q) =
      ∑ i : Fin 3, smoothMul (partialDerivative i (polynomialSmooth p))
        (partialDerivative i (polynomialSmooth q)) := by
    simp only [quadraticGradientPair, polynomialSmooth_sum, polynomialSmooth_mul,
      partialDerivative_polynomialSmooth]
  rw [he, ← double_lie_L0_multiplication f h]
  have hL : L0 f h ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  exact (estimationAlgebra f h).lie_mem ((estimationAlgebra f h).lie_mem hL hp) hq

/-- A diagonal quadratic in the two admitted visible coordinates. -/
def visibleDiagonalQuadratic (a b : ℝ) : RealPoly := C a * X 0 ^ 2 + C b * X 1 ^ 2

/-- The potentially inadmissible hidden linear tail is retained explicitly. -/
def visibleQuadraticHiddenTail (a b g : ℝ) : RealPoly :=
  visibleDiagonalQuadratic a b + C g * X 2

theorem visibleQuadraticHiddenTail_gradient_square (a b g : ℝ) :
    quadraticGradientPair (visibleQuadraticHiddenTail a b g)
      (visibleQuadraticHiddenTail a b g) =
      visibleDiagonalQuadratic (4*a^2) (4*b^2) + C (g^2) := by
  apply MvPolynomial.funext
  intro x
  simp [quadraticGradientPair, visibleQuadraticHiddenTail, visibleDiagonalQuadratic,
    Fin.sum_univ_three, pderiv_pow, pderiv_X]
  ring

theorem visibleQuadraticHiddenTail_second_gradient (a b g : ℝ) :
    quadraticGradientPair (visibleQuadraticHiddenTail a b g)
      (visibleDiagonalQuadratic (4*a^2) (4*b^2)) =
      visibleDiagonalQuadratic (16*a^3) (16*b^3) := by
  apply MvPolynomial.funext
  intro x
  simp [quadraticGradientPair, visibleQuadraticHiddenTail, visibleDiagonalQuadratic,
    Fin.sum_univ_three, pderiv_pow, pderiv_X]
  ring

/-- Two genuine gradient words recover the original visible quadratic.  The
proof includes the zero and repeated-eigenvalue cases. -/
theorem visibleDiagonalQuadratic_mem_of_two_gradient_words
    (S : Submodule ℝ RealPoly) (a b : ℝ)
    (hF : visibleDiagonalQuadratic (4*a^2) (4*b^2) ∈ S)
    (hG : visibleDiagonalQuadratic (16*a^3) (16*b^3) ∈ S) :
    visibleDiagonalQuadratic a b ∈ S := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simpa only [visibleDiagonalQuadratic, map_zero, zero_mul, add_zero] using S.zero_mem
    · have he : visibleDiagonalQuadratic 0 b =
          (1/(4*b)) • visibleDiagonalQuadratic (4*(0:ℝ)^2) (4*b^2) := by
        apply MvPolynomial.funext
        intro x
        simp [visibleDiagonalQuadratic, smul_eq_C_mul]
        field_simp [hb] <;> ring
      rw [he]
      exact S.smul_mem _ hF
  · by_cases hb : b = 0
    · subst b
      have he : visibleDiagonalQuadratic a 0 =
          (1/(4*a)) • visibleDiagonalQuadratic (4*a^2) (4*(0:ℝ)^2) := by
        apply MvPolynomial.funext
        intro x
        simp [visibleDiagonalQuadratic, smul_eq_C_mul]
        field_simp [ha] <;> ring
      rw [he]
      exact S.smul_mem _ hF
    · have he : visibleDiagonalQuadratic a b =
          ((a+b)/(4*a*b)) • visibleDiagonalQuadratic (4*a^2) (4*b^2) -
            (1/(16*a*b)) • visibleDiagonalQuadratic (16*a^3) (16*b^3) := by
        apply MvPolynomial.funext
        intro x
        simp [visibleDiagonalQuadratic, smul_eq_C_mul]
        field_simp [ha, hb] <;> ring
      rw [he]
      exact S.sub_mem (S.smul_mem _ hF) (S.smul_mem _ hG)

/-- The hidden linear term cannot be silently subtracted: this theorem derives
its actual membership from gradient words and then uses rank two to eliminate it. -/
theorem hidden_linear_tail_zero_of_visible_quadratic_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (a b g : ℝ)
    (hphi : multiplication (polynomialSmooth (visibleQuadraticHiddenTail a b g)) ∈
      estimationAlgebra f h) : g = 0 := by
  let S := polynomialFunctionElements f h
  have hphiS : visibleQuadraticHiddenTail a b g ∈ S := hphi
  have hconstant : C (g^2) ∈ S := by
    change multiplication (polynomialSmooth (C (g^2))) ∈ estimationAlgebra f h
    rw [polynomialSmooth_C, multiplication_smul]
    exact (estimationAlgebra f h).smul_mem _
      (smoothOne_mem_estimationAlgebra_of_rank_two f h hrank)
  have hF : visibleDiagonalQuadratic (4*a^2) (4*b^2) ∈ S := by
    have he := polynomialFunctionElements_gradient_pair_closed f h hphiS hphiS
    rw [visibleQuadraticHiddenTail_gradient_square] at he
    simpa only [add_sub_cancel_right] using S.sub_mem he hconstant
  have hG : visibleDiagonalQuadratic (16*a^3) (16*b^3) ∈ S := by
    have he := polynomialFunctionElements_gradient_pair_closed f h hphiS hF
    simpa only [visibleQuadraticHiddenTail_second_gradient] using he
  have hQ := visibleDiagonalQuadratic_mem_of_two_gradient_words S a b hF hG
  have htail : C g * X 2 ∈ S := by
    have he := S.sub_mem hphiS hQ
    simpa only [visibleQuadraticHiddenTail, add_sub_cancel_left] using he
  have hlin : polynomialSmooth (C g * X (2 : Fin 3)) =
      linearFunction (g • coordinateVector 2) := by
    apply Subtype.ext
    funext x
    simp [polynomialSmooth, linearFunction, coordinateVector, Pi.single_apply]
  have hmember : g • coordinateVector 2 ∈ linearCoefficientSpace (estimationAlgebra f h) := by
    change multiplication (linearFunction (g • coordinateVector 2)) ∈ estimationAlgebra f h
    rw [← hlin]
    exact htail
  have hz := rank_two_adapted_coefficient_zero (estimationAlgebra f h)
    hrank hx₀ hx₁ (g • coordinateVector 2) hmember
  simpa [coordinateVector] using hz

/-- The general visible quadratic, including its mixed visible term. -/
def visibleBinaryQuadratic (a b c : ℝ) : RealPoly :=
  C a * X 0 ^ 2 + C (2*b) * X 0 * X 1 + C c * X 1 ^ 2

/-- Cayley--Hamilton gradient recovery for the complete visible quadratic.
This avoids introducing a diagonalizing coordinate transformation. -/
theorem visibleBinaryQuadratic_mem_of_gradient_words
    (S : Submodule ℝ RealPoly) (a b c g : ℝ)
    (hF : quadraticGradientPair (visibleBinaryQuadratic a b c + C g * X 2)
      (visibleBinaryQuadratic a b c + C g * X 2) - C (g^2) ∈ S)
    (hG : quadraticGradientPair (visibleBinaryQuadratic a b c + C g * X 2)
      (quadraticGradientPair (visibleBinaryQuadratic a b c + C g * X 2)
        (visibleBinaryQuadratic a b c + C g * X 2) - C (g^2)) ∈ S) :
    visibleBinaryQuadratic a b c ∈ S := by
  let p := visibleBinaryQuadratic a b c + C g * X 2
  let F := quadraticGradientPair p p - C (g^2)
  let G := quadraticGradientPair p F
  change F ∈ S at hF
  change G ∈ S at hG
  have hFshape : F = visibleBinaryQuadratic (4*(a^2+b^2)) (4*b*(a+c))
      (4*(b^2+c^2)) := by
    apply MvPolynomial.funext
    intro x
    simp [F, p, quadraticGradientPair, visibleBinaryQuadratic,
      Fin.sum_univ_three, pderiv_pow, pderiv_X]
    ring
  have hGshape : G = visibleBinaryQuadratic (16*(a^3+2*a*b^2+b^2*c))
      (16*b*(a^2+a*c+b^2+c^2)) (16*(a*b^2+2*b^2*c+c^3)) := by
    dsimp only [G]
    rw [hFshape]
    apply MvPolynomial.funext
    intro x
    simp [p, quadraticGradientPair, visibleBinaryQuadratic,
      Fin.sum_univ_three, pderiv_pow, pderiv_X]
    ring
  by_cases hd : a*c-b^2 = 0
  · by_cases ht : a+c = 0
    · have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have ha : a = 0 := by nlinarith [sq_nonneg a]
      have hc : c = 0 := by linarith
      simpa [visibleBinaryQuadratic, ha, hb, hc] using S.zero_mem
    · have he : visibleBinaryQuadratic a b c = (1/(4*(a+c))) • F := by
        rw [hFshape]
        apply MvPolynomial.funext
        intro x
        simp [visibleBinaryQuadratic, smul_eq_C_mul]
        field_simp [ht]
        nlinarith [congrArg (fun z : ℝ => (x 0)^2*z) hd,
          congrArg (fun z : ℝ => (x 1)^2*z) hd]
      rw [he]
      exact S.smul_mem _ hF
  · have he : visibleBinaryQuadratic a b c =
        ((a+c)/(4*(a*c-b^2))) • F - (1/(16*(a*c-b^2))) • G := by
      rw [hFshape, hGshape]
      apply MvPolynomial.funext
      intro x
      simp [visibleBinaryQuadratic, smul_eq_C_mul]
      field_simp [hd] <;> ring
    rw [he]
    exact S.sub_mem (S.smul_mem _ hF) (S.smul_mem _ hG)

/-- Without any coordinate diagonalization, a quadratic in the visible plane
cannot carry a hidden linear term in an adapted rank-two estimation algebra. -/
theorem hidden_linear_tail_zero_of_visible_binary_quadratic_member {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (a b c g : ℝ)
    (hphi : multiplication (polynomialSmooth (visibleBinaryQuadratic a b c + C g * X 2)) ∈
      estimationAlgebra f h) : g = 0 := by
  let S := polynomialFunctionElements f h
  have hphiS : visibleBinaryQuadratic a b c + C g * X 2 ∈ S := hphi
  have hconstant : C (g^2) ∈ S := by
    change multiplication (polynomialSmooth (C (g^2))) ∈ estimationAlgebra f h
    rw [polynomialSmooth_C, multiplication_smul]
    exact (estimationAlgebra f h).smul_mem _
      (smoothOne_mem_estimationAlgebra_of_rank_two f h hrank)
  have hF := S.sub_mem
    (polynomialFunctionElements_gradient_pair_closed f h hphiS hphiS) hconstant
  have hG := polynomialFunctionElements_gradient_pair_closed f h hphiS hF
  have hQ := visibleBinaryQuadratic_mem_of_gradient_words S a b c g hF hG
  have htail : C g * X 2 ∈ S := by
    simpa only [add_sub_cancel_left] using S.sub_mem hphiS hQ
  have hlin : polynomialSmooth (C g * X (2 : Fin 3)) =
      linearFunction (g • coordinateVector 2) := by
    apply Subtype.ext
    funext x
    simp [polynomialSmooth, linearFunction, coordinateVector, Pi.single_apply]
  have hmember : g • coordinateVector 2 ∈ linearCoefficientSpace (estimationAlgebra f h) := by
    change multiplication (linearFunction (g • coordinateVector 2)) ∈ estimationAlgebra f h
    rw [← hlin]
    exact htail
  have hz := rank_two_adapted_coefficient_zero (estimationAlgebra f h)
    hrank hx₀ hx₁ (g • coordinateVector 2) hmember
  simpa [coordinateVector] using hz

end Wong.SmoothModel

#print axioms Wong.SmoothModel.polynomialFunctionElements_gradient_pair_closed
#print axioms Wong.SmoothModel.hidden_linear_tail_zero_of_visible_quadratic_member

#print axioms Wong.SmoothModel.hidden_linear_tail_zero_of_visible_binary_quadratic_member
