import Wong.PolynomialVisibleFirstOrderBridge
import Wong.PolynomialVisibleDerivativeBounds
import Wong.PolynomialTopRemainder
import Wong.PolynomialQuadraticFirstOrderRigidity
import Wong.MixedAffinityHighDegree
import Wong.PublishedVisibleAffinityProof
import Wong.IntrinsicWongPolynomial

/-!
Internal mixed-coefficient affinity from genuine admitted visible commutators.
The scalar remainder is retained throughout. No hidden covariant derivative,
associative closure of E, or independent affinity hypothesis is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Wong.SmoothModel
open MvPolynomial

theorem polynomialSmooth_neg (p : RealPoly) :
    polynomialSmooth (-p) = -polynomialSmooth p :=
  polynomialSmoothLinear.map_neg p

theorem polynomialSmooth_hidden_power (a : ℝ) (l : ℕ) :
    polynomialSmooth (C a * X 2 ^ l) = a • ladderHiddenCoordinate ^ l := by
  apply Subtype.ext
  funext x
  simp [polynomialSmooth, ladderHiddenCoordinate, linearFunction,
    coordinateVector, Fin.sum_univ_three]

theorem actual_firstOrder_polynomial_hidden_degree_le_one {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hD₀ : D f 0 ∈ estimationAlgebra f h) (hD₁ : D f 1 ∈ estimationAlgebra f h)
    (P : Fin 3 → RealPoly) (b : Smooth)
    (hP : firstOrder f (fun j => polynomialSmooth (P j)) b ∈ estimationAlgebra f h)
    (hvisible : ∀ i : Fin 3, i ≠ 2 → (P i).totalDegree ≤ 1)
    (h₀ : partialDerivative 2 (polynomialSmooth (P 0)) = 0)
    (h₁ : partialDerivative 2 (polynomialSmooth (P 1)) = 0) :
    (P 2).totalDegree ≤ 1 := by
  classical
  by_contra hn
  obtain ⟨u, v, hshape⟩ := visible_polynomial_derivative_extract (P 2) (by omega)
  let Q : Fin 3 → RealPoly := fun j => visiblePolynomialDerivative u v (P j)
  obtain ⟨c, hc⟩ := firstOrder_visible_polynomial_derivatives_mem f h hD₀ hD₁ P b hP u v
  obtain ⟨p, hp, hact, hS⟩ := exists_actual_normal_firstOrder f
    (fun j => polynomialSmooth (Q j)) c
  have hpE : normalAction p ∈ estimationAlgebra f h := by
    rw [hact]
    exact hc
  have hQvisible (i : Fin 3) (hi : i ≠ 2) : (Q i).totalDegree ≤ 1 :=
    (visiblePolynomialDerivative_degree_le u v (P i)).trans (hvisible i hi)
  have hQ₀ : partialDerivative 2 (polynomialSmooth (Q 0)) = 0 :=
    visiblePolynomialDerivative_actual_hidden_partial_zero u v (P 0) h₀
  have hQ₁ : partialDerivative 2 (polynomialSmooth (Q 1)) = 0 :=
    visiblePolynomialDerivative_actual_hidden_partial_zero u v (P 1) h₁
  rcases hshape with htwo | ⟨l, a, hl, ha, hdegree, htop⟩
  · have haff := actual_polynomial_quadratic_firstOrder_hidden_degree_le_one f h
      hD₀ hD₁ p hp hpE Q hS hQvisible (by exact htwo.le) hQ₀ hQ₁
    change (Q 2).totalDegree = 2 at htwo
    omega
  · change (Q 2).totalDegree = l at hdegree
    change homogeneousComponent l (Q 2) = C a * X 2 ^ l at htop
    let rem : RealPoly := Q 2 - C a * X 2 ^ l
    have hrem : rem.totalDegree ≤ l-1 :=
      polynomial_sub_hidden_top_power_degree_le (Q 2) l a (by omega) hdegree htop
    let r : PolynomialSymbol :=
      X 0 * C (Q 0) + X 1 * C (Q 1) + X 2 * C rem
    have hr : PolynomialPositionDegreeLE (l-1) r :=
      (((PolynomialPositionDegreeLE.C (Q 0) (l-1)
        ((hQvisible 0 (by decide)).trans (by omega))).X_mul 0).add
        ((PolynomialPositionDegreeLE.C (Q 1) (l-1)
        ((hQvisible 1 (by decide)).trans (by omega))).X_mul 1)).add
        ((PolynomialPositionDegreeLE.C rem (l-1) hrem).X_mul 2)
    have hsplit : normalSymbol 1 p =
        C (a • ladderHiddenCoordinate ^ ((l-2)+2)) * X 2 + polynomialSymbolLift r := by
      rw [show (l-2)+2=l by omega, hS]
      simp only [r, map_add, map_mul, polynomialSymbolLift_X, polynomialSymbolLift_C,
        Fin.sum_univ_three]
      have hpol : Q 2 = C a * X 2 ^ l + rem := by dsimp [rem]; ring
      rw [hpol, polynomialSmooth_add, polynomialSmooth_hidden_power, map_add]
      ring
    have ha0 := actual_hidden_top_polynomial_obstruction f h p hp hpE (l-2) a r
      (by simpa only [show l-2+1=l-1 by omega] using hr) hsplit
    exact ha ha0

theorem mixed_wong_published_polynomials_of_visible_affinity {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p₀₁ : RealPoly) (hd₀₁ : p₀₁.totalDegree ≤ 1)
    (hh₀₁ : pderiv 2 p₀₁ = 0) (he₀₁ : polynomialSmooth p₀₁ = wong f 0 1) :
    ∃ p₀₂ p₁₂ : RealPoly, p₀₂.totalDegree ≤ 1 ∧ p₁₂.totalDegree ≤ 1 ∧
      polynomialSmooth p₀₂ = wong f 0 2 ∧ polynomialSmooth p₁₂ = wong f 1 2 := by
  classical
  have hD₀ := D_mem_of_coordinate_mem f h 0 hx₀
  have hD₁ := D_mem_of_coordinate_mem f h 1 hx₁
  obtain ⟨p₀₂, he₀₂⟩ := wong_polynomialSmooth_of_rank_two f h hrank 0 2
  obtain ⟨p₁₂, he₁₂⟩ := wong_polynomialSmooth_of_rank_two f h hrank 1 2
  let P₀ : Fin 3 → RealPoly := ![0, p₀₁, p₀₂]
  let P₁ : Fin 3 → RealPoly := ![-p₀₁, 0, p₁₂]
  have hrow₀ : (fun j => polynomialSmooth (P₀ j)) = wong f 0 := by
    funext j
    fin_cases j <;> simp [P₀, he₀₁, he₀₂]
  have hrow₁ : (fun j => polynomialSmooth (P₁ j)) = wong f 1 := by
    funext j
    fin_cases j <;> simp [P₁, polynomialSmooth_neg, he₀₁, he₁₂,
      wong_skew f 0 1]
  have hhidden : partialDerivative 2 (polynomialSmooth p₀₁) = 0 := by
    rw [partialDerivative_polynomialSmooth, hh₀₁, polynomialSmooth_zero]
  have hmem₀ : firstOrder f (fun j => polynomialSmooth (P₀ j))
      (generatorRemainder f h 0) ∈ estimationAlgebra f h := by
    rw [hrow₀]
    exact firstOrder_wong_mem_of_D_mem f h 0 hD₀
  have hmem₁ : firstOrder f (fun j => polynomialSmooth (P₁ j))
      (generatorRemainder f h 1) ∈ estimationAlgebra f h := by
    rw [hrow₁]
    exact firstOrder_wong_mem_of_D_mem f h 1 hD₁
  have hvis₀ (i : Fin 3) (hi : i ≠ 2) : (P₀ i).totalDegree ≤ 1 := by
    fin_cases i
    · simp [P₀]
    · exact hd₀₁
    · exact False.elim (hi rfl)
  have hvis₁ (i : Fin 3) (hi : i ≠ 2) : (P₁ i).totalDegree ≤ 1 := by
    fin_cases i
    · change (-p₀₁).totalDegree ≤ 1
      simpa only [totalDegree_neg] using hd₀₁
    · simp [P₁]
    · exact False.elim (hi rfl)
  have hd₀₂ := actual_firstOrder_polynomial_hidden_degree_le_one f h hD₀ hD₁
    P₀ _ hmem₀ hvis₀ (by simp [P₀]) (by exact hhidden)
  have hd₁₂ := actual_firstOrder_polynomial_hidden_degree_le_one f h hD₀ hD₁
    P₁ _ hmem₁ hvis₁
    (by
      change partialDerivative 2 (polynomialSmooth (-p₀₁)) = 0
      rw [polynomialSmooth_neg, map_neg, hhidden, neg_zero]) (by simp [P₁])
  exact ⟨p₀₂, p₁₂, hd₀₂, hd₁₂, he₀₂, he₁₂⟩

theorem internal_published_polynomial_of_quadraticFree {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h) :
    PublishedPolynomialWong f := by
  obtain ⟨p₀₁, hd₀₁, hh₀₁, he₀₁⟩ :=
    visible_wong_published_polynomial_of_quadraticFree f h hrank hq hx₀ hx₁
  obtain ⟨p₀₂, p₁₂, hd₀₂, hd₁₂, he₀₂, he₁₂⟩ :=
    mixed_wong_published_polynomials_of_visible_affinity f h hrank hx₀ hx₁
      p₀₁ hd₀₁ hh₀₁ he₀₁
  exact ⟨p₀₁, p₀₂, p₁₂, hd₀₁, hd₀₂, hd₁₂, hh₀₁, he₀₁, he₀₂, he₁₂⟩

end Wong.SmoothModel

#print axioms Wong.SmoothModel.actual_firstOrder_polynomial_hidden_degree_le_one
#print axioms Wong.SmoothModel.internal_published_polynomial_of_quadraticFree
