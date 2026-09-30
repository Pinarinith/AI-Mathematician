import Wong.GeneratorCommutator
import Wong.FirstOrderPolynomial
import Wong.RankStructure
import Wong.SmoothGeometry
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Intrinsic polynomiality of the Wong matrix at linear rank two

Two linearly independent directions whose linear multipliers belong to the
actual algebra give two polynomial contractions of the Wong matrix. In
three real dimensions these contractions determine a skew matrix. A real
linear left inverse reconstructs all entries as actual polynomials.
No adapted-coordinate membership or coordinate change is assumed.
-/

noncomputable section
namespace Wong.SmoothModel
open scoped Matrix

/-- Contraction in the first index, with a constant real direction. -/
def wongContraction (f : Fin 3 → Smooth) (v : State) (j : Fin 3) : Smooth :=
  ∑ i, v i • wong f i j

theorem lie_L0_directionD_firstOrder {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (v : State) :
    ⁅L0 f h, directionD f v⁆ = firstOrder f (wongContraction f v)
      (∑ i, v i • generatorRemainder f h i) := by
  simp only [directionD, lie_sum, lie_smul, lie_L0_D, firstOrder,
    wongContraction, smul_add, Finset.smul_sum, multiplication_sum,
    multiplication_smul, Finset.sum_mul, smul_mul_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_comm]

theorem wongContraction_polynomial_of_linear_mem {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (v : State) (hv : multiplication (linearFunction v) ∈ estimationAlgebra f h)
    (j : Fin 3) : ∃ p : RealPoly,
      ∀ x : State, MvPolynomial.eval x p = (wongContraction f v j).1 x := by
  have hL : L0 f h ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hD : directionD f v ∈ estimationAlgebra f h := by
    rw [← lie_L0_linearFunction f h v]
    exact (estimationAlgebra f h).lie_mem hL hv
  have hA : firstOrder f (wongContraction f v)
      (∑ i, v i • generatorRemainder f h i) ∈ estimationAlgebra f h := by
    rw [← lie_L0_directionD_firstOrder]
    exact (estimationAlgebra f h).lie_mem hL hD
  obtain ⟨_, hpoly⟩ := firstOrder_coefficients_uniform_polynomial_degree f h
  obtain ⟨p, _, hp⟩ := hpoly _ _ hA j
  exact ⟨p, hp⟩

/-- The three independent entries of a real skew matrix, in axial-vector order. -/
def wongAxialValue (f : Fin 3 → Smooth) (x : State) : State :=
  ![(wong f 1 2).1 x, -(wong f 0 2).1 x, (wong f 0 1).1 x]

theorem cross_wongAxialValue (f : Fin 3 → Smooth) (v x : State) (j : Fin 3) :
    (crossProduct (wongAxialValue f x) v) j = (wongContraction f v j).1 x := by
  have h10 := wong_skew f 0 1
  have h20 := wong_skew f 0 2
  have h21 := wong_skew f 1 2
  fin_cases j <;>
    simp [wongAxialValue, cross_apply, wongContraction, Fin.sum_univ_succ,
      h10, h20, h21] <;> ring

/-- Six scalar coordinates of the two cross-product contractions. -/
def twoCross (v : Fin 2 → State) : State →ₗ[ℝ] (Fin 2 × Fin 3 → ℝ) where
  toFun z k := crossProduct z (v k.1) k.2
  map_add' z w := by
    funext k
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c z := by
    funext k
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

theorem twoCross_injective (v : Fin 2 → State) (hv : LinearIndependent ℝ v) :
    Function.Injective (twoCross v) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  by_contra hzne
  have hcross (i : Fin 2) : crossProduct z (v i) = 0 := by
    funext j
    exact congrFun hz (i, j)
  have hdep (i : Fin 2) : ∃ c : ℝ, v i = c • z := by
    have hh : ¬LinearIndependent ℝ ![z, v i] := by
      rw [← crossProduct_ne_zero_iff_linearIndependent]
      exact not_not_intro (hcross i)
    rw [LinearIndependent.pair_iff' hzne] at hh
    push Not at hh
    obtain ⟨c, hc⟩ := hh
    exact ⟨c, hc.symm⟩
  obtain ⟨c, hc⟩ := hdep 0
  obtain ⟨d, hd⟩ := hdep 1
  have hvpair : LinearIndependent ℝ ![v 0, v 1] := by
    convert hv using 1
    funext i
    fin_cases i <;> rfl
  have hrel : d • v 0 + (-c) • v 1 = 0 := by
    rw [hc, hd, smul_smul, smul_smul, ← add_smul]
    simp [mul_comm]
  have hcoeff := LinearIndependent.pair_iff.mp hvpair d (-c) hrel
  have hc0 : c = 0 := neg_eq_zero.mp hcoeff.2
  apply hv.ne_zero 0
  rw [hc, hc0, zero_smul]

theorem visible_independent_pair_of_rank_two (E : LieSubalgebra ℝ Operator)
    (hrank : linearRank E = 2) :
    ∃ v : Fin 2 → State, LinearIndependent ℝ v ∧
      ∀ i, multiplication (linearFunction (v i)) ∈ E := by
  have hdim : 2 ≤ Module.finrank ℝ (linearCoefficientSpace E) := by
    change 2 ≤ linearRank E
    omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  refine ⟨fun i => (v i).1, ?_, fun i => (v i).property⟩
  exact hv.map' (linearCoefficientSpace E).subtype (linearCoefficientSpace E).ker_subtype

/-- A real linear inverse preserves polynomial dependence on the state. -/
theorem polynomial_coordinates_of_linear_leftInverse
    (F : State →ₗ[ℝ] (Fin 2 × Fin 3 → ℝ)) (hF : Function.Injective F)
    (z : State → State) (p : Fin 2 × Fin 3 → RealPoly)
    (hp : ∀ x k, MvPolynomial.eval x (p k) = F (z x) k) :
    ∀ j : Fin 3, ∃ q : RealPoly, ∀ x, MvPolynomial.eval x q = z x j := by
  let G := F.leftInverse
  have hGF : ∀ w, G (F w) = w :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hF)
  intro j
  refine ⟨∑ k, MvPolynomial.C (G (Pi.single k 1) j) * p k, ?_⟩
  intro x
  have hexp : (∑ k, F (z x) k • Pi.single k (1 : ℝ)) = F (z x) := by
    funext k
    simp [Pi.single_apply]
  calc
    MvPolynomial.eval x (∑ k, MvPolynomial.C (G (Pi.single k 1) j) * p k) =
        ∑ k, G (Pi.single k 1) j * F (z x) k := by
      simp only [map_sum, map_mul, MvPolynomial.eval_C, hp]
    _ = G (∑ k, F (z x) k • Pi.single k (1 : ℝ)) j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = z x j := by rw [hexp, hGF]

/-- The rank-two hypothesis alone supplies the directions used to recover
    all three independent Wong entries as genuine polynomials. -/
theorem wongAxial_polynomial_of_rank_two {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2) :
    ∀ j : Fin 3, ∃ p : RealPoly, ∀ x, MvPolynomial.eval x p = wongAxialValue f x j := by
  obtain ⟨v, hv, hmem⟩ := visible_independent_pair_of_rank_two (estimationAlgebra f h) hrank
  have hpol (k : Fin 2 × Fin 3) : ∃ p : RealPoly,
      ∀ x, MvPolynomial.eval x p = (wongContraction f (v k.1) k.2).1 x :=
    wongContraction_polynomial_of_linear_mem f h (v k.1) (hmem k.1) k.2
  choose p hp using hpol
  apply polynomial_coordinates_of_linear_leftInverse (twoCross v) (twoCross_injective v hv)
    (wongAxialValue f) p
  intro x k
  rw [hp]
  exact (cross_wongAxialValue f (v k.1) x k.2).symm

/-- Intrinsic polynomiality of every actual Wong entry: the only structural
    assumptions are finite dimensionality and the original linear rank two. -/
theorem wong_polynomial_of_rank_two {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2) (i j : Fin 3) :
    ∃ p : RealPoly, ∀ x, MvPolynomial.eval x p = (wong f i j).1 x := by
  obtain ⟨p₀, h₀⟩ := wongAxial_polynomial_of_rank_two f h hrank 0
  obtain ⟨p₁, h₁⟩ := wongAxial_polynomial_of_rank_two f h hrank 1
  obtain ⟨p₂, h₂⟩ := wongAxial_polynomial_of_rank_two f h hrank 2
  have e₀ : ∀ x, MvPolynomial.eval x p₀ = (wong f 1 2).1 x := h₀
  have e₁ : ∀ x, MvPolynomial.eval x p₁ = -(wong f 0 2).1 x := h₁
  have e₂ : ∀ x, MvPolynomial.eval x p₂ = (wong f 0 1).1 x := h₂
  have h10 := wong_skew f 0 1
  have h20 := wong_skew f 0 2
  have h21 := wong_skew f 1 2
  fin_cases i <;> fin_cases j
  · exact ⟨0, by simp⟩
  · exact ⟨p₂, e₂⟩
  · refine ⟨-p₁, ?_⟩
    intro x
    simp [e₁]
  · refine ⟨-p₂, ?_⟩
    intro x
    simp [e₂, h10]
  · exact ⟨0, by simp⟩
  · exact ⟨p₀, e₀⟩
  · refine ⟨p₁, ?_⟩
    intro x
    simp [e₁, h20]
  · refine ⟨-p₀, ?_⟩
    intro x
    simp [e₀, h21]
  · exact ⟨0, by simp⟩

theorem wong_polynomialSmooth_of_rank_two {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2) (i j : Fin 3) :
    ∃ p : RealPoly, polynomialSmooth p = wong f i j := by
  obtain ⟨p, hp⟩ := wong_polynomial_of_rank_two f h hrank i j
  exact ⟨p, Subtype.ext (funext hp)⟩

end Wong.SmoothModel
