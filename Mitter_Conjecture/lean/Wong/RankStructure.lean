import Wong.Ocone
import Wong.DirectionalExtraction
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Linear rank and the actual function-element space

Positive linear rank forces the identity multiplier into the actual
estimation algebra. Rank two and quadratic-freeness then describe every
function element intrinsically. The final adapted-coordinate conclusions
explicitly assume membership of the first two coordinate multipliers;
they do not add such a hypothesis to the original main claim.
-/

noncomputable section
namespace Wong.SmoothModel

theorem exists_nonzero_linear_function_of_rank_two (E : LieSubalgebra ℝ Operator)
    (hrank : linearRank E = 2) :
    ∃ a : State, a ≠ 0 ∧ multiplication (linearFunction a) ∈ E := by
  have hr : 0 < Module.finrank ℝ (linearCoefficientSpace E) := by
    change 0 < linearRank E
    omega
  obtain ⟨a, ha⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hr
  refine ⟨a.1, ?_, a.property⟩
  intro hz
  apply ha
  exact Subtype.ext hz

theorem sum_coordinate_squares_pos (a : State) (ha : a ≠ 0) :
    0 < ∑ i, a i * a i := by
  have hex : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro j _
    exact mul_self_nonneg (a j)
  · exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- This uses the original rank hypothesis, not membership of a preselected coordinate. -/
theorem one_mem_estimationAlgebra_of_rank_two {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (hrank : linearRank (estimationAlgebra f h) = 2) :
    (1 : Operator) ∈ estimationAlgebra f h := by
  obtain ⟨a, ha, hMa⟩ := exists_nonzero_linear_function_of_rank_two
    (estimationAlgebra f h) hrank
  have hL : L0 f h ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hD : directionD f a ∈ estimationAlgebra f h := by
    rw [← lie_L0_linearFunction f h a]
    exact (estimationAlgebra f h).lie_mem hL hMa
  have hs : (∑ i, a i * a i) • (1 : Operator) ∈ estimationAlgebra f h := by
    rw [← lie_directionD_linearFunction f a]
    exact (estimationAlgebra f h).lie_mem hD hMa
  have hne : (∑ i, a i * a i) ≠ 0 := ne_of_gt (sum_coordinate_squares_pos a ha)
  have hinv := (estimationAlgebra f h).smul_mem (∑ i, a i * a i)⁻¹ hs
  simpa [smul_smul, hne] using hinv

theorem smoothOne_mem_estimationAlgebra_of_rank_two {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) (hrank : linearRank (estimationAlgebra f h) = 2) :
    multiplication smoothOne ∈ estimationAlgebra f h := by
  simpa using one_mem_estimationAlgebra_of_rank_two f h hrank

theorem affine_representation_unique (c d : ℝ) (a b : State)
    (he : c • smoothOne + linearFunction a = d • smoothOne + linearFunction b) :
    c = d ∧ a = b := by
  have hc := congrArg (fun u : Smooth => u.1 (0 : State)) he
  have hcd : c = d := by simpa [smoothOne, linearFunction] using hc
  refine ⟨hcd, ?_⟩
  funext i
  have hi := congrArg (fun u : Smooth => u.1 (coordinateVector i)) he
  simpa [smoothOne, linearFunction, coordinateVector, Pi.single_apply, mul_ite, hcd] using hi

/-- Each function element has exactly one constant plus homogeneous-linear representation. -/
theorem function_element_unique_affine {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h) :
    ∃! ca : ℝ × State,
      ca.2 ∈ linearCoefficientSpace (estimationAlgebra f h) ∧
        u = ca.1 • smoothOne + linearFunction ca.2 := by
  obtain ⟨c, a, he⟩ := quadraticFree_function_element_affine f h hq u hu
  have hOne := smoothOne_mem_estimationAlgebra_of_rank_two f h hrank
  have ha : a ∈ linearCoefficientSpace (estimationAlgebra f h) := by
    change multiplication (linearFunction a) ∈ estimationAlgebra f h
    have hm := (estimationAlgebra f h).sub_mem hu
      ((estimationAlgebra f h).smul_mem c hOne)
    simpa [he] using hm
  refine ⟨(c, a), ⟨ha, he⟩, ?_⟩
  rintro ⟨d, b⟩ ⟨_, hb⟩
  obtain ⟨hc, hab⟩ := affine_representation_unique d c b a (hb.symm.trans he)
  exact Prod.ext hc hab

/-- Once two specified coordinate multipliers belong to a rank-two algebra,
the third coordinate coefficient of every admitted linear function is zero. -/
theorem rank_two_adapted_coefficient_zero (E : LieSubalgebra ℝ Operator)
    (hrank : linearRank E = 2)
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ E)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ E)
    (a : State) (ha : a ∈ linearCoefficientSpace E) : a 2 = 0 := by
  let S := linearCoefficientSpace E
  have he₀ : coordinateVector 0 ∈ S := h₀
  have he₁ : coordinateVector 1 ∈ S := h₁
  by_contra ha₂
  have hd : a - a 0 • coordinateVector 0 - a 1 • coordinateVector 1 =
      a 2 • coordinateVector 2 := by
    funext i
    fin_cases i <;> simp [coordinateVector]
  have he₂ : coordinateVector 2 ∈ S := by
    have hs := S.sub_mem (S.sub_mem ha (S.smul_mem (a 0) he₀)) (S.smul_mem (a 1) he₁)
    rw [hd] at hs
    have ht := S.smul_mem (a 2)⁻¹ hs
    simpa [smul_smul, ha₂] using ht
  have htop : S = ⊤ := by
    apply top_unique
    intro v _
    have hv : (∑ i, v i • coordinateVector i) = v := by
      funext j
      simp [coordinateVector, Pi.single_apply]
    rw [← hv]
    apply S.sum_mem
    intro i _
    apply S.smul_mem
    fin_cases i
    · exact he₀
    · exact he₁
    · exact he₂
  have hr : Module.finrank ℝ S = 2 := hrank
  rw [htop, finrank_top] at hr
  have hdim : Module.finrank ℝ State = 3 := by simp [State]
  omega

/-- Adapted-coordinate function space, conditional only on the stated coordinate memberships. -/
theorem function_element_adapted {m : ℕ} (f : Fin 3 → Smooth)
    (h : Fin m → Smooth) [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (u : Smooth) (hu : multiplication u ∈ estimationAlgebra f h) :
    ∃ c a₀ a₁ : ℝ, u = c • smoothOne +
      a₀ • linearFunction (coordinateVector 0) + a₁ • linearFunction (coordinateVector 1) := by
  obtain ⟨⟨c, a⟩, ⟨ha, he⟩, _⟩ := function_element_unique_affine f h hrank hq u hu
  have ha₂ := rank_two_adapted_coefficient_zero (estimationAlgebra f h) hrank h₀ h₁ a ha
  refine ⟨c, a 0, a 1, ?_⟩
  rw [he]
  apply Subtype.ext
  funext x
  simp [smoothOne, linearFunction, coordinateVector, Fin.sum_univ_succ, Pi.single_apply, ha₂]
  ring

theorem D_mem_of_coordinate_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i : Fin 3)
    (hi : multiplication (linearFunction (coordinateVector i)) ∈ estimationAlgebra f h) :
    D f i ∈ estimationAlgebra f h := by
  have hL : L0 f h ∈ estimationAlgebra f h :=
    LieSubalgebra.subset_lieSpan (Or.inl rfl)
  have hbr := (estimationAlgebra f h).lie_mem hL hi
  rw [lie_L0_linearFunction] at hbr
  simpa [directionD, coordinateVector, Pi.single_apply, ite_smul] using hbr

theorem wong_mem_of_coordinate_mem {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (i j : Fin 3)
    (hi : multiplication (linearFunction (coordinateVector i)) ∈ estimationAlgebra f h)
    (hj : multiplication (linearFunction (coordinateVector j)) ∈ estimationAlgebra f h) :
    multiplication (wong f i j) ∈ estimationAlgebra f h := by
  rw [← lie_D_D]
  exact (estimationAlgebra f h).lie_mem
    (D_mem_of_coordinate_mem f h j hj) (D_mem_of_coordinate_mem f h i hi)

end Wong.SmoothModel
