import Wong.RootAnalyticBridges
import Wong.EulerHighDegreeLadder
import Wong.VisibleElimination
import Wong.PublishedAffineInput

/-! Actual hidden slope elimination, including both differential spectral
projections and all original-model hypothesis transport. -/


/-! Source segment: EulerHighFrame -/

/-! A protected Euler projection removes all actual lower hidden powers
 of the differential part. Its scalar coefficient remains unrestricted. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
open Polynomial
set_option maxHeartbeats 1200000

theorem normal_euler_polynomial_single (Q : Polynomial ℝ) (α : MultiIndex)
    (u : Smooth) :
    (aeval normalHiddenEuler Q) (Finsupp.single α u) =
      Finsupp.single α ((aeval (shiftedHiddenEuler α) Q) u) := by
  classical
  ext β
  rw [normalHiddenEuler_polynomial_coefficient]
  by_cases he : α=β
  · subst β
    simp
  · simp [he]

theorem shiftedEuler_projection_hidden_independent (Q : Polynomial ℝ)
    (α : MultiIndex) (u : Smooth) (hu : partialDerivative 2 u = 0) :
    (aeval (shiftedHiddenEuler α) Q) u = Q.eval (-(α 2 : ℝ)) • u := by
  simpa only [zero_sub] using shiftedHiddenEuler_polynomial_eigenvalue α u 0
    (by simpa using hiddenEuler_of_hidden_independent u hu) Q

theorem hiddenEuler_hiddenCoordinate_pow (n : ℕ) :
    hiddenEuler (ladderHiddenCoordinate^n) = (n : ℝ) • ladderHiddenCoordinate^n := by
  cases n with
  | zero =>
    simp only [pow_zero,Nat.cast_zero,zero_smul]
    exact hiddenEuler_of_hidden_independent 1 (by simpa using partialDerivative_const 2 1)
  | succ n =>
    rw [hiddenEuler,Module.End.mul_apply,partial_hidden_coordinate_pow_succ]
    apply Subtype.ext
    funext x
    simp only [multiplication_apply,smoothMul_apply,Submodule.coe_smul,
      Pi.smul_apply,smul_eq_mul,smooth_coe_pow,Nat.cast_add,Nat.cast_one,
      ladderHiddenCoordinate,pow_succ,smooth_coe_mul]
    ring

def highProtectedWeights (d : ℕ) : Finset ℤ :=
  insert ((d : ℤ)+1) ({-2,-1,0} ∪ (Finset.range (d+2)).image (fun k : ℕ => (k : ℤ)-1))

theorem highProtectedWeights_small (d : ℕ) (j : ℤ) (hj : j∈({-2,-1,0} : Finset ℤ)) :
    j ∈ highProtectedWeights d := by
  unfold highProtectedWeights
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hj)

theorem highProtectedWeights_lower (d k : ℕ) (hk : k<d+2) :
    (k : ℤ)-1 ∈ highProtectedWeights d := by
  unfold highProtectedWeights
  exact Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr hk,rfl⟩))

theorem actual_high_frameDiffusion_obstruction
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (hnormal : E ≤ normalFormOperators)
    (B : Smooth) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ E)
    (α β a : ℝ) (d : ℕ) (g : Fin 3 → Smooth) (V : Smooth)
    (hg₀ : partialDerivative 2 (g 0) = 0) (hg₁ : partialDerivative 2 (g 1) = 0)
    (hres : (partialDerivative 2 ^ (d+2))
      (α • g 0 + β • g 1 + g 2 - a • ladderHiddenCoordinate^(d+2)) = 0)
    (hL : directionalDiffusion α β g V ∈ E)
    (hHeat : partialDerivative 2 ^ 2 ∈ E) : a = 0 := by
  classical
  let p := frameDiffusionNormal α β g V
  have hp : normalAction p ∈ E := by
    simpa only [p,normalAction_frameDiffusionNormal] using hL
  obtain ⟨Q,hval,hmem,_heig⟩ := actual_euler_projection_with_prescribed_weights
    E hfinite hnormal B hB hJ (normalAction p) hp (d+1) (highProtectedWeights d)
  have hvsmall (j : ℤ) (hj : j∈({-2,-1,0} : Finset ℤ)) : Q.eval (j:ℝ)=0 := by
    rw [hval j (highProtectedWeights_small d j hj)]
    have hn : j ≠ (d:ℤ)+1 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hj; rcases hj with rfl|rfl|rfl <;> omega
    simp [hn]
  have hv₀ : Q.eval 0 = 0 := by simpa using hvsmall 0 (by simp)
  have hv₁ : Q.eval (-1) = 0 := by simpa using hvsmall (-1) (by simp)
  have hv₂ : Q.eval (-2) = 0 := by simpa using hvsmall (-2) (by simp)
  have hvlead : Q.eval (d+1 : ℝ) = 1 := by
    simpa using hval (d+1) (by simp [highProtectedWeights])
  let r := α • g 0 + β • g 1 + g 2 - a • ladderHiddenCoordinate^(d+2)
  have hr : (aeval (shiftedHiddenEuler (Finsupp.single 2 1)) Q) r = 0 := by
    apply shiftedHiddenEuler_polynomial_zero_of_nilpotent _ r (d+2) hres Q
    intro k hk
    have hh := hval ((k:ℤ)-1) (highProtectedWeights_lower d k hk)
    have hn : (k:ℤ)-1 ≠ (d:ℤ)+1 := by omega
    simpa [hn] using hh
  have hlead : (aeval (shiftedHiddenEuler (Finsupp.single 2 1)) Q)
      (a • ladderHiddenCoordinate^(d+2)) = a • ladderHiddenCoordinate^(d+2) := by
    rw [map_smul,shiftedHiddenEuler_polynomial_eigenvalue _ _ (d+2 : ℝ)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat] using
        hiddenEuler_hiddenCoordinate_pow (d+2)) Q]
    norm_num
    rw [show (d:ℝ)+2-1=(d:ℝ)+1 by ring,hvlead,one_smul]
  have hfirst : (aeval (shiftedHiddenEuler (Finsupp.single 2 1)) Q)
      (α • g 0 + β • g 1 + g 2) = a • ladderHiddenCoordinate^(d+2) := by
    have he : α • g 0 + β • g 1 + g 2 = a • ladderHiddenCoordinate^(d+2) + r := by
      dsimp [r]
      abel
    rw [he,map_add,hlead,hr,add_zero]
  have hconst (γ : MultiIndex) (c : ℝ) :
      (aeval (shiftedHiddenEuler γ) Q) (c • smoothOne) =
        Q.eval (-(γ 2:ℝ)) • (c • smoothOne) :=
    shiftedEuler_projection_hidden_independent Q γ _ (by simp [partialDerivative_const])
  let q := (aeval hiddenEuler Q) (frameScalar g V α β)
  have he : (aeval normalHiddenEuler Q) p = highEulerNormal a d q := by
    simp only [p,frameDiffusionNormal,frameSecondNormal,map_add,map_sub,
      normal_euler_polynomial_single,hconst,
      shiftedEuler_projection_hidden_independent Q _ (g 0) hg₀,
      shiftedEuler_projection_hidden_independent Q _ (g 1) hg₁,
      Finsupp.single_apply,Finsupp.add_apply]
    norm_num
    rw [hv₀,hv₁,hv₂]
    simp only [zero_smul,Finsupp.single_zero,zero_add,sub_zero,zero_sub]
    rw [← Finsupp.single_add,← Finsupp.single_add,
      ← map_smul,← map_smul,← map_add,← map_add,hfirst]
    simp only [zero_smul,Finsupp.single_zero,zero_add,sub_zero,zero_sub,highEulerNormal,
      neg_smul,Finsupp.single_neg,shiftedHiddenEuler,Finsupp.zero_apply,Nat.cast_zero,q]
  have ht : normalAction (highEulerNormal a d q) ∈ E := by
    rw [← he,normalHiddenEuler_polynomial_action]
    exact hmem
  exact highEuler_ladder_obstruction E hfinite a d q hHeat ht

end Wong.SmoothModel


/-! Source segment: SectorICoefficientShapes -/

/-! The actual triangular polynomial drift and the actual slanted gauge
profile give the coefficient decompositions used by the Euler projections. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
set_option maxHeartbeats 1000000

theorem triangular_hidden_affine_split (p : Wong.AffineParameters) (α β δ : ℝ) :
    hiddenAffinePullback α β δ (triangularDrift p 2) =
      smoothMul (visibleSlope p.k₃ p.h₃) (linearFunction (coordinateVector 2)) +
        hiddenRestriction (hiddenAffinePullback α β δ (triangularDrift p 2)) := by
  apply Subtype.ext
  funext x
  simp [hiddenRestriction,hiddenAffinePullback,affinePullback_apply,
    triangularDrift,triangularDriftPolynomials,polynomialSmooth,
    hiddenShear,hiddenShearLinear,visibleSlope,linearFunction,coordinateVector,
    Fin.sum_univ_three,Submodule.coe_add,Submodule.coe_smul,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul,smoothMul_apply]
  <;> ring

theorem low_slanted_polynomial_split (u : Smooth) (p : Polynomial ℝ) (α β δ : ℝ)
    (hu : ∀ x : State, u.1 x = p.eval (x 2-α*x 0-β*x 1-δ))
    (hd : p.natDegree ≤ 1) :
    ∃ a : ℝ, u = a • linearFunction (coordinateVector 2) + hiddenRestriction u := by
  obtain ⟨a,b,hp⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hd
  refine ⟨a,?_⟩
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_add,Pi.add_apply,Submodule.coe_smul,Pi.smul_apply,
    smul_eq_mul,hiddenRestriction]
  rw [hu,hu,hp]
  simp [linearFunction,coordinateVector,Fin.sum_univ_three]
  <;> ring

theorem normalized_low_hidden_first_coefficient
    (p : Wong.AffineParameters) (α β δ : ℝ) (Λ : Smooth)
    (hp : Polynomial ℝ)
    (hw : ∀ x : State, (partialDerivative 2 Λ).1 x =
      hp.eval (x 2-α*x 0-β*x 1-δ)) (hd : hp.natDegree ≤ 1)
    (hg₀ : partialDerivative 2 (frameDrift (triangularDrift p) α β δ Λ 0) = 0)
    (hg₁ : partialDerivative 2 (frameDrift (triangularDrift p) α β δ Λ 1) = 0) :
    ∃ c : ℝ, ∃ v : Smooth, partialDerivative 2 v = 0 ∧
      α • frameDrift (triangularDrift p) α β δ Λ 0 +
      β • frameDrift (triangularDrift p) α β δ Λ 1 +
      frameDrift (triangularDrift p) α β δ Λ 2 =
      smoothMul (visibleSlope p.k₃ p.h₃ + c • smoothOne)
        (linearFunction (coordinateVector 2)) + v := by
  obtain ⟨c,hc⟩ := low_slanted_polynomial_split (partialDerivative 2 Λ) hp α β δ hw hd
  let v := α • frameDrift (triangularDrift p) α β δ Λ 0 +
    β • frameDrift (triangularDrift p) α β δ Λ 1 +
    hiddenRestriction (hiddenAffinePullback α β δ (triangularDrift p 2)) +
    hiddenRestriction (partialDerivative 2 Λ)
  refine ⟨c,v,?_,?_⟩
  · simp [v,hg₀,hg₁,partialDerivative_hiddenRestriction]
  · have he₂ : frameDrift (triangularDrift p) α β δ Λ 2 =
        hiddenAffinePullback α β δ (triangularDrift p 2) + partialDerivative 2 Λ := by
      simp [frameDrift,frameVectors,coordinate_directionalDerivative]
    rw [he₂,triangular_hidden_affine_split,hc]
    simp only [smoothMul_eq_mul,add_mul,smul_mul_assoc,smoothOne_eq_one,one_mul,v]
    abel

theorem normalized_high_hidden_first_nilpotent
    (p : Wong.AffineParameters) (α β δ : ℝ) (Λ : Smooth)
    (hp : Polynomial ℝ) (d : ℕ) (hd : hp.natDegree = d+2)
    (hw : ∀ x : State, (partialDerivative 2 Λ).1 x =
      hp.eval (x 2-α*x 0-β*x 1-δ))
    (hg₀ : partialDerivative 2 (frameDrift (triangularDrift p) α β δ Λ 0) = 0)
    (hg₁ : partialDerivative 2 (frameDrift (triangularDrift p) α β δ Λ 1) = 0) :
    (partialDerivative 2 ^ (d+2))
      (α • frameDrift (triangularDrift p) α β δ Λ 0 +
      β • frameDrift (triangularDrift p) α β δ Λ 1 +
      frameDrift (triangularDrift p) α β δ Λ 2 -
      hp.leadingCoeff • linearFunction (coordinateVector 2)^(d+2)) = 0 := by
  have he₂ : frameDrift (triangularDrift p) α β δ Λ 2 =
      hiddenAffinePullback α β δ (triangularDrift p 2) + partialDerivative 2 Λ := by
    simp [frameDrift,frameVectors,coordinate_directionalDerivative]
  have hz₀ := hidden_power_zero_of_first _ hg₀ (d+1)
  have hz₁ := hidden_power_zero_of_first _ hg₁ (d+1)
  have hfP : (partialDerivative 2 ^ 2)
      (hiddenAffinePullback α β δ (triangularDrift p 2)) = 0 := by
    simp only [pow_two,Module.End.mul_apply,hidden_partial_pullback]
    have he := triangularDrift_hidden_second_partial_zero p
    change partialDerivative 2 (partialDerivative 2 (triangularDrift p 2)) = 0 at he
    rw [he,map_zero]
  have hzP := hidden_power_zero_of_second _ hfP d
  have hzW := slanted_polynomial_leading_remainder_nilpotent hp α β δ
  have hpoly := smooth_eq_slanted_polynomial (partialDerivative 2 Λ) hp α β δ hw
  rw [← hpoly,hd] at hzW
  rw [he₂]
  have he : α • frameDrift (triangularDrift p) α β δ Λ 0 +
      β • frameDrift (triangularDrift p) α β δ Λ 1 +
      (hiddenAffinePullback α β δ (triangularDrift p 2) + partialDerivative 2 Λ) -
      hp.leadingCoeff • linearFunction (coordinateVector 2)^(d+2) =
      α • frameDrift (triangularDrift p) α β δ Λ 0 +
      β • frameDrift (triangularDrift p) α β δ Λ 1 +
      hiddenAffinePullback α β δ (triangularDrift p 2) +
      (partialDerivative 2 Λ-hp.leadingCoeff • linearFunction (coordinateVector 2)^(d+2)) := by
    abel
  rw [he]
  simp only [map_add,map_smul,hz₀,hz₁,hzP,hzW,smul_zero,zero_add]

end Wong.SmoothModel


/-! Source segment: SectorIHiddenElimination -/

/-! Actual elimination of hidden affine slopes. Every transformed operator
belongs to the image of the original estimation algebra. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel
set_option maxHeartbeats 1200000

theorem affine_hidden_slopes_zero {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (hx₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (hx₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters) (hform : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (hb₂ : p.b₂ = 0) : p.k₃ = 0 ∧ p.h₃ = 0 := by
  by_contra hzero
  have hne : p.k₃ ≠ 0 ∨ p.h₃ ≠ 0 := by tauto
  have hμ := ne_of_gt (hiddenSlopeNorm_pos p hne)
  obtain ⟨G⟩ := exists_canonicalGaugeData f h hrank hq hx₀ hx₁ p hform
  let E := gaugeAlgebra G.Λ (estimationAlgebra f h)
  let : FiniteDimensional ℝ E := G.finiteDimensional
  let α := hiddenSlopeAlpha p
  let β := hiddenSlopeBeta p
  let δ := hiddenSlopeDelta p
  obtain ⟨Λ,B,hB,hJ⟩ := exists_normalized_hiddenEuler E (triangularDrift p) (eta f h)
    p G.wong_eq hμ hb₁ hb₂ G.filtering_mem G.D_zero_mem G.D_one_mem
  let F := hiddenFrameAlgebra α β δ Λ E
  let : FiniteDimensional ℝ F := hiddenFrameAlgebra_finiteDimensional α β δ Λ E
  have hfinite : F ≤ finiteOrderAlgebra :=
    hiddenFrameAlgebra_le_finiteOrder α β δ Λ E G.finiteOrder
  have hnormal : F ≤ normalFormOperators :=
    hiddenFrameAlgebra_le_normalFormOperators α β δ Λ E G.normalForm
  have hfun : AdaptedFunctionSpace F :=
    hiddenFrameAlgebra_adaptedFunctionSpace α β δ Λ E G.functionSpace
  have hheat : partialDerivative 2 ^ 2 ∈ F :=
    actual_hiddenFrame_pure_second_mem E G.finiteOrder G.normalForm
      (triangularDrift p) (eta f h) α β δ Λ B G.filtering_mem hB hJ
  let g := frameDrift (triangularDrift p) α β δ Λ
  let V := hiddenAffinePullback α β δ (eta f h)
  have hL : directionalDiffusion α β g V ∈ F := by
    rw [← actual_transported_filteringOperator]
    exact hiddenFrame_image_mem α β δ Λ E _ G.filtering_mem
  obtain ⟨hg₀,hg₁⟩ := normalized_frameDrift_visible_independent E (triangularDrift p)
    α β δ Λ B hfun hB hJ G.D_zero_mem G.D_one_mem
  obtain ⟨q,hqeval⟩ := actual_normalizing_gauge_hidden_polynomial E G.finiteOrder
    (triangularDrift p) (eta f h) α β δ Λ B hfun hB hJ
    G.filtering_mem G.D_zero_mem G.D_one_mem
    (triangularDrift_hidden_visible_partial_zero p 0 (by decide))
    (triangularDrift_hidden_visible_partial_zero p 1 (by decide))
    (triangularDrift_hidden_second_partial_zero p)
  by_cases hd : q.natDegree ≤ 1
  · obtain ⟨c,v,hv,he⟩ := normalized_low_hidden_first_coefficient p α β δ Λ q
      hqeval hd hg₀ hg₁
    have hz := actual_low_frameDiffusion_hidden_slopes_zero F hfinite hnormal B hB hJ
      α β p.k₃ p.h₃ c g V v hg₀ hg₁ hv he hL hheat
    exact hzero hz
  · let d := q.natDegree-2
    have hdegree : q.natDegree = d+2 := by dsimp [d]; omega
    have hres := normalized_high_hidden_first_nilpotent p α β δ Λ q d hdegree
      hqeval hg₀ hg₁
    have hz := actual_high_frameDiffusion_obstruction F hfinite hnormal B hB hJ
      α β q.leadingCoeff d g V hg₀ hg₁ hres hL hheat
    have hqne : q ≠ 0 := by
      intro he
      simp [he] at hd
    exact (Polynomial.leadingCoeff_ne_zero.mpr hqne) hz

end Wong.SmoothModel



/-! Source segment: MainReduction -/

/-! The remaining Sector II statement has exactly the original model
assumptions together with affine coefficients already proved to vanish.
The reduction below is conditional until that statement is proved. -/

noncomputable section
set_option autoImplicit false
namespace Wong.SmoothModel

def RemainingVisibleAffineSlopesClaim : Prop :=
  ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    QuadraticFree (estimationAlgebra f h) →
    multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h →
    multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h →
    ∀ (p : Wong.AffineParameters),
      (∀ i j x, (wong f i j).1 x = p.matrix x i j) →
      p.b₁ = 0 → p.b₂ = 0 → p.k₃ = 0 → p.h₃ = 0 →
      p.k₁ = 0 ∧ p.k₂ = 0 ∧ p.h₂ = 0

theorem quadraticFreeMainClaim_of_remaining_visible_affine_slopes
    (H : RemainingVisibleAffineSlopesClaim) : QuadraticFreeMainClaim := by
  apply quadraticFreeMainClaim_iff_adaptedConstancyClaim.mpr
  intro m f h hFD hrank hq hx₀ hx₁
  letI := hFD
  obtain ⟨p,hform⟩ := shi_yau_affine_structure f h hrank hx₀ hx₁
  obtain ⟨hb₁,hb₂⟩ := VisibleHeads.visible_slopes_zero f h hrank hq hx₀ hx₁ p hform
  obtain ⟨hk₃,hh₃⟩ := affine_hidden_slopes_zero f h hrank hq hx₀ hx₁ p hform hb₁ hb₂
  obtain ⟨hk₁,hk₂,hh₂⟩ := H m f h hFD hrank hq hx₀ hx₁ p hform hb₁ hb₂ hk₃ hh₃
  exact wongConstant_of_independent_affine_slopes_zero f p hform
    hb₁ hb₂ hk₁ hk₂ hk₃ hh₂ hh₃

end Wong.SmoothModel
