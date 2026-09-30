import Wong.EulerHeadExtraction
import Wong.NormalSymbolsHeads
import Wong.HiddenEulerElement
import Wong.AffineFrameAlgebra
import Wong.GaugeNormalForm
import Wong.HiddenEulerNormalization

/-! Extraction of the actual constant hidden second derivative after affine
and gauge transport of the diffusion generator. -/

noncomputable section
namespace Wong.SmoothModel
open MvPolynomial
set_option maxHeartbeats 1000000

def hiddenDiffusionCoefficient (α β : ℝ) : ℝ := (1 + α^2 + β^2) / 2

theorem hiddenDiffusionCoefficient_pos (α β : ℝ) :
    0 < hiddenDiffusionCoefficient α β := by
  dsimp [hiddenDiffusionCoefficient]
  positivity

theorem filtering_double_affine_coordinate (f : Fin 3 → Smooth) (V : Smooth)
    (α β δ : ℝ) :
    ⁅⁅filteringOperator f V, multiplication (hiddenAffineCoordinate α β δ)⁆,
      multiplication (hiddenAffineCoordinate α β δ)⁆ =
      (2 * hiddenDiffusionCoefficient α β) • (1 : Operator) := by
  simp only [hiddenAffineCoordinate, multiplication_add, multiplication_smul,
    multiplication_smoothOne, lie_add, lie_scalar_identity, add_zero,
    lie_filteringOperator_linearFunction, lie_directionD_linearFunction,
    Fin.sum_univ_three]
  congr 1
  simp [hiddenDiffusionCoefficient]
  ring

theorem actualAlgEquiv_map_lie (C : Operator ≃ₐ[ℝ] Operator) (A B : Operator) :
    C ⁅A,B⁆ = ⁅C A, C B⁆ := by
  simp only [operator_lie_def, map_sub, map_mul]

def hiddenFrameGenerator (f : Fin 3 → Smooth) (V : Smooth)
    (α β δ : ℝ) (Λ : Smooth) : Operator :=
  gaugeConjugation Λ
    (affineConjugation (hiddenShear α β) ![0, 0, -δ] (filteringOperator f V))

theorem hiddenFrameGenerator_double_hidden_coordinate (f : Fin 3 → Smooth)
    (V : Smooth) (α β δ : ℝ) (Λ : Smooth) :
    ⁅⁅hiddenFrameGenerator f V α β δ Λ,
        multiplication (linearFunction (coordinateVector 2))⁆,
      multiplication (linearFunction (coordinateVector 2))⁆ =
      (2 * hiddenDiffusionCoefficient α β) • (1 : Operator) := by
  let C := (affineConjugation (hiddenShear α β) ![0, 0, -δ]).trans (gaugeConjugation Λ)
  have hc : C (multiplication (hiddenAffineCoordinate α β δ)) =
      multiplication (linearFunction (coordinateVector 2)) := by
    change gaugeConjugation Λ
      (affineConjugation (hiddenShear α β) ![0, 0, -δ]
        (multiplication (hiddenAffineCoordinate α β δ))) = _
    rw [affineConjugation_multiplication]
    change gaugeConjugation Λ (multiplication
      (hiddenAffinePullback α β δ (hiddenAffineCoordinate α β δ))) = _
    rw [hiddenAffinePullback_coordinate, gaugeConjugation_multiplication]
  have he := congrArg C (filtering_double_affine_coordinate f V α β δ)
  rw [actualAlgEquiv_map_lie, actualAlgEquiv_map_lie, hc, map_smul, map_one] at he
  exact he

theorem hiddenFrameGenerator_order (f : Fin 3 → Smooth) (V : Smooth)
    (α β δ : ℝ) (Λ : Smooth) :
    hiddenFrameGenerator f V α β δ Λ ∈ orderSpace 2 :=
  gaugeConjugation_mem_orderSpace Λ 2 _
    (affineConjugation_mem_orderSpace _ _ 2 _ (filteringOperator_mem_orderSpace_two f V))

theorem degree_eq_two_hidden_index (α : MultiIndex)
    (hdeg : α.degree ≤ 2) (hh : 1 < α 2) : α = Finsupp.single 2 2 := by
  have hd : α.degree = α 0 + α 1 + α 2 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
  have h0 : α 0 = 0 := by omega
  have h1 : α 1 = 0 := by omega
  have h2 : α 2 = 2 := by omega
  ext i
  fin_cases i <;> simp [h0, h1, h2]

theorem normal_hidden_second_coefficient (p : NormalForm) (c : ℝ)
    (hh : ⁅⁅normalAction p, multiplication (linearFunction (coordinateVector 2))⁆,
      multiplication (linearFunction (coordinateVector 2))⁆ = (2 * c) • (1 : Operator)) :
    p (Finsupp.single 2 2) = c • smoothOne := by
  have hmult : (2 * c) • (1 : Operator) = multiplication ((2 * c) • smoothOne) := by
    rw [multiplication_smul, multiplication_smoothOne]
  have he := normalSymbol_two_head p 2 2 ((2*c) • smoothOne) (hh.trans hmult)
  have hc := congrArg (fun q : SmoothSymbol => q.coeff 0) he
  have hi : (0 : MultiIndex) + Finsupp.single 2 1 + Finsupp.single 2 1 =
      Finsupp.single 2 2 := by ext i; simp [Finsupp.single_apply]; split_ifs <;> omega
  simp only [coeff_pderiv, hi, normalSymbol_coeff, Finsupp.degree_single,
    ite_true, Finsupp.zero_apply, Finsupp.add_apply, Finsupp.single_eq_same,
    coeff_C, ite_true] at hc
  apply Subtype.ext
  funext x
  have hx := congrArg (fun u : Smooth => u.1 x) hc
  simp only [smooth_coe_mul, smooth_coe_natCast, Submodule.coe_add,
    Pi.add_apply, smooth_coe_one, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, smoothOne] at hx ⊢
  norm_num at hx ⊢
  linarith

theorem normal_second_hidden_split (p : NormalForm) (c : ℝ)
    (horder : normalAction p ∈ orderSpace 2)
    (hh : ⁅⁅normalAction p, multiplication (linearFunction (coordinateVector 2))⁆,
      multiplication (linearFunction (coordinateVector 2))⁆ = (2 * c) • (1 : Operator)) :
    ∃ r : NormalForm, (∀ α, 1 < α 2 → r α = 0) ∧
      normalAction p = c • partialDerivative 2 ^ 2 + normalAction r := by
  let head := normalHiddenHead 2 c
  refine ⟨p - head, ?_, ?_⟩
  · intro α hhα
    have hd := normalDegreeLE_of_action_order p 2 horder
    by_cases hdeg : α.degree ≤ 2
    · have he := degree_eq_two_hidden_index α hdeg hhα
      subst α
      simp [head, normalHiddenHead, normal_hidden_second_coefficient p c hh]
    · have hz := hd α (by omega)
      have hne : (Finsupp.single 2 2 : MultiIndex) ≠ α := by
        intro he
        simp [← he, Finsupp.degree_single] at hdeg
      simp [head, normalHiddenHead, hz, hne]
  · rw [map_sub, normalAction_hiddenHead]
    abel

theorem actual_hiddenFrame_pure_second_mem
    (E : LieSubalgebra ℝ Operator) [FiniteDimensional ℝ E]
    (hfinite : E ≤ finiteOrderAlgebra) (hnormal : E ≤ normalFormOperators)
    (f : Fin 3 → Smooth) (V : Smooth) (α β δ : ℝ) (Λ B : Smooth)
    (hL : filteringOperator f V ∈ E) (hB : partialDerivative 2 B = 0)
    (hJ : hiddenEuler + multiplication B ∈ hiddenFrameAlgebra α β δ Λ E) :
    partialDerivative 2 ^ 2 ∈ hiddenFrameAlgebra α β δ Λ E := by
  let F := hiddenFrameAlgebra α β δ Λ E
  let : FiniteDimensional ℝ F := hiddenFrameAlgebra_finiteDimensional α β δ Λ E
  have hFfinite : F ≤ finiteOrderAlgebra := hiddenFrameAlgebra_le_finiteOrder α β δ Λ E hfinite
  have hFnormal : F ≤ normalFormOperators := hiddenFrameAlgebra_le_normalFormOperators α β δ Λ E hnormal
  have hLmem : hiddenFrameGenerator f V α β δ Λ ∈ F :=
    hiddenFrame_image_mem α β δ Λ E _ hL
  obtain ⟨p, hp⟩ := hFnormal hLmem
  have horder : normalAction p ∈ orderSpace 2 := by
    rw [hp]
    exact hiddenFrameGenerator_order f V α β δ Λ
  have hh : ⁅⁅normalAction p, multiplication (linearFunction (coordinateVector 2))⁆,
      multiplication (linearFunction (coordinateVector 2))⁆ =
      (2 * hiddenDiffusionCoefficient α β) • (1 : Operator) := by
    rw [hp]
    exact hiddenFrameGenerator_double_hidden_coordinate f V α β δ Λ
  obtain ⟨r, hr, he⟩ := normal_second_hidden_split p (hiddenDiffusionCoefficient α β) horder hh
  have hP : hiddenDiffusionCoefficient α β • partialDerivative 2 ^ 2 + normalAction r ∈ F := by
    rw [← he, hp]
    exact hLmem
  exact hidden_second_derivative_mem F hFfinite B hB hJ r hr _
    (ne_of_gt (hiddenDiffusionCoefficient_pos α β)) hP

end Wong.SmoothModel
