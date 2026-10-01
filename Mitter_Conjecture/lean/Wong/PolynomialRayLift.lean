import Wong.PolynomialSmooth
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Translation along a real direction, with polynomial position coefficients.
The leading ray coefficient is independent of the base point.  Linear moments
are taken coefficientwise, so their leading term records only total mass. -/
noncomputable section
namespace Wong.SmoothModel
open MvPolynomial

def rayCoordinate (v : State) (i : Fin 3) : Polynomial RealPoly :=
  Polynomial.C (X i) + Polynomial.C (C (v i)) * Polynomial.X

def rayLift (v : State) : RealPoly →+* Polynomial RealPoly :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) (rayCoordinate v)

@[simp] theorem rayLift_C (v : State) (c : ℝ) :
    rayLift v (C c) = Polynomial.C (C c) := by
  simp [rayLift]

@[simp] theorem rayLift_X (v : State) (i : Fin 3) :
    rayLift v (X i) = rayCoordinate v i := by
  exact MvPolynomial.eval₂Hom_X' _ _ _

theorem rayCoordinate_degree (v : State) (i : Fin 3) :
    (rayCoordinate v i).natDegree ≤ 1 := by
  unfold rayCoordinate
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact (Polynomial.natDegree_mul_le).trans (by simp)

@[simp] theorem rayCoordinate_coeff_one (v : State) (i : Fin 3) :
    (rayCoordinate v i).coeff 1 = C (v i) := by
  simp [rayCoordinate]

theorem polynomial_product_natDegree_le {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial RealPoly) (n : ι → ℕ)
    (hp : ∀ i ∈ s, (p i).natDegree ≤ n i) :
    (∏ i ∈ s, p i).natDegree ≤ ∑ i ∈ s, n i := by
  exact (Polynomial.natDegree_prod_le s p).trans (Finset.sum_le_sum hp)

theorem polynomial_product_coeff_bound {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial RealPoly) (n : ι → ℕ)
    (hp : ∀ i ∈ s, (p i).natDegree ≤ n i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (p i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le
      (hp i (Finset.mem_insert_self _ _))
      (polynomial_product_natDegree_le s p n
        (fun j hj => hp j (Finset.mem_insert_of_mem hj)))]
    rw [ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]

theorem rayLift_monomial (v : State) (α : Fin 3 →₀ ℕ) (c : ℝ) :
    rayLift v (monomial α c) = Polynomial.C (C c) *
      ∏ i ∈ α.support, (rayCoordinate v i)^(α i) := by
  rw [rayLift, eval₂Hom_monomial]
  rfl

theorem rayLift_monomial_degree (v : State) (α : Fin 3 →₀ ℕ) (c : ℝ) :
    (rayLift v (monomial α c)).natDegree ≤ α.degree := by
  rw [rayLift_monomial]
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add, Finsupp.degree_apply]
  apply polynomial_product_natDegree_le
  intro i _
  exact (Polynomial.natDegree_pow_le).trans (by
    simpa using Nat.mul_le_mul_left (α i) (rayCoordinate_degree v i))

theorem rayLift_monomial_top (v : State) (α : Fin 3 →₀ ℕ) (c : ℝ) :
    (rayLift v (monomial α c)).coeff α.degree = C (eval v (monomial α c)) := by
  have hp (i : Fin 3) : ((rayCoordinate v i)^(α i)).natDegree ≤ α i :=
    Polynomial.natDegree_pow_le.trans (by
      simpa using Nat.mul_le_mul_left (α i) (rayCoordinate_degree v i))
  rw [rayLift_monomial, Polynomial.coeff_C_mul, Finsupp.degree_apply,
    polynomial_product_coeff_bound _ _ _ (fun i _ => hp i)]
  have hc (i : Fin 3) : ((rayCoordinate v i)^(α i)).coeff (α i)=(C (v i))^(α i) := by
    simpa using Polynomial.coeff_pow_of_natDegree_le (m := α i) (rayCoordinate_degree v i)
  simp only [hc, eval_monomial, map_mul, map_prod, map_pow, Finsupp.prod]

theorem rayLift_natDegree_le (v : State) (p : RealPoly) :
    (rayLift v p).natDegree ≤ p.totalDegree := by
  have he : rayLift v p = ∑ α ∈ p.support, rayLift v (monomial α (p.coeff α)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [he]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro α hα
  exact (rayLift_monomial_degree v α _).trans (le_totalDegree hα)

/-- At any degree bound, only the corresponding highest homogeneous part
contributes to the ray coefficient. -/
theorem rayLift_coeff_of_degree_le (v : State) (p : RealPoly) (d : ℕ)
    (hp : p.totalDegree ≤ d) :
    (rayLift v p).coeff d = C (eval v (homogeneousComponent d p)) := by
  have hm (α : Fin 3 →₀ ℕ) (hα : α ∈ p.support) :
      (rayLift v (monomial α (p.coeff α))).coeff d =
        if α.degree = d then C (eval v (monomial α (p.coeff α))) else 0 := by
    split_ifs with he
    · rw [← he, rayLift_monomial_top]
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((rayLift_monomial_degree v α _).trans_lt
          (lt_of_le_of_ne ((le_totalDegree hα).trans hp) he))
  have hsum : (rayLift v p).coeff d =
      ∑ α ∈ p.support, (rayLift v (monomial α (p.coeff α))).coeff d := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum, Polynomial.finsetSum_coeff]
  rw [hsum, homogeneousComponent_apply, map_sum, map_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl hm

theorem rayLift_eval (v x : State) (t : ℝ) (p : RealPoly) :
    Polynomial.eval₂ (eval x) t (rayLift v p) = eval (x+t•v) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval₂_mul, hp, rayLift_X, rayCoordinate,
      Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_X, eval_X, eval_C,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem rayLift_base_eval (v x : State) (t : ℝ) (p : RealPoly) :
    eval x ((rayLift v p).eval (C t))=eval (x+t•v) p := by
  have he := Polynomial.eval₂_at_apply (p := rayLift v p) (eval x) (C t)
  rw [eval_C] at he
  rw [← he, rayLift_eval]

/-- Coefficientwise application of a real linear test functional. -/
def polynomialMoment (F : RealPoly →ₗ[ℝ] ℝ) (p : Polynomial RealPoly) : Polynomial ℝ :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange F (map_zero F)))

@[simp] theorem polynomialMoment_coeff (F : RealPoly →ₗ[ℝ] ℝ)
    (p : Polynomial RealPoly) (d : ℕ) : (polynomialMoment F p).coeff d=F (p.coeff d) := rfl

theorem polynomialMoment_add (F : RealPoly →ₗ[ℝ] ℝ) (p q : Polynomial RealPoly) :
    polynomialMoment F (p+q)=polynomialMoment F p+polynomialMoment F q := by
  ext d
  simp only [polynomialMoment_coeff, Polynomial.coeff_add, map_add]

theorem polynomialMoment_monomial (F : RealPoly →ₗ[ℝ] ℝ) (d : ℕ) (p : RealPoly) :
    polynomialMoment F (Polynomial.monomial d p)=Polynomial.monomial d (F p) := by
  ext n
  simp only [polynomialMoment_coeff, Polynomial.coeff_monomial]
  split_ifs <;> simp

theorem polynomialMoment_eval (F : RealPoly →ₗ[ℝ] ℝ) (p : Polynomial RealPoly) (t : ℝ) :
    (polynomialMoment F p).eval t=F (p.eval (C t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [polynomialMoment_add, Polynomial.eval_add, map_add, hp, hq]
  | monomial n p =>
    rw [polynomialMoment_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial]
    rw [show p * C t ^ n = (t^n) • p by rw [← map_pow, mul_comm, smul_eq_C_mul]]
    rw [map_smul, smul_eq_mul, mul_comm]

theorem polynomialMoment_degree (F : RealPoly →ₗ[ℝ] ℝ) (p : Polynomial RealPoly) :
    (polynomialMoment F p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro d hd
  rw [polynomialMoment_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hd, map_zero]

def rayMoment (F : RealPoly →ₗ[ℝ] ℝ) (v : State) (p : RealPoly) : Polynomial ℝ :=
  polynomialMoment F (rayLift v p)

@[simp] theorem rayMoment_zero (F : RealPoly →ₗ[ℝ] ℝ) (v : State) :
    rayMoment F v 0 = 0 := by
  ext n
  simp [rayMoment, polynomialMoment_coeff]

theorem rayMoment_add (F : RealPoly →ₗ[ℝ] ℝ) (v : State) (p q : RealPoly) :
    rayMoment F v (p+q)=rayMoment F v p+rayMoment F v q := by
  unfold rayMoment
  rw [map_add, polynomialMoment_add]

theorem rayMoment_neg (F : RealPoly →ₗ[ℝ] ℝ) (v : State) (p : RealPoly) :
    rayMoment F v (-p) = -rayMoment F v p := by
  ext n
  simp only [rayMoment, polynomialMoment_coeff, map_neg, Polynomial.coeff_neg]

theorem rayMoment_sub (F : RealPoly →ₗ[ℝ] ℝ) (v : State) (p q : RealPoly) :
    rayMoment F v (p-q)=rayMoment F v p-rayMoment F v q := by
  rw [sub_eq_add_neg, rayMoment_add, rayMoment_neg, sub_eq_add_neg]

theorem rayMoment_sum {ι : Type*} (F : RealPoly →ₗ[ℝ] ℝ) (v : State)
    (s : Finset ι) (p : ι → RealPoly) :
    rayMoment F v (∑i∈s,p i)=∑i∈s,rayMoment F v (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, rayMoment_add, ih, Finset.sum_insert hi]

theorem rayMoment_eval (F : RealPoly →ₗ[ℝ] ℝ) (v : State) (p : RealPoly) (t : ℝ) :
    (rayMoment F v p).eval t = F ((rayLift v p).eval (C t)) :=
  polynomialMoment_eval F _ t

theorem rayMoment_degree (F : RealPoly →ₗ[ℝ] ℝ) (v : State) (p : RealPoly) :
    (rayMoment F v p).natDegree ≤ p.totalDegree :=
  (polynomialMoment_degree _ _).trans (rayLift_natDegree_le _ _)

theorem rayMoment_top (F : RealPoly →ₗ[ℝ] ℝ) (v : State) (p : RealPoly) (d : ℕ)
    (hp : p.totalDegree ≤ d) :
    (rayMoment F v p).coeff d = eval v (homogeneousComponent d p) * F 1 := by
  rw [rayMoment, polynomialMoment_coeff, rayLift_coeff_of_degree_le v p d hp]
  rw [show C (eval v (homogeneousComponent d p)) =
    eval v (homogeneousComponent d p) • (1 : RealPoly) by rw [smul_eq_C_mul, mul_one]]
  exact F.map_smul _ _

/-- Squaring a bounded-degree observation contributes the square of its top
homogeneous value to the top ray moment coefficient. -/
theorem rayMoment_square_coeff (F : RealPoly →ₗ[ℝ] ℝ) (v : State)
    (p : RealPoly) (d : ℕ) (hp : p.totalDegree ≤ d) :
    (rayMoment F v (p^2)).coeff (2*d) =
      (eval v (homogeneousComponent d p))^2 * F 1 := by
  rw [rayMoment, polynomialMoment_coeff, map_pow,
    Polynomial.coeff_pow_of_natDegree_le ((rayLift_natDegree_le v p).trans hp),
    rayLift_coeff_of_degree_le v p d hp, ← map_pow]
  rw [show C ((eval v (homogeneousComponent d p))^2) =
    (eval v (homogeneousComponent d p))^2 • (1 : RealPoly) by rw [smul_eq_C_mul, mul_one]]
  exact F.map_smul _ _

end Wong.SmoothModel

#print axioms Wong.SmoothModel.rayMoment_top

#print axioms Wong.SmoothModel.rayMoment_square_coeff
