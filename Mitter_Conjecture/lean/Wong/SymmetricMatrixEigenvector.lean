import Mathlib.Analysis.Matrix.Spectrum

/-!
# A nonzero symmetric matrix column detects a nonzero eigenmode

This is a finite-dimensional real spectral theorem consequence. A nonzero
column at index `i` supplies a nonzero real eigenvalue with an eigenvector
whose `i`-th coordinate is nonzero. No Wong or published theorem is imported.
-/

noncomputable section
namespace Wong

/-- A nonzero column of a real symmetric matrix is witnessed by a nonzero
eigenvalue and an eigenvector with nonzero coordinate in that column. -/
theorem symmetric_matrix_nonzero_column_eigenvector {n : Type*}
    [Fintype n] [DecidableEq n] (Q : Matrix n n ℝ) (hQ : Q.IsSymm)
    (i : n) (hne : Q.mulVec (Pi.single i 1) ≠ 0) :
    ∃ (lam : ℝ) (v : n → ℝ), lam ≠ 0 ∧ v i ≠ 0 ∧ Q.mulVec v = lam • v := by
  let hH : Q.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hQ
  let b := hH.eigenvectorBasis
  let e : EuclideanSpace ℝ n := EuclideanSpace.single i 1
  have hT : Q.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have heig (j : n) : Q.toEuclideanLin (b j) = hH.eigenvalues j • b j := by
    ext k
    exact congrFun (hH.mulVec_eigenvectorBasis j) k
  have hw : Q.toEuclideanLin e ≠ 0 := by
    intro hz
    apply hne
    funext k
    have hk := congrArg (fun u : EuclideanSpace ℝ n => u k) hz
    simpa [e, Matrix.toLpLin_apply] using hk
  have hex : ∃ j : n, b.repr (Q.toEuclideanLin e) j ≠ 0 := by
    by_contra! hn
    apply hw
    apply b.repr.injective
    ext j
    simpa only [map_zero, PiLp.zero_apply] using hn j
  obtain ⟨j, hj⟩ := hex
  have heq : b.repr (Q.toEuclideanLin e) j = hH.eigenvalues j * b j i := by
    rw [b.repr_apply_apply, ← hT, heig]
    simp [e, inner_smul_left, EuclideanSpace.inner_single_right]
  rw [heq] at hj
  exact ⟨hH.eigenvalues j, fun k => b j k,
    (mul_ne_zero_iff.mp hj).1, (mul_ne_zero_iff.mp hj).2,
    hH.mulVec_eigenvectorBasis j⟩

/-- The hidden-coordinate version used for a real symmetric three-dimensional Hessian. -/
theorem symmetric_three_hidden_column_eigenvector
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm)
    (hne : Q.mulVec (Pi.single (2 : Fin 3) 1) ≠ 0) :
    ∃ (lam : ℝ) (v : Fin 3 → ℝ),
      lam ≠ 0 ∧ v 2 ≠ 0 ∧ Q.mulVec v = lam • v :=
  symmetric_matrix_nonzero_column_eigenvector Q hQ 2 hne

end Wong
