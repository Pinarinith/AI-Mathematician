import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
Exact affine normal form used in the manuscript.  Constancy here refers to
the matrix-valued function, not to the estimation Lie algebra.
No finite-dimensionality-to-zero-slope implication is assumed or asserted.
-/

namespace Wong

structure AffineParameters where
  b₀ : ℝ
  b₁ : ℝ
  b₂ : ℝ
  k₀ : ℝ
  k₁ : ℝ
  k₂ : ℝ
  k₃ : ℝ
  h₀ : ℝ
  h₁ : ℝ
  h₂ : ℝ
  h₃ : ℝ

abbrev Point := Fin 3 → ℝ

def AffineParameters.w12 (p : AffineParameters) (x : Point) : ℝ :=
  p.b₁ * x 0 + p.b₂ * x 1 + p.b₀

def AffineParameters.w13 (p : AffineParameters) (x : Point) : ℝ :=
  p.k₁ * x 0 + p.k₂ * x 1 + p.k₃ * x 2 + p.k₀

def AffineParameters.w23 (p : AffineParameters) (x : Point) : ℝ :=
  p.h₁ * x 0 + p.h₂ * x 1 + p.h₃ * x 2 + p.h₀

def AffineParameters.matrix (p : AffineParameters) (x : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, p.w12 x, p.w13 x;
     -p.w12 x, 0, p.w23 x;
     -p.w13 x, -p.w23 x, 0]

def AffineParameters.ZeroSlopes (p : AffineParameters) : Prop :=
  p.b₁ = 0 ∧ p.b₂ = 0 ∧ p.k₁ = 0 ∧ p.k₂ = 0 ∧ p.k₃ = 0 ∧
  p.h₁ = 0 ∧ p.h₂ = 0 ∧ p.h₃ = 0

def AffineParameters.ConstantMatrix (p : AffineParameters) : Prop :=
  ∀ x y : Point, p.matrix x = p.matrix y

theorem affine_constancy_iff_zero_slopes (p : AffineParameters) :
    p.ConstantMatrix ↔ p.ZeroSlopes := by
  constructor
  · intro H
    have h (x : Point) (i j : Fin 3) := congrArg (fun A => A i j) (H x 0)
    have hb₁ := h ![1, 0, 0] 0 1
    have hb₂ := h ![0, 1, 0] 0 1
    have hk₁ := h ![1, 0, 0] 0 2
    have hk₂ := h ![0, 1, 0] 0 2
    have hk₃ := h ![0, 0, 1] 0 2
    have hh₁ := h ![1, 0, 0] 1 2
    have hh₂ := h ![0, 1, 0] 1 2
    have hh₃ := h ![0, 0, 1] 1 2
    simp [AffineParameters.matrix, AffineParameters.w12, AffineParameters.w13,
      AffineParameters.w23] at hb₁ hb₂ hk₁ hk₂ hk₃ hh₁ hh₂ hh₃
    exact ⟨hb₁, hb₂, hk₁, hk₂, hk₃, hh₁, hh₂, hh₃⟩
  · rintro ⟨hb₁, hb₂, hk₁, hk₂, hk₃, hh₁, hh₂, hh₃⟩ x y
    simp [AffineParameters.matrix, AffineParameters.w12, AffineParameters.w13,
      AffineParameters.w23, hb₁, hb₂, hk₁, hk₂, hk₃, hh₁, hh₂, hh₃]

/-- The Bianchi identity reduces to this scalar equality in the affine form. -/
theorem affine_bianchi (p : AffineParameters) (h : 0 - p.k₂ + p.h₁ = 0) :
    p.h₁ = p.k₂ := by linarith

end Wong
