# Mitter Conjecture: Constancy of the Wong Matrix (State Dim 3, Rank 2)

This directory contains the paper and its Lean 4 formal proof for:

> **Finite Dimensional Estimation Algebra with State Dimension 3 and Rank 2: Constancy of Wong Matrix**
> Songlin Zhou, 2026.

The paper proves that the Wong matrix $\Omega$ is constant for any finite-dimensional estimation algebra of a smooth nonlinear filtering system on $\mathbb{R}^3$ with state dimension 3 and linear rank 2. This removes the constant-Wong-matrix assumption required by Yu–Jiao–Yau (2024) for the rank-$n{-}1$ classification in this special case.

## Contents

```
paper/
  main_tCON.tex      — LaTeX source
  main_tCON.pdf      — compiled paper
  ref.bib            — bibliography
  tCON2e.cls         — journal class file (IEEE Trans. Control)

lean/
  Wong/              — Lean 4 proof modules (~90 files)
  Wong.lean          — top-level import
  MainStatement.lean — formal statement of the main claim
  MainProof.lean     — proof assembly
  PublishedFullEquivalence.lean — equivalence to the published Shi–Yau formulation
  AxiomAudit.lean    — #print axioms for every theorem
  lakefile.toml      — Lake build configuration
  lean-toolchain     — Lean version (leanprover/lean4:v4.35.0-rc2)
```

## How to verify the Lean proof

### Prerequisites

Install `elan` (the Lean version manager):

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

The `lean-toolchain` file pins the exact Lean version. `elan` will download it automatically on first build.

### Build

```sh
cd lean/
lake exe cache get   # download prebuilt Mathlib cache (~1 GB, saves hours)
lake build           # compile the full proof
```

A clean build with no errors means the formal proof is accepted by the Lean kernel.

### Check for sorry

The proof must contain no `sorry` (unverified axiom placeholders):

```sh
grep -r "sorry" lean/Wong/ lean/Wong.lean lean/MainProof.lean
```

This should return no output. You can also run the included audit script:

```sh
cd lean/
python3 audit_sources.py
```

### Verify the axiom base

To confirm the proof rests only on standard Lean/Mathlib axioms (`propext`, `funext`, `Classical.choice`, `Quot.sound`), compile `AxiomAudit.lean` and inspect the output:

```sh
lake env lean AxiomAudit.lean 2>&1 | grep -v "^#"
```

Every theorem should list only those four axioms.

### Check published equivalence

`PublishedFullEquivalence.lean` proves that the Lean main claim is logically equivalent to the statement as published in Shi–Yau (2017/2020). Build it with:

```sh
lake env lean lean/Wong/PublishedFullEquivalence.lean
```

No output means the equivalence proof compiles cleanly.

### What the main claim says

In `lean/Wong/MainStatement.lean`:

```lean
def mainClaim : Prop :=
  ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    QuadraticFree (estimationAlgebra f h) →
    WongConstant f
```

This matches the paper's main theorem exactly: state dimension 3, linear rank 2, finite-dimensional estimation algebra, quadratic-free (non-maximal rank) → Wong matrix is constant.

## References

- Shi, J. and Yau, S.S.-T. (2017). *Finite Dimensional Estimation Algebras with State Dimension 3 and rank 2, I.* SIAM J. Control Optim. 55(6):4227–4246.
- Shi, J. and Yau, S.S.-T. (2020). *Finite dimensional estimation algebras with state dimension 3 and rank 2, Mitter conjecture.* Intl. J. Control 93(9):2177–2186.
- Yu, H., Jiao, X., and Yau, S.S.-T. (2024). *Complete Classification of Finite Dimensional Estimation Algebras With State Dimension n, Linear Rank n−1, and Constant Wong Matrix.* IEEE TAC 69(1):295–302.
