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
  journal-version/   — standalone journal-format manuscript

lean/
  Wong/                        — Lean 4 proof modules (164 files)
  Wong.lean                    — top-level import
  Wong/MainStatement.lean      — formal statement of the main claim
  Wong/MainProof.lean          — proof assembly
  Wong/ShiYau2020MainProof.lean — internal proof of the Shi–Yau 2020
                                 function-element affineness theorem
  Wong/PublishedAffineInput.lean — internal proof of the Shi–Yau 2017
                                 affine structure theorem
  Wong/UnconditionalMainProof.lean — compatibility name for the main theorem
  AxiomAudit.lean              — #print axioms for every theorem
  ProofRouteAudit.lean         — expands the public statements and traces
                                 the actual proof terms (no circularity)
  verification/                — acceptance certificates and per-module logs
    mitter-main/               — verification address for the main theorem
    shi-yau-2020/              — verification address for the Shi–Yau 2020 result
  reports/                     — correspondence and audit reports
  lakefile.toml                — Lake build configuration
  lean-toolchain               — Lean version (leanprover/lean4:v4.35.0-rc2)
```

The two verifications have separate addresses that share a common parent,
`lean/verification/`:

- main theorem — `lean/verification/mitter-main/`
- Shi–Yau 2020 — `lean/verification/shi-yau-2020/`

Each address carries a README stating the exact theorem it certifies, the
module that proves it, and how to reproduce the check.

The Shi–Yau 2017 and 2020 structural results are verified **within this same
package**, not in a separate tree: their proofs share the model layer and the
affine/Euler machinery with the main proof, and the dependency closure of
`Wong/ShiYau2020MainProof.lean` and `Wong/PublishedAffineInput.lean` spans 157
of the 164 modules. `verification/acceptance.json` records a single acceptance
run covering all of them.

## What the main claim says

In `lean/Wong/MainStatement.lean`:

```lean
def mainClaim : Prop :=
  ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 → WongConstant f
```

This matches the paper's main theorem exactly: state dimension 3, linear rank 2,
finite-dimensional estimation algebra → Wong matrix is constant. **There is no
quadratic-freeness premise.**

`QuadraticFree` is not assumed; it is *derived*. The chain is:

1. `shiYau2020_mitter_theorem` (`Wong/ShiYau2020MainProof.lean`) independently
   proves that every function element is affine, from finite-dimensionality and
   rank two alone.
2. `quadraticFree_of_finiteDimensional_rank_two` (`Wong/MainProof.lean`) turns
   affineness of function elements into `QuadraticFree`.
3. `main_theorem` applies slope elimination to conclude constancy.

The quadratic-free statement is retained separately as `QuadraticFreeMainClaim`
(`quadraticFree_main_theorem`), an intermediate used only within slope
elimination. It is not the public result.

## How to verify the Lean proof

### Prerequisites

Install `elan` (the Lean version manager):

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

The `lean-toolchain` file pins the exact Lean version. `elan` will download it
automatically on first build.

### Build

```sh
cd lean/
lake exe cache get   # download prebuilt Mathlib cache (~1 GB, saves hours)
lake build           # compile the full proof
```

A clean build with no errors means the formal proof is accepted by the Lean kernel.

### Check for sorry

```sh
grep -rn "sorry" lean/Wong/ lean/Wong.lean
```

This should return no output.

### Verify the axiom base

```sh
cd lean/
lake env lean AxiomAudit.lean 2>&1 | grep -v "^#"
```

Every theorem should list only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.

### Full audit

```sh
cd lean/
./check.sh --clean --jobs 4
```

This rebuilds every module from source, checks the transitive axiom
dependencies of all local theorems and lemmas, and traces the actual proof
terms of the public statements. Acceptance evidence is in `verification/`.

### Scope

The formalization covers the Shi–Yau 2017 Theorems 3.4 and 3.10 and the
Shi–Yau 2020 Theorems 1.1, 1.2, 3.7, and 3.10 together with the structural
results those depend on. It does **not** cover the numerical experiments or
the filter implementations in either paper.

## References

- Shi, J. and Yau, S.S.-T. (2017). *Finite Dimensional Estimation Algebras with State Dimension 3 and rank 2, I.* SIAM J. Control Optim. 55(6):4227–4246.
- Shi, J. and Yau, S.S.-T. (2020). *Finite dimensional estimation algebras with state dimension 3 and rank 2, Mitter conjecture.* Intl. J. Control 93(9):2177–2186.
- Yu, H., Jiao, X., and Yau, S.S.-T. (2024). *Complete Classification of Finite Dimensional Estimation Algebras With State Dimension n, Linear Rank n−1, and Constant Wong Matrix.* IEEE TAC 69(1):295–302.
