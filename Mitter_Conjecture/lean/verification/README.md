# Lean verification — GitHub: Mitter Conjecture

This directory holds the machine-checked proofs for the paper

> **Finite Dimensional Estimation Algebra with State Dimension 3 and Rank 2:
> Constancy of Wong Matrix** — Songlin Zhou.

It contains **two independent entry points**, each with its own address:

| Result | Entry point |
| --- | --- |
| Main theorem of the paper (Wong matrix is constant) | [`mitter-main/`](mitter-main/) |
| Shi–Yau 2020 function-element affineness (Mitter's conjecture) | [`shi-yau-2020/`](shi-yau-2020/) |

Both share one Lean package so that the two proofs can reuse the same model
layer, the same affine/Euler machinery, and the same audit scripts. Each
subdirectory states the exact theorem it certifies, the module that proves it,
and the command that reproduces the check.

## The package

- `Wong/` — 164 Lean modules shared by both verifications.
- `lean-toolchain` — `leanprover/lean4:v4.35.0-rc2`.
- `lakefile.toml` — Mathlib and dependencies, pinned by revision.

## Reproducing

```sh
cd lean/
lake exe cache get   # prebuilt Mathlib cache, ~1 GB
lake build           # checks both entry points
```

A clean build with no errors means the Lean kernel accepts both proofs.
For the full audit (source rebuild, axiom dependencies, proof-term tracing):

```sh
cd lean/
./check.sh --clean --jobs 4
```

## Trust base

The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
`AxiomAudit.lean` checks the transitive axiom dependencies of every local
theorem and lemma; `ProofRouteAudit.lean` expands the public statements and
traces the real proof terms to rule out circularity. Mathlib and its
dependencies come from a pinned revision's existing build cache — the Lean
compiler and third-party libraries are not rebuilt from source here.

## Scope

Covers the Shi–Yau 2017 Theorems 3.4 and 3.10 and the Shi–Yau 2020
Theorems 1.1, 1.2, 3.7, and 3.10 together with the structural results they
depend on. It does **not** cover the numerical experiments or filter
implementations in either paper.
