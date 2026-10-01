# Shi–Yau 2020: function elements are affine (Mitter's conjecture)

Certifies the Shi–Yau 2020 structural theorem that the paper builds on.

## Statement

`Wong/ShiYau2020MainProof.lean`:

```lean
theorem shiYau2020_mitter_theorem : ShiYau2020MitterClaim
```

Every function element of a finite-dimensional estimation algebra with state
dimension 3 and linear rank 2 is affine. This is Mitter's conjecture, proposed
at the ICM in 1983, in this setting.

## Proof

`Wong/ShiYau2020MainProof.lean` proves the result by an exhaustive
classification of the actually occurring quadratic function elements: each of
the five cases yields an affine function element, contradicting the existence
of a genuine quadratic one. It does **not** assume `QuadraticFree` or any
classification branch as a hypothesis, and it does not depend on the main
constancy theorem — the dependency runs the other way.

The same file also verifies the Shi–Yau 2017 affine structure theorem
(`Wong/PublishedAffineInput.lean`, Theorems 3.4 and 3.10), which supplies the
affine shape of the Wong matrix used in both proofs.

## Reproducing

```sh
cd lean/
lake exe cache get
lake build
```

Then check the statement and the axiom base:

```sh
cd lean/
lake env lean ProofRouteAudit.lean
lake env lean AxiomAudit.lean
```

`ProofRouteAudit.lean` expands `shiYau2020_mitter_theorem` and checks that no
literature result is introduced as an axiom and that the main theorem depends
on it, rather than the converse.
