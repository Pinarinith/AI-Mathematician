# Main theorem: constancy of the Wong matrix

Certifies the main result of the paper.

## Statement

`Wong/MainStatement.lean`:

```lean
def mainClaim : Prop :=
  ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 → WongConstant f
```

State dimension 3, linear rank 2, finite-dimensional estimation algebra
implies the Wong matrix is constant. There is no quadratic-freeness premise.

## Proof

`Wong/MainProof.lean` — `main_theorem : mainClaim`.

The argument does not assume `QuadraticFree`; it derives it. The chain is:

1. `shiYau2020_mitter_theorem` (verified independently at
   [`../shi-yau-2020/`](../shi-yau-2020/)) gives that every function element
   is affine, from finite-dimensionality and rank two alone.
2. `quadraticFree_of_finiteDimensional_rank_two` turns affineness into
   `QuadraticFree`.
3. `main_theorem` applies slope elimination to conclude constancy.

`Wong/UnconditionalMainProof.lean` keeps `unconditional_main_theorem` as a
compatibility name for the same result. The quadratic-free statement is
retained as `quadraticFree_main_theorem`, an intermediate used only inside
slope elimination; it is not the public result.

## Reproducing

```sh
cd lean/
lake exe cache get
lake build
```

Then confirm the statement and the axiom base:

```sh
cd lean/
lake env lean ProofRouteAudit.lean    # expands the public statement
lake env lean AxiomAudit.lean         # transitive axiom dependencies
```

`ProofRouteAudit.lean` requires the expanded type of `main_theorem` to mention
only finite-dimensionality and rank two, and traces the proof term to confirm
it calls the Shi–Yau 2020 theorem without circularity.
