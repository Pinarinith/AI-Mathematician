# Jacobi implementation report

The new route has been checked by the local Lean 4.35.0-rc2 compiler on the actual smooth-operator model. The two production commands below both exited **0**, with no diagnostic output (no errors or warnings):

```sh
./run-lean.sh -j1 -o .lake/build/lib/lean/Wong/JacobiVisible.olean Wong/JacobiVisible.lean
./run-lean.sh -j1 -o .lake/build/lib/lean/Wong/VisibleHeadContradiction.olean Wong/VisibleHeadContradiction.lean
```

Working directory: `/Users/rinithpina/Documents/Codex/2026-09-29/xian-z/outputs/wong_jacobi_2026-09-29/01_lean_verification`.

## Formal proof map

- `Wong.JacobiVisible.first_identity` is a generic real Lie-algebra theorem deriving the first compatibility identity solely from Jacobi, `[Q,P]=W`, `[L,W]=b Q`, and `[W,[L,P]]=−b W`.
- `Wong.JacobiVisible.second_identity` applies `ad Q` and a second Jacobi identity to get the scalar obstruction `−2 b² e`; its only additional inputs are `[Q,W]=b e` and `[W,[P,[L,Q]]]=0`.
- `Wong.SmoothModel.VisibleHeads.jacobi_visible_multiplier` establishes `M_w=b₀ I+b₂ M_x₂` on the genuine globally smooth functions from the existing normalized affine assumption.
- `Wong.SmoothModel.VisibleHeads.normalized_slope_zero_by_jacobi` instantiates the abstract identities with the actual differential operators. It proves the double-coordinate commutator identities directly using `δ_lie_L0`, `δ_lie_D`, and `δ_H`; constant heads then annihilate the left side of the scalar obstruction. Evaluating the resulting scalar identity on `smoothOne` at the origin yields `b₂=0`.
- `Wong.SmoothModel.VisibleHeads.normalized_slope_zero_of_constant_heads` retains its old statement unchanged and now calls `normalized_slope_zero_by_jacobi`.

The new proof does not call the old `head11`, `head01`, `δ_δ_Y`, `partialDerivative_commute_apply`, or `singleAxisElimination` results. There are no `sorry`, `axiom`, or `native_decide` declarations in the two edited source files. Local names `hhead11` and `hhead01` designate the new Jacobi-derived identities, not calls to the old formulas. Full transitive dependency and axiom audits are being run separately by the root task; the two commands above verify compilation, not an independent recheck of every unchanged imported dependency.

Only `Wong/JacobiVisible.lean` (new) and `Wong/VisibleHeadContradiction.lean` (replacement bridge) were modified in the project source. Original research source files were not changed. The temporary `work_jacobi_check.lean` was removed.

## SHA-256 at successful compilation

| File | SHA-256 |
| --- | --- |
| `Wong/JacobiVisible.lean` | `3bbf9708b02028bd99a7cf54fa4b9c8668a9119b6702ce5968c26d39ad915ed1` |
| `Wong/VisibleHeadContradiction.lean` | `42e454a2956cae1fc022f29071b9cd83846956f69874c8b010c859e6dbc743aa` |
| `.lake/build/lib/lean/Wong/JacobiVisible.olean` | `2aa16894ad22123f10c987e176182111a9b6bb026ed73878657235c371757340` |
| `.lake/build/lib/lean/Wong/VisibleHeadContradiction.olean` | `482432f9482cfed0d530dff222ba8b33be61306c428281d3db345fb9befbd86d` |
