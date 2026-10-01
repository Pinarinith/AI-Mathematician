# Existing Lean proof audit for the Jacobi replacement

Audit date: 2026-09-29. Source project (read only):
`/Users/rinithpina/Documents/Research/Mitter_Conjecture/lean_wong_unconditional_2026-09-18`.

## Conclusion

The current source provides an actual smooth differential-operator model and a complete source-level bridge to the frozen original `mainClaim`. The final visible-entry step can be replaced without strengthening a hypothesis or weakening a conclusion by retaining the exact declaration name and type of `Wong.SmoothModel.VisibleHeads.normalized_slope_zero_of_constant_heads` and changing only its proof to the new Jacobi argument.

The old eta elimination is localized: the only uses of `VisibleHeads.head11` and `VisibleHeads.head01` anywhere in the 233 Lean source files are in the old `VisibleHeadContradiction.lean` proof. Thus replacing that proof severs the main theorem's logical dependence on those two explicit eta formulas. Those declarations may remain imported or present as unused historical lemmas; module import and proof dependency must not be confused.

This audit is a source audit, not a successful fresh full rebuild. A read-only `lake env lean` wrapper was started and then interrupted (exit 130, no output) to avoid competing with the new proof compilation. No source project file was edited.

## Exact integration point

`Wong/VisibleHeadContradiction.lean:11` currently has the following type:

```lean
theorem normalized_slope_zero_of_constant_heads {m : ℕ}
    (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j)
    (hb₁ : p.b₁ = 0) (c₁ c : ℝ)
    (h11 : δ 1 (δ 1 (Y f h)) = multiplication (c₁ • smoothOne))
    (h01 : δ 0 (δ 1 (Y f h)) = multiplication (c • smoothOne)) :
    p.b₂ = 0
```

The type has no finite-dimensionality assumption because the two required constant heads have already been established. It also does not assume any desired zero slope, a hidden coordinate's membership, any eta regularity stronger than `Smooth`, or solvability. Its only slope premise is the actual rotation normalization `p.b₁ = 0`.

Minimal change plan:

1. Add `Wong/JacobiVisible.lean`, proving the new actual-operator identities from the existing bracket identities and normalization.
2. Replace the proof of the declaration above, retaining its type and qualified name. Its import may be changed to `Wong.JacobiVisible`.
3. Keep `VisibleElimination.lean` unchanged, or make only documentary/import changes. Its existing application at line 57 automatically uses the replacement proof.
4. Keep `MainStatement.lean` unchanged. Its verified source hash is `e9f51310ade6a4539e43c3074a1b35ed35e34bd85946761d53c93183d842a5cc`.
5. Rebuild all downstream modules, update the declaration audit manifest from the accepted source closure, and verify the exact `mainClaim` type and axiom dependencies again.

## Existing bridge to the original model

The actual source chain is:

```text
MainProof.main_theorem
  = mainClaim_of_remaining_visible_affine_slopes
      remainingVisibleAffineSlopesClaim_proved

SectorIHiddenBridge.mainClaim_of_remaining_visible_affine_slopes
  → RootAnalyticBridges.mainClaim_iff_adaptedConstancyClaim
  → PublishedAffineInput.shi_yau_affine_structure
  → VisibleElimination.visible_slopes_zero
  → VisibleElimination.normalized_visible_slope_zero
  → VisibleElimination.normalized_heads_constant (applied to actual Y)
  → VisibleHeadContradiction.normalized_slope_zero_of_constant_heads
      [the replacement point]
  → the unchanged hidden-slope arguments
  → wongConstant_of_independent_affine_slopes_zero
```

`VisibleElimination.lean:21` proves constant heads for every actual `B ∈ estimationAlgebra f h` with `B ∈ orderSpace 2`. It obtains the visible affine head restrictions from `VisibleHeadConstraints.normalized_visible_heads`, reconstructs the genuine ordinary principal symbol from the unique normal form, and applies `visible_mixed_slope_zero`. It does not introduce constant-head assumptions at the main theorem boundary.

`VisibleElimination.lean:46` applies this result to `Y f h`, proves `Y` is an actual Lie element with `Y_mem_of_coordinate_mem`, proves `Y ∈ orderSpace 2` using `Y_mem_orderSpace_two`, and calls the replacement theorem.

`VisibleElimination.lean:61` uses the genuine orthogonal coordinate model returned by `normalized_visible_model`, including transported finite dimensionality, rank two, quadratic freeness, both visible coordinate memberships, and affine Wong parameters. Its conclusion remains `p.b₁ = 0 ∧ p.b₂ = 0`.

`RootAnalyticBridges.lean:807` proves both directions of `mainClaim ↔ AdaptedConstancyClaim`. The reverse direction uses `CoordinateGenerators.estimationAlgebra_adapted_coordinates` (line 283), whose result preserves all three original hypotheses, gives the two visible multipliers, and provides `WongConstant (coordinateDrift e f) ↔ WongConstant f`. Thus the final theorem is not merely a theorem about pre-adapted or affine slope data.

## Meaning of the frozen original proposition

`MainStatement.lean` defines:

- `State := Fin 3 → ℝ`;
- `Smooth` as the vector subtype of globally `C∞` real functions on that state space;
- `Operator := Module.End ℝ Smooth`;
- coordinate derivatives using the actual Fréchet derivative of smooth functions;
- `D f i = partialDerivative i - multiplication (f i)`;
- the original eta, including drift divergence, drift squares, and observation squares;
- the exact filtering operator `L0 = (1/2) Σ D_i² - (1/2) eta`;
- `estimationAlgebra` as the least real Lie subalgebra generated by that `L0` and observation multipliers;
- homogeneous linear rank through coefficient vectors, with injectivity explicitly proved;
- `QuadraticFree` as absence of a member acting by multiplication by a polynomial of total degree exactly two;
- `WongConstant` as constancy of every actual Wong entry on all of real three-space.

The frozen `mainClaim` has only the quantifiers `m, f, h` and premises finite dimensionality, homogeneous linear rank two, and quadratic freeness. It has no affine-Wong, normalized-slope, constant-head, polynomial-drift, hidden-coordinate, or gauge hypothesis. This matches the quadratic-free main theorem in the supplied TeX, rather than claiming a broader theorem without quadratic freeness.

The eventual report should distinguish this theorem from any unconditional 2020 corollary: proving this `mainClaim` does not by itself formalize the external fact that every rank-two function element is affine. The parent plans to publish only the actual `Wong` public import closure and to state this boundary explicitly.

## New Jacobi core: required actual-operator bridge

Using mathematical indices 1 and 2 (Lean indices 0 and 1), define:

```text
H0 = [L0, D1], H1 = [L0, D2],
J11 = [D1, H0], J12 = [D1, H1],
w = multiplication (wong f 0 1), b = p.b₂.
```

The new core supplied by the parent must internally prove, rather than add as unexplained assumptions at the final bridge:

```text
[D2,J11] - [D1,J12] = -2b w,
δ0 δ1 Y = 2 [D2,J11],
δ1 δ1 Y = 2 [D2,J12],
[w,J12] = 0,
the final differentiated Jacobi difference = -2b² 1.
```

The existing `VisibleHeadCalculus` provides genuine `δ_lie_L0`, `δ_lie_D`, `δ_H`, `δ_D`, `δ_L0`, and ordinary multiplication/bracket identities. `VisibleHeadConstraints.normalized_wong01` identifies the multiplier as `b*x₂+b₀`; `lie_normalized_wong01` converts its bracket to `b • δ 1`. These can instantiate an abstract Lie-algebra lemma without weakening the model. An abstract Jacobi lemma alone is not the deliverable: the same-signature actual-model theorem plus the complete main chain above is the necessary bridge.

The constant `1 : Operator` is faithful/nonzero here: application to `smoothOne`, then evaluation at any state, gives the real number 1. Consequently `b² • (1 : Operator) = 0` really implies `b=0`; this should be discharged explicitly rather than postulated.

## Old formulas and dependency separation

The old eta-based declarations are:

- `VisibleGeneratorHeads.head00`, `head11`, `head01`;
- `VisibleHeadCalculus.doubleHead`, `δ_δ_Y`, `partial_generatorRemainder`, and `partial_partial_generatorRemainder`;
- `Visible.singleAxisElimination`, a standalone real polynomial elimination lemma with no uses found in the source.

Only `VisibleHeadContradiction` uses `head11` or `head01`. `head00` has no consumer. The new proof can therefore cut the relevant logical dependence without deleting old declarations or performing a broad refactor. Some general-purpose lemmas are co-located in these files, so mere file imports are not evidence that the eta elimination is still used.

For machine confirmation, traverse the new theorem's proof-expression constant dependencies (recursively through local `Wong.*` declarations) and require that it reaches the new `JacobiVisible` declaration and does not reach `VisibleHeads.head11`, `VisibleHeads.head01`, or `Visible.singleAxisElimination`. At the full main theorem level, also check that the replacement theorem is reachable. `#print axioms` checks unproved inputs, not algorithmic/proof-route dependence, so these are separate checks.

## Assumptions, axioms, and stale metadata

The source-level scan of all 233 `.lean` source files found no code declaration/token introducing `axiom`, `sorry`, `admit`, `unsafe`, `native_decide`, or `implemented_by` (comments excluded). This is a useful static check, not a substitute for fresh compilation and kernel dependency inspection.

Current `PublishedAffineInput.lean` declares `Wong.Published.shi_yau_affinity` as a theorem with an actual proof. It imports `PublishedVisibleComplete` and `PublishedMixedAffinityProof` and assembles their conclusions. `shi_yau_affine_structure` wraps it and treats zero observations via the independently proved rank-zero result. `PublishedAffineStatement.lean` only defines the proposition and proves equivalent parametrizations; it does not assert an axiom.

The current `audit_axioms.py`, `verify_main.py`, and `verify_paper.py` allow only:

```text
propext
Classical.choice
Quot.sound
```

The README still says that Shi–Yau affinity is the sole authorized external axiom, cites an older 100-module/1109-declaration run, and refers to the older `audit_2026-09-17` campaign. Those statements are stale relative to the source now present and should not be repeated as current evidence.

The current campaign path is `audit_unconditional_2026-09-18`. At the time of inspection it contained `fresh-sources.json` but not `fresh-build.json`, `fresh-axioms.json`, or `main-verification.json`. Furthermore `MainProof.olean` was older than `MainProof.lean`; timestamp comparison alone does not establish which statement/proof artifact is loaded. This is why the fresh rebuilt copy is needed.

The source project's `check.sh` and audit helpers are not read-only: they rewrite `AxiomAudit.lean`, reports, queue state, and build artifacts. They were not executed by this audit agent.

## Acceptance checks for the new copy

1. Compile the complete actual public import closure from current sources in dependency order; do not rely on copied stale `.olean` files for changed local modules or downstream consumers.
2. Keep `MainStatement.lean` byte-identical and check the frozen SHA-256 above.
3. Compile a typed wrapper `example : Wong.SmoothModel.mainClaim := Wong.SmoothModel.main_theorem`.
4. Run `#print axioms` for the new Jacobi core, the replacement `normalized_slope_zero_of_constant_heads`, `normalized_visible_slope_zero`, `visible_slopes_zero`, `Wong.Published.shi_yau_affinity`, and `main_theorem`; allow only the three listed foundations.
5. Audit every accepted local theorem/lemma declaration in the advertised deliverable closure, not merely the final theorem.
6. Check proof dependency reachability separately so the final `main_theorem` demonstrably uses the new Jacobi bridge and the new bridge does not use the old eta head formulas.
7. Bind the source hashes, accepted build artifacts, declaration manifest, toolchain/dependencies, audit output, and exact-type verification to one fresh build identifier.
8. State the scope honestly: the earlier symbol/order-growth argument establishing constant visible heads remains; the new Jacobi argument replaces the eta mixed-derivative cancellation at the final step.


## Subsequent baseline verification

The complete core audit was subsequently located under `audit_unconditional_core_2026-09-18`. All 122 frozen source and compiled artifact hashes match its linked successful build/axiom/main reports. These records are copied to `verification/baseline/` and checked by `seed_baseline.py`. The current run rebuilds changed modules and every affected consumer, and re-runs the complete axiom and proof-route audits. No unrecorded development artifact is accepted.
