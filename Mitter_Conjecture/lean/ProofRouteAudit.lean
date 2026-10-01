import Wong
import Lean.Util.FoldConsts
import Lean.Elab.Command

/-!
# Proof-route audit for the Jacobi replacement

This file is an executable audit of already elaborated proof expressions.
It is not imported by `Wong` and contributes no premise to the mathematical
theorems. Run it only against the fully rebuilt local import closure.

The exact-type examples below must elaborate. The command then follows
constant references in declaration values, allowing theorem/opaque values,
recursively through names whose namespace prefix is exactly `Wong`.
Library declarations outside that prefix are deliberately not traversed.
Every reached local name is printed for independent inspection.

A missing required route, a reached forbidden or circular declaration, or a
missing local declaration raises a command error, so Lean exits unsuccessfully.
This route check is separate from the companion `#print axioms` audit.
-/

namespace WongProofRouteAudit

open Wong.SmoothModel

/-- Exact paper target: no extra interface assumptions may be supplied. -/
example : mainClaim := main_theorem

/-- Check the public proposition and theorem against the literal assumptions,
not only against a named proposition whose definition could hide a premise. -/
example : mainClaim ↔
    (∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
      FiniteDimensional ℝ (estimationAlgebra f h) →
      linearRank (estimationAlgebra f h) = 2 → WongConstant f) := Iff.rfl

example : ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 → WongConstant f := main_theorem

example {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2) :
    QuadraticFree (estimationAlgebra f h) :=
  quadraticFree_of_finiteDimensional_rank_two f h hrank

/-- Exact actual-model visible-entry target, with the original hypotheses. -/
example {m : ℕ} (f : Fin 3 → Smooth) (h : Fin m → Smooth)
    [FiniteDimensional ℝ (estimationAlgebra f h)]
    (hrank : linearRank (estimationAlgebra f h) = 2)
    (hq : QuadraticFree (estimationAlgebra f h))
    (h₀ : multiplication (linearFunction (coordinateVector 0)) ∈ estimationAlgebra f h)
    (h₁ : multiplication (linearFunction (coordinateVector 1)) ∈ estimationAlgebra f h)
    (p : Wong.AffineParameters)
    (hp : ∀ i j x, (wong f i j).1 x = p.matrix x i j) :
    p.b₁ = 0 ∧ p.b₂ = 0 :=
  VisibleHeads.visible_slopes_zero f h hrank hq h₀ h₁ p hp

/-- Literal 2020 Theorem 3.10 type: no quadratic-free premise. -/
example : ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    FunctionElementsAffine (estimationAlgebra f h) := shiYau2020_mitter_theorem

/-- Literal 2020 Theorem 3.7 type: arbitrary actual degree-two polynomial. -/
example : ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 →
    (∃ p : RealPoly, p.totalDegree = 2 ∧
      multiplication (polynomialSmooth p) ∈ estimationAlgebra f h) →
    WongConstant f ∧
      (∀ j : Fin m, ∃ p : RealPoly, p.totalDegree ≤ 1 ∧ polynomialSmooth p = h j) :=
  shiYau2020_quadratic_theorem

example : ShiYau2020WongQuadraticClaim := shiYau2020_wong_quadratic_theorem

/-- Literal unconditional integrated type, also without quadratic-freeness. -/
example : ∀ (m : ℕ) (f : Fin 3 → Smooth) (h : Fin m → Smooth),
    FiniteDimensional ℝ (estimationAlgebra f h) →
    linearRank (estimationAlgebra f h) = 2 → WongConstant f := unconditional_main_theorem

end WongProofRouteAudit

open Lean Elab Command

set_option maxHeartbeats 10000000 in
run_cmd do
  let env ← getEnv
  let localPrefix : Name := `Wong
  let roots : Array Name := #[
    `Wong.SmoothModel.shiYau2020_mitter_theorem,
    `Wong.SmoothModel.unconditional_main_theorem,
    `Wong.SmoothModel.main_theorem,
    `Wong.SmoothModel.quadraticFree_main_theorem,
    `Wong.SmoothModel.quadraticFree_of_finiteDimensional_rank_two,
    `Wong.SmoothModel.VisibleHeads.visible_slopes_zero,
    `Wong.SmoothModel.VisibleHeads.normalized_slope_zero_by_jacobi
  ]
  let jacobiRequired : Array Name := #[
    `Wong.JacobiVisible.second_identity,
    `Wong.SmoothModel.VisibleHeads.normalized_slope_zero_by_jacobi
  ]
  let obsoleteVisible : Array Name := #[
    `Wong.SmoothModel.VisibleHeads.head00,
    `Wong.SmoothModel.VisibleHeads.head11,
    `Wong.SmoothModel.VisibleHeads.head01,
    `Wong.SmoothModel.VisibleHeads.δ_δ_Y,
    `Wong.Visible.singleAxisElimination
  ]

  logInfo "PASS exact-type wrapper: Wong.SmoothModel.mainClaim"
  logInfo "PASS public mainClaim/main_theorem: finite-dimensional and rank-two only"
  logInfo "PASS derived QuadraticFree: finite-dimensional and rank-two only"
  logInfo "PASS exact-type wrapper: actual-model visible_slopes_zero"

  for root in roots do
    let some rootInfo := env.find? root
      | throwError "PROOF_ROUTE_FAIL: missing root declaration {root}"
    if (rootInfo.value? (allowOpaque := true)).isNone then
      throwError "PROOF_ROUTE_FAIL: root has no inspectable proof/value: {root}"

    let mut pending : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut reached : Array Name := #[]
    while !pending.isEmpty do
      let current := pending.back!
      pending := pending.pop
      if !seen.contains current then
        seen := seen.insert current
        reached := reached.push current
        let some info := env.find? current
          | throwError "PROOF_ROUTE_FAIL: missing reachable local declaration {current} from {root}"
        match info.value? (allowOpaque := true) with
        | none => pure ()
        | some body =>
          for dependency in body.getUsedConstants do
            if localPrefix.isPrefixOf dependency && !seen.contains dependency then
              pending := pending.push dependency

    let is2020 := root == `Wong.SmoothModel.shiYau2020_mitter_theorem
    let isIntegrated := root == `Wong.SmoothModel.unconditional_main_theorem
    let isMain := root == `Wong.SmoothModel.main_theorem
    let isConditional := root == `Wong.SmoothModel.quadraticFree_main_theorem
    let isQuadraticFree := root == `Wong.SmoothModel.quadraticFree_of_finiteDimensional_rank_two
    let required : Array Name := if is2020 then #[
      `Wong.SmoothModel.classification_model_functionElementsAffine,
      `Wong.SmoothModel.actual_quadratic_function_cases
    ] else if isIntegrated then #[
      `Wong.SmoothModel.shiYau2020_mitter_theorem,
      `Wong.SmoothModel.main_theorem,
      `Wong.JacobiVisible.second_identity
    ] else if isMain then #[
      `Wong.SmoothModel.shiYau2020_mitter_theorem,
      `Wong.SmoothModel.quadraticFree_of_finiteDimensional_rank_two,
      `Wong.SmoothModel.quadraticFree_main_theorem,
      `Wong.JacobiVisible.second_identity
    ] else if isQuadraticFree then #[
      `Wong.SmoothModel.shiYau2020_mitter_theorem
    ] else jacobiRequired
    let forbidden : Array Name := if is2020 then #[
      `Wong.SmoothModel.main_theorem,
      `Wong.SmoothModel.unconditional_main_theorem,
      `Wong.SmoothModel.quadraticFree_main_theorem,
      `Wong.SmoothModel.quadraticFree_of_finiteDimensional_rank_two
    ] else if isQuadraticFree then #[
      `Wong.SmoothModel.main_theorem,
      `Wong.SmoothModel.unconditional_main_theorem,
      `Wong.SmoothModel.quadraticFree_main_theorem
    ] else if isConditional then obsoleteVisible ++ #[
      `Wong.SmoothModel.shiYau2020_mitter_theorem,
      `Wong.SmoothModel.main_theorem,
      `Wong.SmoothModel.unconditional_main_theorem
    ] else if isIntegrated || isMain then #[] else obsoleteVisible

    for target in required do
      if seen.contains target then
        logInfo m!"PASS required route: {root} -> {target}"
      else
        throwError "PROOF_ROUTE_FAIL: {root} does not reach required new declaration {target}"

    for target in forbidden do
      if seen.contains target then
        throwError "PROOF_ROUTE_FAIL: {root} still reaches forbidden or circular declaration {target}"
      else
        logInfo m!"PASS forbidden route absent: {root} -/-> {target}"

    let ordered := reached.qsort (fun a b => Name.cmp a b == Ordering.lt)
    logInfo m!"LOCAL_REACHABILITY_BEGIN root={root} count={ordered.size}"
    for name in ordered do
      logInfo m!"LOCAL_REACHABLE root={root} declaration={name}"
    logInfo m!"LOCAL_REACHABILITY_END root={root}"

  logInfo "PROOF_ROUTE_AUDIT_PASSED"
