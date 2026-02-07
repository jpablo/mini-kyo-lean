# Klean Roadmap

## Proposed Module Layout
- `Klean` (root)
- `Klean/Kernel/Row.lean` (effect-row representation and laws)
- `Klean/Kernel/Pending.lean` (`<`-like type and core combinators)
- `Klean/Kernel/Effect.lean` (base effect and defer/catching primitives)
- `Klean/Kernel/ArrowEffect.lean`
- `Klean/Kernel/ContextEffect.lean`
- `Klean/Kernel/Internal/*.lean` (runtime machinery analogues)
- Later:
  - `Klean/Core/Sync.lean`
  - `Klean/Core/Async.lean`
  - `Klean/Core/Fiber.lean`
  - `Klean/Core/Scope.lean`

## Phased Porting Plan
### Phase 0: Foundations
- Define canonical effect-row representation and row operations.
- Prove or encode canonicalization properties needed for handler signatures.
- Decide how much coercion machinery is used vs explicit row APIs.

Acceptance:
- Basic row rewrites used in signatures are stable and do not require ad hoc casts.

### Phase 1: Kernel Skeleton
- Port minimal pending representation and continuation nodes.
- Implement `map`, `flatMap`-equivalent bind semantics and `eval` for closed effects.
- Port `defer` and error-catching behavior with a minimal safepoint model.

Acceptance:
- Small examples run with handler pipelines and no unsafe casts in core public APIs.

### Phase 2: Context Effects
- Port context storage and `ContextEffect.suspend/handle`.
- Port inheritable vs noninheritable behavior model.

Acceptance:
- Scoped context provision works with nested handlers and defaults.

### Phase 3: Arrow Effects
- Port `suspend`, `suspendWith`, single-effect `handle`.
- Then add multi-effect handling variants and `handleFirst`.
- Add `handleLoop` variants after `Loop` is in place.

Acceptance:
- Abort/Env/Var-style effects port cleanly on top of kernel.

### Phase 4: Loop and Internal Optimization Layer
- Port loop outcomes and iterative handlers.
- Optimize hot paths only after semantics are validated.

Acceptance:
- Stateful handlers no longer need recursion patterns that fail termination checks.

### Phase 5: Core Runtime Primitives
- Introduce `Sync`, `Async`, `Fiber`, `Scope`, finalizers.
- Implement minimal scheduler/runtime sufficient for representative concurrency tests.

Acceptance:
- Structured concurrency scenarios execute with deterministic cleanup.

### Phase 6: Core Data Structures and Services
- Port `Queue`, `Channel`, `Hub`, `Signal`, etc.
- Port local/contextual services (`Clock`, `Random`, `Log`, ...).

Acceptance:
- End-to-end examples use core services and channels/fibers correctly.

### Phase 7: Convenience Modules
- Port `Retry`, `Admission`, `Meter`, stream helpers.

Acceptance:
- Higher-level APIs compose over stable primitives without kernel changes.

## Immediate Next Work Items
1. [x] Implement `Klean/Kernel/Row.lean` and freeze row design.
2. [x] Implement minimal `Pending` + `Effect.defer` against that row.
3. [x] Port one validation effect trio (`Abort`, `Env`, `Var`) as kernel acceptance tests.
   Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Validation.lean`
   as standalone fuel-bounded interpreters.
4. [x] Add semantic row-equivalence layer (`SemEq`) with commutativity/idempotence theorems.
   Also includes append congruence/associativity theorems for row-semantic rewriting.
5. [x] Integrate row equivalence (`≈`) into upcoming kernel API contracts.
   `Pending` now exposes semantic obligations through `obligations : RowSet`, with
   flatMap commutativity/associativity obligation laws in
   `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Pending.lean`.
6. [x] Add canonical row normalization strategy (or equivalent quotient-style API boundary).
   Implemented quotient-style boundary: `RowSet = Row / ≈` in
   `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Row.lean`.
7. [x] Port minimal single-effect `ContextEffect` suspend/handle shape.
   Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/ContextEffect.lean`
   on top of `Pending1`, with effect discharge into closed `Pending _ Row.empty`.
8. [x] Port minimal single-effect `ArrowEffect` suspend/handle shape.
   Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/ArrowEffect.lean`
   with generic `suspend`, `suspendWith`, and fold-based elimination into closed `Pending`.
9. [x] Add row-level one-step removal/discharge witness and decomposition theorem.
   Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Row.lean`
   via `Remove`, `exists_remove_of_contains`, and
   `semEq_append_singleton_of_remove` / `exists_remove_decomposition` /
   `toRowSet_remove_discharge`.
10. [x] Bridge row removal witness into `Pending` obligation contracts.
    Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Pending.lean`
    via `obligations_decompose_of_contains` and `obligations_discharge_shape`.
11. [x] Add row-aware single-effect handler discharge bridge.
    Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Discharge.lean`
    via `handleRemoved`, `handleRemoved_obligations`, and `handleRemoved_discharge_shape`.
12. [x] Add executable two-effect dispatch combinator.
    Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectSum.lean`
    via `liftLeft`/`liftRight`, `handleLeft`/`handleRight`, and validated mixed
    `Abort + Env` scenarios (`mixedEval1_spec`, `mixedEval2_spec`).
13. [x] Compose two-step row-aware discharge for summed effects.
    Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Discharge2.lean`
    via `handleTwoRemoved`, `handleTwoRemoved_obligations`, and
    `handleTwoRemoved_discharge_shape`.
14. [x] Add nested 3-effect executable composition helpers + validation.
    Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectSum3.lean`
    via `lift1`/`lift2`/`lift3`, `handle1`/`handle12`, and validated
    `Abort + Env + Var` scenarios (`eval3_case1_spec`, `eval3_case2_spec`).
15. [x] Add 3-step row-aware nested-sum discharge bridge.
    Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Discharge3.lean`
    via `handleThreeRemoved`, `handleThreeRemoved_obligations`, and
    `handleThreeRemoved_discharge_shape`.
16. [x] Add recursive nested-sum injection typeclass foundation.
    Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectNest.lean`
    via `Inject`, generic `lift`/`suspend`, and validated stack example
    (`evalStack_case1_spec`, `evalStack_case2_spec`).
17. [x] Add executable nested-sum re-association transforms.
    Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectReassoc.lean`
    via `swap`, `assocRight`, `assocLeft`, with validation for handling a
    non-head effect by reorder+handle (`eval_case1_spec`, `eval_case2_spec`).
18. [x] Add reusable 3-effect non-head handler combinators.
    Implemented in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectReassoc.lean`
    via `handleMiddle` and `handleLast`, with helper-based validation
    (`eval_auto_case1_spec`, `eval_auto_case2_spec`).

## Non-Goals for Early Phases
- Reproducing Scala macro behavior exactly.
- Performance parity before semantic parity.
- Porting all `kyo-core` modules before kernel maturity.
