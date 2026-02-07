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
5. [ ] Integrate row equivalence (`≈`) into upcoming kernel API contracts.
6. [ ] Add canonical row normalization strategy (or equivalent quotient-style API boundary).

## Non-Goals for Early Phases
- Reproducing Scala macro behavior exactly.
- Performance parity before semantic parity.
- Porting all `kyo-core` modules before kernel maturity.
