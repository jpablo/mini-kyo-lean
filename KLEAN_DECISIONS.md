# Klean Architecture Decisions

This file is the running decision log for Klean.

## ADR-0001: Use `Row` as the initial effect-context encoding

Date: 2026-02-07  
Status: Accepted (provisional)

Related: `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/KLEAN_EQUIVALENCE.md`

### Context
Kyo encodes pending effects in the type parameter `S` of `<[A, S]`, and composes effect requirements through intersection types (`S & S2`).  
In Scala/Kyo, this relies heavily on intersection-subtyping behavior and variance.

In Lean 4, there is no direct equivalent of Scala's intersection-subtyping engine for this use case.

### Decision
Use an explicit effect-row datatype (`Klean.Kernel.Row`) as the initial representation of the effect context, with:
- row composition via append
- effect membership via a `Contains` proposition

### Why
- Gives a concrete, proof-oriented representation we can reason about in Lean.
- Avoids fragile coercion-only encodings for complex effect composition.
- Creates a direct place to encode and prove effect operations needed by handlers (membership, removal, normalization).
- Matches the *role* of Kyo's `S` even if the representation differs.

### Kyo Features This Matches
- Effect-context parameter `S` in:
  - `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel.scala`
  - `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/Pending.scala`
- Effect-set composition (`S & S2`) in pending combinators/handlers.
- Handler signatures that consume one effect from `E & S` and continue with `S` in:
  - `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/ArrowEffect.scala`
  - `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/ContextEffect.scala`

### Tradeoffs
- Current row is ordered; Kyo intersections are effectively unordered/idempotent.
- Additional work is required to recover Kyo-like equivalence behavior.

### Consequences
- `Row` is a foundation, not final semantics.
- We must add canonicalization/equivalence rules so `E & S` and `S & E` are compatible in practice.
- Future kernel APIs should target row equivalence classes, not raw row syntax shape.

### Follow-up
1. Define row normalization and an equivalence relation.
2. Add lemmas for commutativity/idempotence at the semantic layer.
3. Introduce effect removal operation used by handlers.

### Revisit Trigger
Revisit ADR-0001 if row normalization makes kernel proofs too heavy or ergonomics too poor, and evaluate alternative encodings (e.g., finite-set-like rows or scoped coercion wrappers).

## ADR-0002: Introduce `Pending1` as the single-effect suspension bridge

Date: 2026-02-07  
Status: Accepted (transitional)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Pending1.lean`
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/ContextEffect.lean`
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/KLEAN_EQUIVALENCE.md`

### Context
After validating `Abort`/`Env`/`Var` with standalone interpreters, we needed a
generic suspension/handler representation before full row-based multi-effect
dispatch is ready. Jumping directly to row-indexed request dispatch would couple
several unresolved concerns at once (row normalization, typed removal proofs,
multi-effect routing ergonomics).

### Decision
Add `Pending1 E A` with `request` continuations typed by `EffectSig E`, and use
it as an intermediate kernel layer for single-effect handling.

### Why
- Captures the core Arrow/Context suspend shape in Lean today.
- Lets us validate handler elimination semantics independently of row removal.
- Reduces proof/debug surface while row-level API contracts stabilize.

### Kyo Features This Matches
- Typed suspended requests with resumable continuations (`ArrowEffect` shape).
- Scoped provision for context effects (`ContextEffect.suspend/handle` shape),
  currently represented by single-effect discharge into closed `Pending`.

### Tradeoffs
- `Pending1` does not represent open multi-effect sets by itself.
- Row-level elimination theorem (`E & S -> S`) is still pending.
- Some examples currently exist both as standalone validations and `Pending1`.

### Consequences
- Immediate progress on semantic parity for request/handle loops.
- Clear path to later integrate `Pending1`-style requests with row obligations,
  or subsume `Pending1` into a row-indexed `Pending` request node.

### Follow-up
1. Define typed row-level removal/discharge operation.
2. Bridge single-effect handlers into row-aware multi-effect dispatch.
3. Consolidate duplicate validation programs onto one generic kernel path.

## ADR-0003: Use fold-based elimination for single-effect handlers

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/ArrowEffect.lean`
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/ContextEffect.lean`

### Context
`Pending1` requests need an interpretation mechanism that can model Scala-style
handler loops while remaining simple enough to reuse across effects.

### Decision
Define `ArrowEffect.fold` as the generic eliminator from `Pending1` into closed
`Pending`, and define `ArrowEffect.handle` as its value-preserving specialization.

### Why
- Encodes handler semantics directly with typed continuations.
- Supports effect-specific interpretations without duplicating recursion logic.
- Keeps discharge target explicit (`Pending _ Row.empty`) until row-level routing
  is added.

### Consequences
- `ContextEffect.handle` is now expressed via `ArrowEffect.handle`.
- Future effects can share one elimination primitive.
- Multi-effect dispatch can later replace/extend `fold` internals without
  changing effect-local APIs.

## ADR-0004: Model row discharge as proof-level `Remove` witness

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Row.lean`
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/KLEAN_EQUIVALENCE.md`

### Context
We need an explicit replacement for Scala’s “remove handled effect from `E & S`”.
In Lean, current row membership (`Contains`) is in `Prop`. That means we cannot
compute data rows directly from membership proofs (no elimination from `Prop`
into data in this setting).

### Decision
Represent removal/discharge first as a proof witness:
- `Remove effect src out`
- `exists_remove_of_contains`
- `semEq_append_singleton_of_remove`
- `exists_remove_decomposition`

### Why
- Gives an explicit, checkable discharge contract now.
- Matches the semantic requirement (“`src` is `out` plus handled effect”).
- Avoids forcing a premature redesign of membership indices solely for
  computational extraction.

### Tradeoffs
- Current discharge is proof-level, not an executable row-transform function.
- Generic handler APIs still need integration work to consume this witness.

### Consequences
- The equivalence contract now has a concrete Lean artifact for row removal.
- Next step is to thread `Remove` into row-aware `Pending` handler signatures.

## ADR-0005: Introduce `Discharge.handleRemoved` as row-aware handler contract

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Discharge.lean`
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/ArrowEffect.lean`

### Context
We now have:
- single-effect interpreters (`Pending1`, `ArrowEffect.handleInto`)
- proof-level row removal (`Row.Remove`)

We still need a typed API that explicitly ties handler elimination to row
discharge without waiting for a full multi-effect runtime dispatcher.

### Decision
Add `Discharge.handleRemoved`, requiring a `Row.Remove E S out` witness in the
signature and returning `Pending A out`.

### Why
- Encodes the intended `E & S -> S` elimination shape directly in API types.
- Keeps runtime implementation simple while preserving proof obligations.
- Creates a stable integration point for future multi-effect dispatch.

### Tradeoffs
- Current bridge is still single-effect at runtime.
- It does not yet route among multiple in-flight effect families.

### Consequences
- `Pending` obligations and `Discharge` now align on the same row-removal proof.
- Remaining gap is implementation-level multi-effect request dispatch.

## ADR-0006: Add operation-sum executable multi-effect dispatcher (`EffectSum`)

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectSum.lean`

### Context
We needed an executable answer to “how do we route multiple effect families at
runtime?” while row-indexed dispatch is still under construction.

### Decision
Introduce `EffectSum`:
- sum-composed operation type (`Op.left` / `Op.right`)
- `EffectSig` instance for the sum
- interpreters `handleLeft` and `handleRight` that handle one side and forward
  the other

### Why
- Provides concrete multi-effect runtime behavior now.
- Keeps typed operation/result relationships intact.
- Avoids blocking on row-indexed dispatcher design.

### Tradeoffs
- Current composition is binary and explicit (`Effect E1 E2`).
- Not yet connected to row-indexed `Pending` obligations for generic routing.

### Consequences
- We can already execute mixed-effect programs with handler forwarding.
- Next step is to connect this dispatch shape to row membership/removal evidence.

## ADR-0007: Compose summed dispatch with sequential row removals (`Discharge2`)

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Discharge2.lean`

### Context
After adding executable two-effect dispatch (`EffectSum`) and single-step
row-aware discharge (`Discharge`), we still lacked a typed composition story for
handling two effects while preserving row-removal evidence end-to-end.

### Decision
Add `Discharge2.handleTwoRemoved`, which:
1. handles `E1` from `EffectSum.Effect E1 E2` into `Pending1 E2`
2. discharges `E2` into residual row `S2` using `Row.Remove` proof

### Why
- Demonstrates concrete composition of runtime dispatch + row proofs.
- Keeps the proof obligations explicit in the API.
- Provides a stepping stone toward generalized n-ary handlers.

### Tradeoffs
- Composition is currently sequential and binary.
- Still not a single generic dispatcher for arbitrary row shapes.

### Consequences
- Two-effect elimination now has a documented and executable typed path.
- Remaining work is generalized row-indexed handler synthesis/dispatch.

## ADR-0008: Represent 3-effect composition via nested `EffectSum`

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectSum3.lean`

### Context
The equivalence checklist requires multi-handler composition examples beyond two
effects. We already had a binary dispatcher (`EffectSum`), but no concrete
3-effect runtime artifact.

### Decision
Introduce `EffectSum3` as nested binary sums:
- `Effect E1 E2 E3 := E1 + (E2 + E3)`
- explicit lifts (`lift1`, `lift2`, `lift3`)
- sequential handlers (`handle1`, `handle12`)

### Why
- Delivers executable 3-effect composition immediately.
- Reuses existing typed dispatch machinery.
- Keeps control-flow and typing behavior transparent while design is in flux.

### Tradeoffs
- Composition is explicit and right-associated.
- Still not a general row-driven dispatcher over arbitrary effect counts.

### Consequences
- We now have executable 2-effect and 3-effect composition evidence.
- Next step is abstracting over nesting shape toward n-ary row-indexed dispatch.

## ADR-0009: Add 3-step row-aware discharge composition (`Discharge3`)

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Discharge3.lean`

### Context
After introducing nested 3-effect runtime composition (`EffectSum3`), we needed
the same level of explicit row-removal contracts already present for 1-step and
2-step discharge bridges.

### Decision
Add `Discharge3.handleThreeRemoved`, with three `Row.Remove` witnesses and
obligation-shape theorems.

### Why
- Keeps runtime composition and row-proof contracts aligned.
- Provides a concrete 3-effect elimination artifact for equivalence tracking.
- Preserves the staged design while avoiding premature n-ary generalization.

### Tradeoffs
- API is still explicit and sequential.
- Boilerplate grows with arity.

### Consequences
- 1/2/3-step row-aware discharge layers are now all available.
- Next step is abstracting these staged patterns into reusable n-ary machinery.

## ADR-0010: Introduce recursive nested-sum injection typeclass (`EffectNest.Inject`)

Date: 2026-02-07  
Status: Accepted (foundation)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectNest.lean`

### Context
With explicit `lift1`/`lift2`/`lift3` helpers, boilerplate grows linearly with
stack depth. We needed a reusable mechanism to inject effects into deeper nested
sums without defining new lift families per arity.

### Decision
Add `Inject E S` with recursive instances:
- head injection into `Effect E R`
- tail recursion into `Effect L R`
- identity base `Inject E E`

and expose generic `lift` / `suspend`.

### Why
- Establishes a scalable n-ary composition foundation.
- Reduces manual injection combinator proliferation.
- Keeps current runtime encoding intact while enabling future generalization.

### Tradeoffs
- Membership is currently left-biased.
- Duplicate effects in a stack may require explicit disambiguation policies.

### Consequences
- Nested-stack examples can now use generic injection APIs.
- Next step is matching this with generic n-ary handling/removal APIs.

## ADR-0011: Add executable re-association transforms for nested sums

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectReassoc.lean`

### Context
Head-oriented handlers are easiest to implement, but targeted effects are often
not at the head of a nested sum stack. We needed a runtime mechanism to reorder
stacks before handling, without introducing unsafe casts.

### Decision
Add executable transforms:
- `swap` for binary stacks
- `assocRight` / `assocLeft` for nested stacks

with dependent result transport helpers (`swapRes`, `assocRightRes`,
`assocLeftRes`) to keep continuation typing correct.

### Why
- Enables “reorder then handle” workflow for non-head effects.
- Keeps transforms explicit and auditable.
- Reuses existing binary dispatcher/handler machinery.

### Tradeoffs
- Reordering is still manual and explicit.
- No automated normal-form synthesis yet.

### Consequences
- We now have injection + re-association building blocks for n-ary handling.
- Next step is deriving generic handler search/synthesis over these primitives.

## ADR-0012: Add reusable non-head 3-effect handler combinators

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectReassoc.lean`

### Context
`swap`/`assoc` enabled manual reorder+handle flows, but call sites still had to
spell each transformation sequence explicitly.

### Decision
Add high-level combinators over right-associated 3-effect stacks:
- `handleMiddle : E1 + (E2 + E3) -> E1 + E3`
- `handleLast : E1 + (E2 + E3) -> E1 + E2`

### Why
- Encapsulates reorder choreography behind stable APIs.
- Reduces boilerplate at handler call sites.
- Keeps implementation fully explicit and type-safe.

### Tradeoffs
- Scope is currently 3-effect right-associated stacks.
- General n-ary synthesis is still pending.

### Consequences
- Non-head handling has practical reusable APIs now.
- Next step is deriving these combinators generically from membership evidence.

## ADR-0013: Add typeclass-driven target selection for 3-effect handling

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandle3.lean`

### Context
After introducing `handleMiddle` and `handleLast`, call sites still had to pick
the right combinator manually based on effect position.

### Decision
Introduce `HandleAt3` and `handleAt3`:
- head instance uses direct `handleLeft`
- middle instance uses `EffectReassoc.handleMiddle`
- last instance uses `EffectReassoc.handleLast`

### Why
- Moves handler-path choice into typeclass resolution.
- Keeps runtime behavior explicit while improving API ergonomics.
- Provides a prototype for future n-ary target-selection abstractions.

### Tradeoffs
- Current scope is right-associated 3-effect stacks.
- Ambiguity can arise if the same effect type appears multiple times.

### Consequences
- 3-effect handler call sites can target effects declaratively.
- Next step is lifting this pattern to generalized n-ary stacks with explicit
  duplicate-handling policy.

## ADR-0014: Introduce recursive generic handler core (`EffectHandleN`)

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleN.lean`

### Context
`HandleAt3` improved ergonomics for 3-effect stacks, but we still lacked a
single recursive mechanism for deeper nested stacks.

### Decision
Add:
- `OpProjection` (hit/pass classification for one operation)
- `RemoveOp` (recursive operation-level projection evidence)
- `handleByRemoveOp` (generic one-target elimination by projection)

### Why
- Provides a reusable n-ary-oriented core over nested sums.
- Avoids hardcoding handler combinators for each arity.
- Works with existing runtime encoding and validates on a 4-effect stack.

### Tradeoffs
- Current recursion is left-biased over nested sums.
- Rightmost-leaf target elimination may still require explicit reordering or
  direct binary handlers.

### Consequences
- We now have a generic handling engine plus arity-specific ergonomics.
- Next step is making elimination fully position-agnostic and aligning it with
  row-removal witnesses end-to-end.

## ADR-0015: Use terminal marker (`VoidEffect`) to complete rightmost-leaf elimination

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleN.lean`

### Context
The initial `RemoveOp` recursion handled deep targets, but when the target was
the final rightmost leaf, residual typing required a terminal stack marker.

### Decision
Add:
- `VoidEffect` as the terminal no-op residual
- `removeOpSelf : RemoveOp Target Target VoidEffect`
- `pruneVoidRight : Pending1 (E + VoidEffect) A -> Pending1 E A`

### Why
- Makes generic elimination total for right-associated stacks.
- Avoids special-case fallback handlers in validation pipelines.
- Keeps residual simplification explicit and executable.

### Tradeoffs
- Introduces an explicit terminal marker in intermediate residual types.
- Normalization (e.g., automatic pruning) is still manual.

### Consequences
- Generic handling now covers rightmost-leaf targets as well.
- Remaining work is integrating this runtime machinery with row-level proofs and
  normalization policy.

## ADR-0016: Add `EffectHandleNRow` bridge from nested stacks to `Row` discharge

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNRow.lean`

### Context
After `EffectHandleN`, runtime generic elimination was available, but we still
needed explicit alignment with row-level discharge contracts.

### Decision
Add:
- `StackRow` (map stack types to row obligations)
- `RemoveOpRow` (recursive `Row.Remove` witness matching elimination shape)
- `stackRow_discharge` (canonical `RowSet` discharge equality)

### Why
- Connects runtime stack elimination to existing row proof infrastructure.
- Makes discharge reasoning explicit at type level.
- Provides a stepping stone toward unified `Pending` integration.

### Tradeoffs
- Current `StackRow` mapping is right-associated and marker-based.
- Duplicate-effect and normalization policy are still open.

### Consequences
- Generic runtime handling now has corresponding row-semantic theorems.
- Next step is exposing one API that couples runtime elimination and row
  obligations in `Pending`-facing signatures.

## ADR-0017: Add coupled runtime+row elimination step API (`EffectHandleNCoupled`)

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNCoupled.lean`

### Context
After adding `EffectHandleN` (runtime) and `EffectHandleNRow` (row bridge), the
two artifacts still had to be consumed separately at call sites.

### Decision
Introduce:
- `Step target S out A` with both
  - transformed runtime program (`Pending1 out A`)
  - row discharge equality (`RowSet`)
- `handleStep` as the constructor from handler + program

### Why
- Couples operational and proof-level outcomes in one value.
- Reduces orchestration noise in multi-step elimination pipelines.
- Provides a clearer shape for eventual public kernel API design.

### Tradeoffs
- Still staged per elimination step.
- Final API shape for `Pending` integration remains open.

### Consequences
- Runtime and row proof flows can now be advanced together by construction.
- Next step is deciding final external API and duplicate-effect semantics.

## ADR-0018: Add higher-level generic elimination facade (`EffectHandleNApi`)

Date: 2026-02-07  
Status: Accepted (intermediate)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`

### Context
`EffectHandleNCoupled` provided paired runtime+proof steps, but users still had
to orchestrate raw step plumbing directly.

### Decision
Introduce a thin facade:
- `Eliminated` record
- `eliminate` constructor
- `discharge_two` composition theorem

### Why
- Gives a cleaner public-facing entry point.
- Preserves full typed guarantees from lower layers.
- Reduces boilerplate in multi-step elimination call sites.

### Tradeoffs
- Still explicit/staged across elimination steps.
- Final ergonomic API (including duplicate policy) is not finalized.

### Consequences
- We now have a coherent layered stack: runtime core -> row bridge -> coupled
  steps -> facade API.
- Remaining work is finalizing/stabilizing this as the external kernel surface.

## ADR-0019: Add explicit binary duplicate-target side policy (`E + E`)

Date: 2026-02-07  
Status: Accepted (narrow policy)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNPath.lean`

### Context
Duplicate effect occurrences need a deterministic selection policy. A fully
general path mechanism is still under design, but we needed an immediate,
executable policy artifact.

### Decision
Introduce `Side` (`left`/`right`) and `handleDuplicate` for stacks of shape
`E + E`, with explicit caller-chosen elimination side.

### Why
- Provides deterministic behavior today for the core duplicate case.
- Keeps policy explicit at call sites.
- Avoids blocking broader progress on full path-generalization design.

### Tradeoffs
- Scope is intentionally narrow (`E + E` only).
- Does not yet solve arbitrary duplicate placement in deeper stacks.

### Consequences
- Duplicate policy now has a concrete executable baseline.
- Next step is extending side/path policy to deeper nested stacks.

## ADR-0020: Extend duplicate policy to `E + (E + R)` with outer/inner selection

Date: 2026-02-07  
Status: Accepted (incremental extension)

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNPath.lean`

### Context
`E + E` side-selection solved only the simplest duplicate shape. We needed the
next practical nested case where one duplicate is at stack head and another is
inside the right branch.

### Decision
Add:
- `Side3` (`outer` / `inner`)
- `handleDuplicate3` for stacks `E + (E + R)` returning `E + R`

### Why
- Extends deterministic duplicate handling without introducing complex generic
  path machinery.
- Reuses existing reassociation-aware handling primitives.
- Provides immediate coverage for a common nested duplicate shape.

### Tradeoffs
- Still shape-specific.
- Not yet a fully generic duplicate-selection mechanism.

### Consequences
- Duplicate-target policy now covers both binary and one nested form.
- Remaining work is unifying these policies into a general path-based API.

## ADR-0021: Generalize duplicate-target selection via occurrence index

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNSelect.lean`

### Context
Shape-specific selectors (`Side`, `Side3`) were useful but not scalable as stack
shapes grew.

### Decision
Introduce:
- `SelectOp target skip S out` (skip-count projection evidence)
- `handleAtIndex` to eliminate the `(skip+1)`-th target occurrence

### Why
- Removes shape-specific duplication for duplicate-target handling.
- Preserves type-safe operation forwarding/handling.
- Reuses the existing generic projection machinery style.

### Tradeoffs
- Index semantics are tied to right-associated, left-to-right occurrence order.
- Invalid indices still surface as missing-instance/type errors.

### Consequences
- Duplicate handling is now expressed with one generalized mechanism.
- Remaining work is documenting/stabilizing this as part of the final public API.

## ADR-0022: Couple index-based duplicate selection with row discharge and facade

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNSelect.lean`
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`

### Context
`SelectOp` + `handleAtIndex` provided runtime elimination by occurrence index,
but the generic row accounting and high-level facade still only covered the
single-occurrence removal path.

### Decision
Add:
- `SelectOpRow target skip S out` as row-level witness for indexed removal
- `stackRow_discharge_at` as the canonical row discharge theorem for
  `handleAtIndex`
- `eliminateAt` in `EffectHandleNApi` so index-based duplicate elimination uses
  the same `Eliminated` record/discharge shape as `eliminate`

### Why
- Keeps runtime and row semantics aligned for duplicate-index selection.
- Avoids splitting API usage into "generic single-target path" vs "duplicate
  index path" with different result contracts.
- Preserves the feature-by-feature equivalence story with Kyo-style effect
  elimination steps.

### Tradeoffs
- Requires maintaining two projection families (`RemoveOp` and `SelectOp`)
  until API unification is completed.
- Row and runtime evidence are still separate classes rather than one coupled
  synthesis class.

### Consequences
- Index-based duplicate elimination now has the same discharge contract at API
  level as non-duplicate elimination.
- The next remaining step is consolidating these handler-selection mechanisms
  under one stable public kernel interface.

## ADR-0023: Unify `eliminate` with index-selection kernel (`skip := 0`)

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNSelect.lean`

### Context
After adding `eliminateAt`, the facade had two runtime kernels:
- `eliminate` via the older generic removal path
- `eliminateAt` via occurrence-index selection

This split increased maintenance cost and risk of semantic drift.

### Decision
- Define `eliminate` using `handleAtIndex` with `skip := 0`.
- Add `selectSelf` / `selectSelfRow` instances so direct leaf-target removal
  (`S = target`) remains expressible in the index-selection system.

### Why
- One elimination runtime path simplifies reasoning and testing.
- "First occurrence" semantics are explicit and match previous behavior.
- Keeps row discharge and runtime elimination aligned under one selector family.

### Tradeoffs
- The facade now depends on `SelectOp`/`SelectOpRow` even for non-duplicate
  scenarios.
- `RemoveOp`/`RemoveOpRow` remain in the codebase for now, so there is still
  transitional overlap at the lower-level kernel.

### Consequences
- Public elimination APIs now share one generalized engine.
- Next step is deciding whether and how to retire or reframe the legacy removal
  evidence classes in the external-facing kernel surface.

## ADR-0024: Add two-step facade combinators (`Eliminated2`, `eliminateTwoAt`)

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`

### Context
Even with `Eliminated` and `eliminateAt`, common two-step handling required
manual threading:
1) call first elimination
2) pass `.program` into second elimination
3) manually apply `discharge_two`

### Decision
Add to facade:
- `Eliminated2` result record
- `eliminateTwoAt` for index-controlled two-step elimination
- `eliminateTwo` as first-occurrence (`skip := 0`) convenience

### Why
- Reduces boilerplate in the most common multi-handler case.
- Keeps row-discharge composition tied to executable composition.
- Provides a direct bridge toward future n-step façade ergonomics.

### Tradeoffs
- Adds API surface while n-ary composition design is still evolving.
- Requires users to provide the intermediate stack type `mid` explicitly.

### Consequences
- Two-step elimination now has a first-class façade API with integrated
  discharge proof shape.
- Next step is evaluating whether to add a stable n-step encoding or keep
  explicit `2/3` combinators as the public surface.

## ADR-0025: Add three-step facade combinators (`Eliminated3`, `eliminateThreeAt`)

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`

### Context
After introducing `eliminateTwoAt`, common 3-handler flows still required manual
threading of one additional step and custom discharge-equation composition.

### Decision
Add:
- `Eliminated3`
- `discharge_three`
- `eliminateThreeAt`
- `eliminateThree` (first-occurrence convenience)

### Why
- Covers the practical "Abort + Env + Dummy"-style flows already used in
  validation.
- Keeps executable sequencing and row-shape discharge in one API layer.
- Provides a concrete baseline to evaluate whether explicit small-arity
  combinators are sufficient before introducing fully generic n-ary encodings.

### Tradeoffs
- Further increases facade API surface.
- Still requires explicit intermediate stack types (`m1`, `m2`) at call sites.

### Consequences
- 2-step and 3-step elimination are now both first-class operations.
- Next step is deciding between:
  - continuing with explicit small-arity combinators (`2/3/...`), or
  - introducing a single n-step typed composition encoding.

## ADR-0026: Introduce composable n-step elimination plans (`ElimPlan`)

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`

### Context
Even with `eliminateTwo` and `eliminateThree`, scaling to longer handler chains
would require adding `eliminateFour`, `eliminateFive`, etc., and replicating
row-discharge composition lemmas per arity.

### Decision
Add a generic composable facade object:
- `ElimPlan S out A` with
  - `removed : Row.RowSet`
  - `apply : Pending1 S A → Pending1 out A`
  - `discharge : toRowSet(stackRow S) = removed ++ toRowSet(stackRow out)`
- constructors/combinators:
  - `ElimPlan.id`
  - `ElimPlan.singleAt`
  - `ElimPlan.then`

### Why
- Provides n-step composition without proliferating fixed-arity APIs.
- Preserves executable behavior and semantic row accounting in one artifact.
- Reuses existing indexed selection machinery for each single step.

### Tradeoffs
- Plan composition currently remains explicit in user code (no syntax sugar).
- `removed` tracks semantic rowset append order, not a normalized canonical list.

### Consequences
- The kernel now supports both:
  - ergonomic fixed-arity helpers (`eliminateTwo`, `eliminateThree`)
  - fully composable n-step elimination plans.
- Next step is deciding which API should be primary for external users and how
  to expose plan-building ergonomics.

## ADR-0027: Add ergonomic plan helpers (`single`, `>>>`, `run`)

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`

### Context
`ElimPlan.singleAt` + `ElimPlan.then` were expressive but verbose for common
first-occurrence workflows and for executing a plan against a concrete program.

### Decision
Add:
- `ElimPlan.single` as `skip := 0` convenience
- `>>>` infix alias for `ElimPlan.then`
- `Planned` execution-result record
- `ElimPlan.run` to materialize a plan on a program while preserving discharge

### Why
- Lowers boilerplate at call sites.
- Keeps "plan definition" and "plan execution result" distinct in the type
  model.
- Improves readability for multi-step handler pipelines.

### Tradeoffs
- Adds another naming layer over existing primitives.
- Could overlap with future custom syntax if we later introduce DSL-style plans.

### Consequences
- n-step plan APIs are now practical for day-to-day use in validation/examples.
- Next step is deciding whether to de-emphasize fixed-arity helpers (`2/3`) in
  favor of the plan API as the primary public façade.

## ADR-0028: Implement fixed-arity composition on top of `ElimPlan`

Date: 2026-02-07  
Status: Accepted

Related:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`

### Context
After introducing `ElimPlan`, fixed-arity helpers still carried their own
threading logic, leaving two composition implementations in the facade.

### Decision
Refactor:
- `eliminateTwoAt`
- `eliminateThreeAt`

to build a composed `ElimPlan`, execute it with `run`, and reuse its discharge.

### Why
- Makes `ElimPlan` the single composition kernel.
- Reduces duplicated composition code and proof paths.
- Keeps fixed-arity APIs as thin convenience wrappers.

### Tradeoffs
- Fixed-arity helpers now depend more directly on `ElimPlan` internals.
- Large `simpa [plan]` proofs can become brittle if plan internals are renamed.

### Consequences
- API layering is clearer:
  - core composition: `ElimPlan`
  - convenience surface: `eliminateTwo/Three`
- Next step is deciding whether to keep all fixed-arity helpers long-term or
  retain only first-occurrence and plan-based composition for the public API.
