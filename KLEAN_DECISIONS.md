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
