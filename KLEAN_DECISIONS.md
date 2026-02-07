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
