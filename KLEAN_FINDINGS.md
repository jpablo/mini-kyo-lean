# Klean Findings

## Purpose
This document captures the analysis findings that should drive the Lean 4 Kyo port (`Klean`).

The approach is goal-driven, not transliteration-driven: preserve Kyo semantics and user outcomes, but use Lean-native encodings where they are better.

## Sources Reviewed
- `/Users/jpablo/GitHub/kyo/README.md`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/Pending.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/Effect.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/ArrowEffect.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/ContextEffect.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/internal/KyoInternal.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/internal/Context.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/internal/Safepoint.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/Loop.scala`
- `/Users/jpablo/GitHub/kyo/kyo-core/shared/src/main/scala/kyo/*.scala`
- `/Users/jpablo/GitHub/kyo/kyo-core/shared/src/main/scala/kyo/scheduler/*.scala`
- Lean references:
  - `/Users/jpablo/GitHub/reference-manual/Manual/Coercions.lean`
  - `/Users/jpablo/GitHub/reference-manual/Manual/Monads/Lift.lean`
  - `/Users/jpablo/GitHub/lean4/src/Init/Coe.lean`
  - `/Users/jpablo/GitHub/lean4/src/Init/Prelude.lean`
  - `/Users/jpablo/GitHub/lean4/src/Init/Dynamic.lean`

## What Kyo Is Optimizing For
- Ergonomic algebraic effects for everyday Scala use (not category-theory-heavy APIs).
- Open, composable effect sets and handlers.
- Structured concurrency and deterministic cleanup (`Scope`, finalizers).
- Practical runtime performance (scheduler, low overhead kernel internals).
- Layered architecture: kernel primitives first, then richer core/convenience modules.

## Key Architecture Findings
### Kernel
- `<[A, S]` is the core pending/effectful computation representation.
- `ArrowEffect` models effect requests with resumable continuations.
- `ContextEffect` models scoped context requirements.
- `Safepoint` + `KyoSuspend/KyoContinue/KyoDefer` implement execution/stack safety.
- `Loop` provides low-overhead, stateful iterative handling.

### Core
- Fundamental runtime abstractions: `Sync`, `Async`, `Fiber`, `Scope`, scheduler internals.
- Fundamental concurrent data structures: `Queue`, `Channel`, `Hub`, `Signal`, `Latch`, `Barrier`.
- Contextual services via locals: `Clock`, `Random`, `Console`, `Log`, `System`, `Stat`.
- Convenience modules (`Retry`, `Admission`, `Meter`, stream extensions) are built on the above.

## Porting Principles for Klean
- Preserve semantics and guarantees before preserving Scala syntax shape.
- Port in dependency order: kernel -> runtime/concurrency primitives -> convenience layers.
- Keep explicit boundaries between pure suspension-like effects and async/fiber effects.
- Treat structured finalization semantics as non-negotiable.
- Avoid ad hoc effect-row hacks that do not scale (associativity/duplication issues).

## One-to-One vs Needs Redesign
### Mostly One-to-One
- Higher-kinded parameters as `Type -> Type`.
- Typeclass-driven handler evidence.
- `Id` and `Const` constructors.
- Inductive representation of suspended computations and continuations.

### Needs Lean-Specific Redesign
- Scala subtyping/intersection-heavy effect rows (`S & S2`) with variance.
- Runtime subtype-tag checks used in effect dispatch.
- Implicit lifting ergonomics from pure values into pending computations.
- Some macro/inlining behavior that is Scala/JIT-specific.

## Main Technical Risks
- Effect-row normalization and reasoning (order/associativity/idempotence).
- Dispatch soundness without unsafe casts in handlers.
- Preserving multi-shot continuation behavior.
- Matching Kyo-style ergonomics without introducing ambiguity-heavy coercion graphs.
- Runtime model for `Async`/fibers and interruption semantics.
