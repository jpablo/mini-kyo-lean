# Klean Equivalence Contract

This document defines what we mean by “Lean code is equivalent to Kyo Scala code” for the port.

## 1. Equivalence Dimensions

We use four dimensions, in priority order:

1. Semantic equivalence  
After all required effects are handled, programs that correspond between Scala and Lean produce the same observable outcomes (value, failure, emitted data, state transition, finalizer behavior).

2. Type-level obligation equivalence  
If Scala requires effect obligations `S`, Lean should require an equivalent effect context obligation (possibly encoded differently).

3. Handler elimination equivalence  
Handling effect `E` in context `E & S` should produce context `S` (modulo encoding/normalization).

4. Ergonomic equivalence  
Call-site complexity should remain practical; replacement should not require pervasive manual casts or proof noise for normal use.

Non-goal: bytecode/JIT equivalence or Scala macro-equivalent implementation strategy.

## 2. Scala Effect-Context Features We Must Match

Reference points:
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/Pending.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/ArrowEffect.scala`
- `/Users/jpablo/GitHub/kyo/kyo-kernel/shared/src/main/scala/kyo/kernel/ContextEffect.scala`

Required properties of Scala’s `S` encoding:

1. Open effect composition  
`S` can be extended with new effects (`S & S2`) without redesigning old code.

2. Monotonic accumulation  
Combinators add obligations, not remove them accidentally.

3. Order-insensitive effect meaning  
`E1 & E2` and `E2 & E1` represent the same effect obligations.

4. Idempotent effect meaning  
`E & E & S` is semantically equivalent to `E & S`.

5. Handler elimination  
A handler for `E` discharges `E` from `E & S` and continues with `S`.

6. Membership/discovery for dispatch  
Runtime/handler code can identify whether an effect request is for `E`.

7. Compositional multi-handler support  
Handling several effects should compose without requiring a single monolithic handler.

## 3. Lean `Row` Mapping (Feature-by-Feature)

Current implementation:
- `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Row.lean`

### Matched now

1. Open effect composition  
Mapped by `Row.append` (`lhs ++ rhs`).

2. Membership/discovery structure  
Mapped by `Row.Contains`.

3. Basis for handler elimination  
`Contains` + future removal operation gives a direct path to “discharge `E`”.

### Partially matched (needs semantic layer)

4. Order-insensitive meaning  
Matched at semantic level via `Row.SemEq` and `semEq_append_comm`.

5. Idempotent meaning  
Matched at semantic level via `Row.SemEq` and `semEq_append_idem`.

6. Multi-handler composition  
Mechanically possible, but we need normalized row laws to keep type signatures ergonomic.

### Not implemented yet

7. Explicit discharge/remove operation  
Implemented at proof level in
`/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Row.lean`
via `Remove` and decomposition theorems
(`exists_remove_decomposition`, `semEq_append_singleton_of_remove`).  
Still pending: integration of this row-level witness into generic multi-effect
`Pending` handler APIs with a direct `E & S -> S` eliminator contract.
Single-effect discharge remains implemented in
`/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/ContextEffect.lean`
via handler elimination into `Pending _ Row.empty`.

8. Canonical equivalence relation for rows  
Implemented (`Row.SemEq`) and exposed through quotient boundary (`RowSet`), but not yet integrated across all kernel APIs.

## 4. Why `Row` Was Chosen

`Row` is a deliberate replacement for Scala’s intersection-subtyping machinery in the effect-context layer.

Rationale:
- It makes invariants explicit and provable in Lean.
- It avoids brittle global coercion chains as the only mechanism.
- It provides a stable substrate for discharge/removal proofs used by handlers.

`Row` is therefore a *representation decision*, not a claim that ordered rows are final Kyo semantics.

## 5. Validation Checklist (Corroboration Plan)

For each Scala feature above, we require a corresponding Lean artifact:

1. Open composition: proven append lemmas.
2. Order insensitivity: equivalence theorem or normalized representation.
3. Idempotence: equivalence theorem or normalized representation.
4. Handler elimination: typing theorem or API contract showing discharge.
5. Membership/dispatch: constructive evidence used by handler implementation.
6. Multi-handler composition: examples/tests equivalent to 2-effect and 3-effect handling patterns.

A replacement is accepted only when each item has either:
- a theorem/proof, or
- an executable test demonstrating the contract with no unsafe workaround in public API.

## 6. Current Status Summary

- Good foundation: open composition + membership proofs are in place.
- Semantic set-like layer exists in code:
  - `contains_append_iff`
  - `SemEq`
  - `semEq_append_comm`
  - `semEq_append_idem`
  - `semEq_append_congr_left`
  - `semEq_append_congr_right`
  - `semEq_append_assoc`
- Canonical semantic API boundary exists:
  - `RowSet`
  - `appendRowSet` with commutativity/idempotence/associativity equalities.
- Minimal pending kernel skeleton exists (`Pending`, `flatMap`, `Effect.defer`).
- `Pending` now exposes semantic effect obligations through `obligations : RowSet`,
  with flatMap obligation commutativity/associativity laws.
- Abort/Env/Var acceptance semantics are validated in
  `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Validation.lean`
  via standalone fuel-bounded interpreters.
- Generic single-effect suspension/handling bridge is now implemented:
  - `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/ArrowEffect.lean`
  - `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Pending1.lean`
  - `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/ContextEffect.lean`
- Row-level one-step discharge witness exists:
  - `Remove`
  - `exists_remove_of_contains`
  - `semEq_append_singleton_of_remove`
  - `exists_remove_decomposition`
  - `toRowSet_remove_discharge`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Row.lean`.
- `Pending` obligation contracts now expose discharge shape from membership:
  - `obligations_decompose_of_contains`
  - `obligations_discharge_shape`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Pending.lean`.
- Row-aware single-effect handler bridge now exists:
  - `handleRemoved`
  - `handleRemoved_obligations`
  - `handleRemoved_discharge_shape`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Discharge.lean`.
- Executable multi-effect dispatch prototype exists (operation-sum encoding):
  - `EffectSum.Op` + `EffectSig` instance
  - `handleLeft` / `handleRight`
  - mixed `Abort + Env` validation
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectSum.lean`.
- Executable 3-effect composition over nested sums now exists:
  - `EffectSum3.Effect` (`E1 + (E2 + E3)`)
  - `lift1` / `lift2` / `lift3`
  - `handle1` / `handle12`
  - mixed `Abort + Env + Var` validation
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectSum3.lean`.
- Recursive nested-sum injection foundation now exists:
  - `Inject`
  - generic `lift` / `suspend`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectNest.lean`.
- Executable re-association transforms now exist for nested sums:
  - `swap`
  - `assocRight`
  - `assocLeft`
  - `handleMiddle`
  - `handleLast`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectReassoc.lean`.
- Typeclass-driven 3-effect target handling now exists:
  - `HandleAt3`
  - `handleAt3`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandle3.lean`.
- Recursive generic target handling core now exists:
  - `OpProjection`
  - `RemoveOp`
  - `handleByRemoveOp`
  - `VoidEffect`
  - `pruneVoidRight`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleN.lean`.
- Row-semantic bridge for generic nested handling now exists:
  - `StackRow`
  - `RemoveOpRow`
  - `stackRow_discharge`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNRow.lean`.
- Coupled runtime+row elimination API now exists:
  - `Step`
  - `handleStep`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNCoupled.lean`.
- Higher-level generic elimination facade now exists:
  - `Eliminated`
  - `eliminate`
  - `discharge_two`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`.
- Explicit duplicate-target policy now exists for the immediate `E + E` case:
  - `Side`
  - `handleDuplicate`
  - `Side3`
  - `handleDuplicate3`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNPath.lean`.
- Generalized duplicate-target selection now exists by occurrence index:
  - `SelectOp`
  - `handleAtIndex`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNSelect.lean`.
- Row-coupled index selection and facade integration now exist:
  - `SelectOpRow`
  - `stackRow_discharge_at`
  - `eliminateAt`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNSelect.lean`
  and `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/EffectHandleNApi.lean`.
- Row-aware 2-effect composition now exists:
  - `handleTwoRemoved`
  - `handleTwoRemoved_obligations`
  - `handleTwoRemoved_discharge_shape`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Discharge2.lean`.
- Row-aware 3-effect composition now exists:
  - `handleThreeRemoved`
  - `handleThreeRemoved_obligations`
  - `handleThreeRemoved_discharge_shape`
  in `/Users/jpablo/proyectos/experimentos/mini-kyo-lean/Klean/Kernel/Discharge3.lean`.
- Main gaps:
  - syntactic normalization/canonical form is not yet encoded
  - full n-ary row-indexed multi-effect dispatch/elimination remains to be integrated directly with `Pending` (runtime handling, row bridge, coupled steps, facade API, and index-based duplicate selection with row-coupled discharge now exist, but final surface stabilization is still pending).
