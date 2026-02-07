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
Current `Row` is ordered; we still need normalization/equivalence so ordering is abstracted away.

5. Idempotent meaning  
Current `Row` permits duplicates; we still need canonicalization or quotient/equivalence to collapse duplicates semantically.

6. Multi-handler composition  
Mechanically possible, but we need normalized row laws to keep type signatures ergonomic.

### Not implemented yet

7. Explicit discharge/remove operation  
We need a typed “remove one `E` from row” operation with proofs.

8. Canonical equivalence relation for rows  
Needed so APIs reason about effect sets semantically, not by row syntax shape.

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
- Main gap: semantic set-like behavior (commutativity/idempotence) is not yet encoded.
- Next critical step: choose and implement row normalization/equivalence strategy.
