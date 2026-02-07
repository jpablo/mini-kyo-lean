import Klean.Kernel.Row

/-!
Minimal pending computation type for Klean.

This is the first kernel skeleton step:
- `Pending A S` is a computation producing `A` with effect-row obligation `S`.
- `defer` models delayed continuation, analogous to Kyo's internal defer step.
- `flatMap` combines obligations with row append.
-/

namespace Klean
namespace Kernel

/--
A pending computation that produces `A` and carries effect-row obligation `S`.
-/
inductive Pending (A : Type) : Row → Type 1 where
  /-- Already-computed value. -/
  | pure {S : Row} (value : A) : Pending A S
  /-- Deferred continuation step. -/
  | defer {S : Row} (thunk : Unit → Pending A S) : Pending A S

namespace Pending

/--
Lift a computation from `S2` into a larger obligation `S1 ++ S2`.

This is the basic widening operation used by `flatMap`.
-/
def weakenLeft {A : Type} {S1 S2 : Row} : Pending A S2 → Pending A (S1 ++ S2)
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => weakenLeft (thunk ()))

/-- Map over a pending computation without changing its effect row. -/
def map {A B : Type} {S : Row} (self : Pending A S) (f : A → B) : Pending B S :=
  match self with
  | .pure value => .pure (f value)
  | .defer thunk => .defer (fun _ => map (thunk ()) f)

/--
Monadic bind for pending computations.

The resulting obligation is row append: `S1 ++ S2`.
-/
def flatMap {A B : Type} {S1 S2 : Row} (self : Pending A S1) (f : A → Pending B S2) : Pending B (S1 ++ S2) :=
  match self with
  | .pure value => weakenLeft (S1 := S1) (f value)
  | .defer thunk => .defer (fun _ => flatMap (thunk ()) f)

/-- Sequence computations, discarding the first result. -/
def andThen {A B : Type} {S1 S2 : Row} (self : Pending A S1) (next : Pending B S2) : Pending B (S1 ++ S2) :=
  flatMap self (fun _ => next)

/--
Evaluate a closed (`Row.empty`) pending computation up to a fuel bound.

Returns `none` if fuel runs out.
-/
def eval? {A : Type} : Nat → Pending A Row.empty → Option A
  | 0, _ => none
  | Nat.succ _fuel, .pure value => some value
  | Nat.succ fuel, .defer thunk => eval? fuel (thunk ())

/--
Semantic obligation view of a pending computation.

This forgets syntactic row shape and keeps only the semantic row quotient.
-/
def obligations {A : Type} {S : Row} (_ : Pending A S) : Row.RowSet :=
  Row.toRowSet S

/--
`map` preserves semantic obligations.
-/
theorem obligations_map {A B : Type} {S : Row} (self : Pending A S) (f : A → B) :
    obligations (map self f) = obligations self := rfl

/--
`flatMap` obligations are semantically commutative in the row quotient.
-/
theorem flatMap_obligations_comm {A B : Type} {S1 S2 : Row} (self : Pending A S1) (f : A → Pending B S2) :
    obligations (flatMap self f) = Row.toRowSet (S2 ++ S1) := by
  change Row.toRowSet (S1 ++ S2) = Row.toRowSet (S2 ++ S1)
  exact Quotient.sound (Row.semEq_append_comm S1 S2)

/--
`flatMap` obligations are semantically associative in the row quotient.
-/
theorem flatMap_obligations_assoc {A B C : Type} {S1 S2 S3 : Row}
    (_self : Pending A S1) (_f : A → Pending B S2) (_g : B → Pending C S3) :
    Row.toRowSet ((S1 ++ S2) ++ S3) = Row.toRowSet (S1 ++ (S2 ++ S3)) := by
  exact Quotient.sound (Row.semEq_append_assoc S1 S2 S3)

end Pending
end Kernel
end Klean
