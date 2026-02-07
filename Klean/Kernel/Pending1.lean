/-!
`Pending1` is a typed pending computation for a single effect.

This is an integration bridge:
- It provides generic request/continuation encoding.
- It supports effect-specific handlers with typed operations/results.
- It avoids row-level multi-effect dispatch while that design is still evolving.
-/

namespace Klean
namespace Kernel

/-!
`EffectSig` is intentionally defined as a typeclass keyed by an effect family
marker `E`, so `Pending1 E _` can carry one statically known operation set.
-/
/--
Signature of one effect family.

`Op` describes operations indexed by expected result shape, and `Res` gives the
actual continuation argument type for each operation value.
-/
class EffectSig (E : Type) where
  Op : Type → Type
  Res : {X : Type} → Op X → Type

/--
Pending computation with one effect family `E`.
-/
inductive Pending1 (E A : Type) [EffectSig E] : Type 1 where
  | pure (value : A) : Pending1 E A
  | defer (thunk : Unit → Pending1 E A) : Pending1 E A
  | request {X : Type}
      (op : EffectSig.Op (E := E) X)
      (cont : EffectSig.Res (E := E) op → Pending1 E A) :
      Pending1 E A

namespace Pending1

def map [EffectSig E] (self : Pending1 E A) (f : A → B) : Pending1 E B :=
  match self with
  | .pure value => .pure (f value)
  | .defer thunk => .defer (fun _ => map (thunk ()) f)
  | .request op cont => .request op (fun out => map (cont out) f)

def flatMap [EffectSig E] (self : Pending1 E A) (f : A → Pending1 E B) : Pending1 E B :=
  match self with
  | .pure value => f value
  | .defer thunk => .defer (fun _ => flatMap (thunk ()) f)
  | .request op cont => .request op (fun out => flatMap (cont out) f)

def andThen [EffectSig E] (self : Pending1 E A) (next : Pending1 E B) : Pending1 E B :=
  flatMap self (fun _ => next)

end Pending1

namespace Validation1

namespace Abort

inductive Effect (Error : Type) where

inductive Op (Error : Type) : Type → Type where
  | fail (error : Error) : Op Error Empty

instance : EffectSig (Effect Error) where
  Op := Op Error
  Res := fun {_X} op =>
    match op with
    | .fail _ => Empty

inductive Result (Error A : Type) where
  | ok (value : A) : Result Error A
  | err (error : Error) : Result Error A
deriving Repr, DecidableEq

def fail (error : Error) : Pending1 (Effect Error) A :=
  .request (Op.fail error) (fun impossible => nomatch impossible)

def run : Nat → Pending1 (Effect Error) A → Option (Result Error A)
  | 0, _ => none
  | Nat.succ _, .pure value => some (.ok value)
  | Nat.succ fuel, .defer thunk => run fuel (thunk ())
  | Nat.succ _, .request op _ =>
      match op with
      | Op.fail error => some (.err error)

def abortEval : Option (Result String Nat) :=
  run 8 (fail (Error := String) (A := Nat) "boom")

theorem abortEval_spec : abortEval = some (.err "boom") := by
  native_decide

end Abort

namespace Env

inductive Effect (Value : Type) where

inductive Op (Value : Type) : Type → Type where
  | get : Op Value Value

instance : EffectSig (Effect Value) where
  Op := Op Value
  Res := fun {_X} op =>
    match op with
    | .get => Value

def get : Pending1 (Effect Value) Value :=
  .request Op.get (fun value => .pure value)

def run (env : Value) : Nat → Pending1 (Effect Value) A → Option A
  | 0, _ => none
  | Nat.succ _, .pure value => some value
  | Nat.succ fuel, .defer thunk => run env fuel (thunk ())
  | Nat.succ fuel, .request op cont =>
      match op with
      | Op.get => run env fuel (cont env)

def envEval : Option Nat :=
  run 42 8 get

theorem envEval_spec : envEval = some 42 := by
  native_decide

end Env

namespace Var

inductive Effect (Value : Type) where

inductive Op (Value : Type) : Type → Type where
  | get : Op Value Value
  | set (value : Value) : Op Value Unit

instance : EffectSig (Effect Value) where
  Op := Op Value
  Res := fun {_X} op =>
    match op with
    | .get => Value
    | .set _ => Unit

def get : Pending1 (Effect Value) Value :=
  .request Op.get (fun value => .pure value)

def set (value : Value) : Pending1 (Effect Value) Unit :=
  .request (Op.set value) (fun u => .pure u)

def run (state : Value) : Nat → Pending1 (Effect Value) A → Option (Value × A)
  | 0, _ => none
  | Nat.succ _, .pure value => some (state, value)
  | Nat.succ fuel, .defer thunk => run state fuel (thunk ())
  | Nat.succ fuel, .request op cont =>
      match op with
      | Op.get => run state fuel (cont state)
      | Op.set newState => run newState fuel (cont ())

def program : Pending1 (Effect Nat) Nat :=
  Pending1.flatMap get (fun n =>
    Pending1.flatMap (set (n + 1)) (fun _ =>
      .pure (n * 2)))

def varEval : Option (Nat × Nat) :=
  run 10 16 program

theorem varEval_spec : varEval = some (11, 20) := by
  native_decide

end Var

end Validation1

end Kernel
end Klean
