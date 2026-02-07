import Klean.Kernel.Pending
import Klean.Kernel.Pending1
import Klean.Kernel.ArrowEffect

/-!
Minimal single-effect `ContextEffect` port for Klean.

This module is an intermediate step:
- request a contextual value (`suspend`, `suspendWith`)
- handle/provide that value for a computation scope
- discharge the effect into a closed `Pending _ Row.empty`

It mirrors the core shape of Scala `ContextEffect` handling while we still
separate single-effect handlers (`Pending1`) from multi-effect row dispatch.
-/

namespace Klean
namespace Kernel
namespace ContextEffect

/-- Marker effect family for required context values. -/
inductive Effect (Value : Type) where

/-- Context operations: request the currently provided value. -/
inductive Op (Value : Type) : Type → Type where
  | get : Op Value Value

instance : EffectSig (Effect Value) where
  Op := Op Value
  Res := fun {_X} op =>
    match op with
    | .get => Value

/-- Request the current context value. -/
def suspend : Pending1 (Effect Value) Value :=
  .request Op.get (fun value => .pure value)

/-- Request and immediately continue with a dependent computation. -/
def suspendWith (f : Value → Pending1 (Effect Value) A) : Pending1 (Effect Value) A :=
  .request Op.get f

/--
Handle/discharge the context effect by providing one concrete value.

The result is a closed pending computation (`Row.empty`).
-/
def handle (value : Value) : Pending1 (Effect Value) A → Pending A Row.empty
  := ArrowEffect.handle (E := Effect Value) (A := A)
      (onRequest := fun {_X} op cont =>
        match op with
        | .get => cont value)

/-- Evaluate a context program by providing a value and running closed `Pending`. -/
def eval? (value : Value) (fuel : Nat) (program : Pending1 (Effect Value) A) : Option A :=
  Pending.eval? fuel (handle value program)

def contextEval : Option Nat :=
  eval? 41 8 (suspendWith (fun n => .pure (n + 1)))

theorem contextEval_spec : contextEval = some 42 := by
  native_decide

end ContextEffect
end Kernel
end Klean
