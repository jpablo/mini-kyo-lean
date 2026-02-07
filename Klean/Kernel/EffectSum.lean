import Klean.Kernel.Pending1

/-!
Executable multi-effect dispatch (single runtime layer).

`EffectSum` combines two `EffectSig` families into one request space so we can
interpret one side while forwarding the other.
-/

namespace Klean
namespace Kernel
namespace EffectSum

/-- Marker for sum-composed effect families. -/
inductive Effect (E1 E2 : Type) where

/-- Operation sum for two effect signatures. -/
inductive Op (E1 E2 : Type) [EffectSig E1] [EffectSig E2] : Type → Type where
  | left {X : Type} (op : EffectSig.Op (E := E1) X) : Op E1 E2 X
  | right {X : Type} (op : EffectSig.Op (E := E2) X) : Op E1 E2 X

instance [EffectSig E1] [EffectSig E2] : EffectSig (Effect E1 E2) where
  Op := Op E1 E2
  Res := fun {_X} op =>
    match op with
    | .left op1 => EffectSig.Res (E := E1) op1
    | .right op2 => EffectSig.Res (E := E2) op2

/-- Lift a left-effect program into the sum effect space. -/
def liftLeft [EffectSig E1] [EffectSig E2] : Pending1 E1 A → Pending1 (Effect E1 E2) A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => liftLeft (thunk ()))
  | .request op cont => .request (.left op) (fun out => liftLeft (cont out))

/-- Lift a right-effect program into the sum effect space. -/
def liftRight [EffectSig E1] [EffectSig E2] : Pending1 E2 A → Pending1 (Effect E1 E2) A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => liftRight (thunk ()))
  | .request op cont => .request (.right op) (fun out => liftRight (cont out))

/--
Handle the left effect `E1`, forwarding requests for right effect `E2`.
-/
def handleLeft [EffectSig E1] [EffectSig E2]
    (onLeft :
      {X : Type} →
      (op : EffectSig.Op (E := E1) X) →
      (EffectSig.Res (E := E1) op → Pending1 E2 A) →
      Pending1 E2 A) :
    Pending1 (Effect E1 E2) A → Pending1 E2 A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => handleLeft onLeft (thunk ()))
  | .request op cont =>
      match op with
      | .left op1 => onLeft op1 (fun out => handleLeft onLeft (cont out))
      | .right op2 => .request op2 (fun out => handleLeft onLeft (cont out))

/--
Handle the right effect `E2`, forwarding requests for left effect `E1`.
-/
def handleRight [EffectSig E1] [EffectSig E2]
    (onRight :
      {X : Type} →
      (op : EffectSig.Op (E := E2) X) →
      (EffectSig.Res (E := E2) op → Pending1 E1 A) →
      Pending1 E1 A) :
    Pending1 (Effect E1 E2) A → Pending1 E1 A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => handleRight onRight (thunk ()))
  | .request op cont =>
      match op with
      | .left op1 => .request op1 (fun out => handleRight onRight (cont out))
      | .right op2 => onRight op2 (fun out => handleRight onRight (cont out))

namespace Validation

open Validation1

abbrev AbortE := Abort.Effect String
abbrev EnvE := Env.Effect Nat

def mixedProgram : Pending1 (Effect AbortE EnvE) Nat :=
  Pending1.flatMap
    (liftRight (E1 := AbortE) (E2 := EnvE) (Env.get (Value := Nat)))
    (fun n =>
      if n = 0 then
        liftLeft (E1 := AbortE) (E2 := EnvE) (Abort.fail (Error := String) (A := Nat) "boom")
      else
        .pure (n + 1))

def handleAbortToZero : Pending1 EnvE Nat :=
  handleLeft (E1 := AbortE) (E2 := EnvE)
    (onLeft := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 0)
    mixedProgram

def mixedEval1 : Option Nat :=
  Env.run (Value := Nat) 41 16 handleAbortToZero

def mixedEval2 : Option Nat :=
  Env.run (Value := Nat) 0 16 handleAbortToZero

theorem mixedEval1_spec : mixedEval1 = some 42 := by
  native_decide

theorem mixedEval2_spec : mixedEval2 = some 0 := by
  native_decide

end Validation

end EffectSum
end Kernel
end Klean
