import Klean.Kernel.EffectSum

/-!
Explicit duplicate-target handling policy for the immediate `E + E` case.

This is a pragmatic policy module:
- when the same effect appears on both sides of a binary sum, choose which side
  to eliminate first (`left` or `right`).
-/

namespace Klean
namespace Kernel
namespace EffectHandleNPath

/-- Side selector for duplicate binary stacks. -/
inductive Side where
  | left
  | right

/--
Eliminate one side of a duplicate stack `E + E`, returning the remaining `E`.
-/
def handleDuplicate
    [EffectSig E]
    (side : Side)
    (onTarget :
      {X : Type} →
      (op : EffectSig.Op (E := E) X) →
      (EffectSig.Res (E := E) op → Pending1 E A) →
      Pending1 E A) :
    Pending1 (EffectSum.Effect E E) A → Pending1 E A :=
  match side with
  | .left =>
      EffectSum.handleLeft (E1 := E) (E2 := E) (onLeft := onTarget)
  | .right =>
      EffectSum.handleRight (E1 := E) (E2 := E) (onRight := onTarget)

namespace Validation

open Validation1

abbrev EnvE := Env.Effect Nat
abbrev DupStack := EffectSum.Effect EnvE EnvE

def leftGet : Pending1 DupStack Nat :=
  EffectSum.liftLeft (E1 := EnvE) (E2 := EnvE) (Env.get (Value := Nat))

def rightGet : Pending1 DupStack Nat :=
  EffectSum.liftRight (E1 := EnvE) (E2 := EnvE) (Env.get (Value := Nat))

def dupProgram : Pending1 DupStack Nat :=
  Pending1.flatMap leftGet (fun a =>
    Pending1.flatMap rightGet (fun b =>
      .pure (a * 10 + b)))

def elimLeft : Pending1 EnvE Nat :=
  handleDuplicate (E := EnvE) .left
    (onTarget := fun {_X} op cont =>
      match op with
      | Env.Op.get => cont (1 : Nat))
    dupProgram

def evalLeft : Option Nat :=
  Env.run (Value := Nat) 2 24 elimLeft

def elimRight : Pending1 EnvE Nat :=
  handleDuplicate (E := EnvE) .right
    (onTarget := fun {_X} op cont =>
      match op with
      | Env.Op.get => cont (9 : Nat))
    dupProgram

def evalRight : Option Nat :=
  Env.run (Value := Nat) 4 24 elimRight

theorem evalLeft_spec : evalLeft = some 12 := by
  native_decide

theorem evalRight_spec : evalRight = some 49 := by
  native_decide

end Validation

end EffectHandleNPath
end Kernel
end Klean
