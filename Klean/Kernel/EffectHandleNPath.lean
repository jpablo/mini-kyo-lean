import Klean.Kernel.EffectSum
import Klean.Kernel.EffectReassoc

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

/-- Selector for duplicate targets in `E + (E + R)`. -/
inductive Side3 where
  | outer
  | inner

/--
Eliminate one duplicate target from `E + (E + R)`, yielding `E + R`.
-/
def handleDuplicate3
    [EffectSig E] [EffectSig R]
    (side : Side3)
    (onTarget :
      {X : Type} →
      (op : EffectSig.Op (E := E) X) →
      (EffectSig.Res (E := E) op → Pending1 (EffectSum.Effect E R) A) →
      Pending1 (EffectSum.Effect E R) A) :
    Pending1 (EffectSum.Effect E (EffectSum.Effect E R)) A →
      Pending1 (EffectSum.Effect E R) A :=
  match side with
  | .outer =>
      EffectSum.handleLeft (E1 := E) (E2 := EffectSum.Effect E R) (onLeft := onTarget)
  | .inner =>
      EffectReassoc.handleMiddle (E1 := E) (E2 := E) (E3 := R) onTarget

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

inductive Dummy where

inductive DummyOp : Type → Type where
  | ping : DummyOp Unit

instance : EffectSig Dummy where
  Op := DummyOp
  Res := fun {_X} op =>
    match op with
    | .ping => Unit

abbrev DupStack3 := EffectSum.Effect EnvE (EffectSum.Effect EnvE Dummy)

def outerEnvGet : Pending1 DupStack3 Nat :=
  EffectSum.liftLeft (E1 := EnvE) (E2 := EffectSum.Effect EnvE Dummy) (Env.get (Value := Nat))

def innerEnvGet : Pending1 DupStack3 Nat :=
  EffectSum.liftRight (E1 := EnvE) (E2 := EffectSum.Effect EnvE Dummy)
    (EffectSum.liftLeft (E1 := EnvE) (E2 := Dummy) (Env.get (Value := Nat)))

def dupProgram3 : Pending1 DupStack3 Nat :=
  Pending1.flatMap outerEnvGet (fun a =>
    Pending1.flatMap innerEnvGet (fun b =>
      .pure (a * 10 + b)))

def resolveDummy : Pending1 (EffectSum.Effect EnvE Dummy) Nat → Pending1 EnvE Nat :=
  EffectSum.handleRight (E1 := EnvE) (E2 := Dummy)
    (onRight := fun {_X} op cont =>
      match op with
      | DummyOp.ping => cont ())

def elimOuter3 : Pending1 EnvE Nat :=
  resolveDummy <|
    handleDuplicate3 (E := EnvE) (R := Dummy) .outer
      (onTarget := fun {_X} op cont =>
        match op with
        | Env.Op.get => cont (1 : Nat))
      dupProgram3

def evalOuter3 : Option Nat :=
  Env.run (Value := Nat) 2 24 elimOuter3

def elimInner3 : Pending1 EnvE Nat :=
  resolveDummy <|
    handleDuplicate3 (E := EnvE) (R := Dummy) .inner
      (onTarget := fun {_X} op cont =>
        match op with
        | Env.Op.get => cont (9 : Nat))
      dupProgram3

def evalInner3 : Option Nat :=
  Env.run (Value := Nat) 4 24 elimInner3

theorem evalOuter3_spec : evalOuter3 = some 12 := by
  native_decide

theorem evalInner3_spec : evalInner3 = some 49 := by
  native_decide

end Validation

end EffectHandleNPath
end Kernel
end Klean
