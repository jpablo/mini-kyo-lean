import Klean.Kernel.EffectHandleNRow

/-!
Coupled runtime+row elimination step for nested stacks.

`Step` packages:
- the transformed runtime program
- the corresponding row-semantic discharge equality
-/

namespace Klean
namespace Kernel
namespace EffectHandleNCoupled

open EffectHandleN
open EffectHandleNRow

/-- One elimination step with both runtime result and row discharge equality. -/
structure Step (target S out A : Type)
    [EffectSig target] [EffectSig S] [EffectSig out]
    [StackRow S] [StackRow out] where
  program : Pending1 out A
  discharge :
    Row.toRowSet (stackRow S) = Row.singletonRowSet target ++ Row.toRowSet (stackRow out)

/-- Build a coupled elimination step from generic nested handler evidence. -/
def handleStep
    [EffectSig target] [EffectSig S] [EffectSig out]
    [StackRow S] [StackRow out]
    [RemoveOp target S out]
    [RemoveOpRow target S out]
    (onTarget :
      {X : Type} →
      (op : EffectSig.Op (E := target) X) →
      (EffectSig.Res (E := target) op → Pending1 out A) →
      Pending1 out A)
    (program : Pending1 S A) :
    Step target S out A where
  program := handleByRemoveOp (Target := target) (S := S) (Out := out) onTarget program
  discharge := stackRow_discharge (target := target) (S := S) (out := out)

namespace Validation

open Validation1
open EffectHandleN.Validation

def abortStep :
    Step AbortE Stack4 (EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect)) Nat :=
  handleStep (target := AbortE) (S := Stack4)
    (onTarget := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 77)
    program4

def envStep (env : Nat) :
    Step EnvE (EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))
      (EffectSum.Effect VarE DummyEffect) Nat :=
  handleStep (target := EnvE) (S := EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))
    (onTarget := fun {_X} op cont =>
      match op with
      | .get => cont env)
    abortStep.program

def dummyStep (env : Nat) :
    Step DummyEffect (EffectSum.Effect VarE DummyEffect) (EffectSum.Effect VarE VoidEffect) Nat :=
  handleStep (target := DummyEffect) (S := EffectSum.Effect VarE DummyEffect)
    (onTarget := fun {_X} op cont =>
      match op with
      | .ping => cont ())
    (envStep env).program

def finalProgram (env : Nat) : Pending1 VarE Nat :=
  pruneVoidRight (dummyStep env).program

def evalCoupled (env state fuel : Nat) : Option (Nat × Nat) :=
  Var.run (Value := Nat) state fuel (finalProgram env)

def evalCoupled_case1 : Option (Nat × Nat) :=
  evalCoupled 3 10 48

def evalCoupled_case2 : Option (Nat × Nat) :=
  evalCoupled 0 10 48

theorem evalCoupled_case1_spec : evalCoupled_case1 = some (13, 13) := by
  native_decide

theorem evalCoupled_case2_spec : evalCoupled_case2 = some (10, 77) := by
  native_decide

end Validation

end EffectHandleNCoupled
end Kernel
end Klean
