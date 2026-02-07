import Klean.Kernel.EffectHandleNCoupled

/-!
Higher-level facade for generic nested effect elimination.

This module exposes a compact API:
- `eliminate` for one target effect
- composable elimination records with discharge equalities
- helper theorem for combining two elimination steps
-/

namespace Klean
namespace Kernel
namespace EffectHandleNApi

open EffectHandleN
open EffectHandleNRow
open EffectHandleNCoupled

/-- Row-semantic obligations of a stack-typed pending program. -/
def obligations [EffectSig S] [StackRow S] (_ : Pending1 S A) : Row.RowSet :=
  Row.toRowSet (stackRow S)

/-- Result of eliminating one target effect from stack `S`. -/
structure Eliminated (target S out A : Type)
    [EffectSig target] [EffectSig S] [EffectSig out]
    [StackRow S] [StackRow out] where
  program : Pending1 out A
  discharge :
    Row.toRowSet (stackRow S) = Row.singletonRowSet target ++ Row.toRowSet (stackRow out)

/-- Eliminate one target effect via the coupled runtime+row step. -/
def eliminate
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
    Eliminated target S out A :=
  let step := handleStep (target := target) (S := S) (out := out) onTarget program
  { program := step.program, discharge := step.discharge }

/--
Compose the discharge equalities from two elimination steps.
-/
theorem discharge_two
    [EffectSig t1] [EffectSig t2] [EffectSig S] [EffectSig mid] [EffectSig out]
    [StackRow S] [StackRow mid] [StackRow out]
    (first : Eliminated t1 S mid A)
    (second : Eliminated t2 mid out A) :
    Row.toRowSet (stackRow S) =
      (Row.singletonRowSet t1 ++ Row.singletonRowSet t2) ++ Row.toRowSet (stackRow out) := by
  calc
    Row.toRowSet (stackRow S) = Row.singletonRowSet t1 ++ Row.toRowSet (stackRow mid) := first.discharge
    _ = Row.singletonRowSet t1 ++ (Row.singletonRowSet t2 ++ Row.toRowSet (stackRow out)) := by
      rw [second.discharge]
    _ = (Row.singletonRowSet t1 ++ Row.singletonRowSet t2) ++ Row.toRowSet (stackRow out) := by
      symm
      exact Row.appendRowSet_assoc _ _ _

namespace Validation

open Validation1
open EffectHandleN.Validation

def elimAbort :
    Eliminated AbortE Stack4 (EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect)) Nat :=
  eliminate (target := AbortE) (S := Stack4)
    (onTarget := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 77)
    program4

def elimEnv (env : Nat) :
    Eliminated EnvE (EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))
      (EffectSum.Effect VarE DummyEffect) Nat :=
  eliminate (target := EnvE) (S := EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))
    (onTarget := fun {_X} op cont =>
      match op with
      | .get => cont env)
    elimAbort.program

def elimDummy (env : Nat) :
    Eliminated DummyEffect (EffectSum.Effect VarE DummyEffect) (EffectSum.Effect VarE VoidEffect) Nat :=
  eliminate (target := DummyEffect) (S := EffectSum.Effect VarE DummyEffect)
    (onTarget := fun {_X} op cont =>
      match op with
      | .ping => cont ())
    (elimEnv env).program

def finalProgram (env : Nat) : Pending1 VarE Nat :=
  pruneVoidRight (elimDummy env).program

def evalApi (env state fuel : Nat) : Option (Nat × Nat) :=
  Var.run (Value := Nat) state fuel (finalProgram env)

def evalApi_case1 : Option (Nat × Nat) :=
  evalApi 3 10 48

def evalApi_case2 : Option (Nat × Nat) :=
  evalApi 0 10 48

theorem evalApi_case1_spec : evalApi_case1 = some (13, 13) := by
  native_decide

theorem evalApi_case2_spec : evalApi_case2 = some (10, 77) := by
  native_decide

theorem abort_env_discharge_combined :
    Row.toRowSet (stackRow Stack4) =
      (Row.singletonRowSet AbortE ++ Row.singletonRowSet EnvE) ++
      Row.toRowSet (stackRow (EffectSum.Effect VarE DummyEffect)) := by
  exact discharge_two elimAbort (elimEnv 3)

end Validation

end EffectHandleNApi
end Kernel
end Klean
