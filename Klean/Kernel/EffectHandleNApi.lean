import Klean.Kernel.EffectHandleNSelect

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
open EffectHandleNSelect

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

/-- Result of eliminating two target effects in sequence from stack `S`. -/
structure Eliminated2 (t1 t2 S out A : Type)
    [EffectSig t1] [EffectSig t2] [EffectSig S] [EffectSig out]
    [StackRow S] [StackRow out] where
  program : Pending1 out A
  discharge :
    Row.toRowSet (stackRow S) =
      (Row.singletonRowSet t1 ++ Row.singletonRowSet t2) ++
      Row.toRowSet (stackRow out)

/-- Result of eliminating three target effects in sequence from stack `S`. -/
structure Eliminated3 (t1 t2 t3 S out A : Type)
    [EffectSig t1] [EffectSig t2] [EffectSig t3] [EffectSig S] [EffectSig out]
    [StackRow S] [StackRow out] where
  program : Pending1 out A
  discharge :
    Row.toRowSet (stackRow S) =
      ((Row.singletonRowSet t1 ++ Row.singletonRowSet t2) ++ Row.singletonRowSet t3) ++
      Row.toRowSet (stackRow out)

/-- Eliminate the first (leftmost) occurrence of one target effect from `S`. -/
def eliminate
    [EffectSig target] [EffectSig S] [EffectSig out]
    [StackRow S] [StackRow out]
    [SelectOp target 0 S out]
    [SelectOpRow target 0 S out]
    (onTarget :
      {X : Type} →
      (op : EffectSig.Op (E := target) X) →
      (EffectSig.Res (E := target) op → Pending1 out A) →
      Pending1 out A)
    (program : Pending1 S A) :
    Eliminated target S out A where
  program := handleAtIndex (target := target) (skip := 0) (S := S) (out := out) onTarget program
  discharge := stackRow_discharge_at (target := target) (skip := 0) (S := S) (out := out)

/--
Eliminate the `(skip+1)`-th occurrence of `target` in `S`.
-/
def eliminateAt
    [EffectSig target] [EffectSig S] [EffectSig out]
    [StackRow S] [StackRow out]
    [SelectOp target skip S out]
    [SelectOpRow target skip S out]
    (onTarget :
      {X : Type} →
      (op : EffectSig.Op (E := target) X) →
      (EffectSig.Res (E := target) op → Pending1 out A) →
      Pending1 out A)
    (program : Pending1 S A) :
    Eliminated target S out A where
  program := handleAtIndex (target := target) (skip := skip) (S := S) (out := out) onTarget program
  discharge := stackRow_discharge_at (target := target) (skip := skip) (S := S) (out := out)

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

/--
Compose the discharge equalities from three elimination steps.
-/
theorem discharge_three
    [EffectSig t1] [EffectSig t2] [EffectSig t3]
    [EffectSig S] [EffectSig m1] [EffectSig m2] [EffectSig out]
    [StackRow S] [StackRow m1] [StackRow m2] [StackRow out]
    (first : Eliminated t1 S m1 A)
    (second : Eliminated t2 m1 m2 A)
    (third : Eliminated t3 m2 out A) :
    Row.toRowSet (stackRow S) =
      ((Row.singletonRowSet t1 ++ Row.singletonRowSet t2) ++ Row.singletonRowSet t3) ++
      Row.toRowSet (stackRow out) := by
  calc
    Row.toRowSet (stackRow S) =
      (Row.singletonRowSet t1 ++ Row.singletonRowSet t2) ++ Row.toRowSet (stackRow m2) := by
        exact discharge_two first second
    _ = (Row.singletonRowSet t1 ++ Row.singletonRowSet t2) ++
          (Row.singletonRowSet t3 ++ Row.toRowSet (stackRow out)) := by
        rw [third.discharge]
    _ = ((Row.singletonRowSet t1 ++ Row.singletonRowSet t2) ++ Row.singletonRowSet t3) ++
          Row.toRowSet (stackRow out) := by
        symm
        exact Row.appendRowSet_assoc _ _ _

/--
Eliminate two targets in sequence, each by occurrence index in its current stack.
-/
def eliminateTwoAt
    [EffectSig t1] [EffectSig t2] [EffectSig S] [EffectSig mid] [EffectSig out]
    [StackRow S] [StackRow mid] [StackRow out]
    [SelectOp t1 skip1 S mid] [SelectOpRow t1 skip1 S mid]
    [SelectOp t2 skip2 mid out] [SelectOpRow t2 skip2 mid out]
    (onFirst :
      {X : Type} →
      (op : EffectSig.Op (E := t1) X) →
      (EffectSig.Res (E := t1) op → Pending1 mid A) →
      Pending1 mid A)
    (onSecond :
      {X : Type} →
      (op : EffectSig.Op (E := t2) X) →
      (EffectSig.Res (E := t2) op → Pending1 out A) →
      Pending1 out A)
    (program : Pending1 S A) :
    Eliminated2 t1 t2 S out A :=
  let first := eliminateAt (target := t1) (skip := skip1) (S := S) (out := mid) onFirst program
  let second := eliminateAt (target := t2) (skip := skip2) (S := mid) (out := out) onSecond first.program
  { program := second.program, discharge := discharge_two first second }

/--
Eliminate two targets in sequence using first-occurrence semantics for both.
-/
def eliminateTwo
    [EffectSig t1] [EffectSig t2] [EffectSig S] [EffectSig mid] [EffectSig out]
    [StackRow S] [StackRow mid] [StackRow out]
    [SelectOp t1 0 S mid] [SelectOpRow t1 0 S mid]
    [SelectOp t2 0 mid out] [SelectOpRow t2 0 mid out]
    (onFirst :
      {X : Type} →
      (op : EffectSig.Op (E := t1) X) →
      (EffectSig.Res (E := t1) op → Pending1 mid A) →
      Pending1 mid A)
    (onSecond :
      {X : Type} →
      (op : EffectSig.Op (E := t2) X) →
      (EffectSig.Res (E := t2) op → Pending1 out A) →
      Pending1 out A)
    (program : Pending1 S A) :
    Eliminated2 t1 t2 S out A :=
  eliminateTwoAt (t1 := t1) (t2 := t2) (skip1 := 0) (skip2 := 0)
    (S := S) (mid := mid) (out := out) onFirst onSecond program

/--
Eliminate three targets in sequence, each by occurrence index in its current stack.
-/
def eliminateThreeAt
    [EffectSig t1] [EffectSig t2] [EffectSig t3]
    [EffectSig S] [EffectSig m1] [EffectSig m2] [EffectSig out]
    [StackRow S] [StackRow m1] [StackRow m2] [StackRow out]
    [SelectOp t1 skip1 S m1] [SelectOpRow t1 skip1 S m1]
    [SelectOp t2 skip2 m1 m2] [SelectOpRow t2 skip2 m1 m2]
    [SelectOp t3 skip3 m2 out] [SelectOpRow t3 skip3 m2 out]
    (onFirst :
      {X : Type} →
      (op : EffectSig.Op (E := t1) X) →
      (EffectSig.Res (E := t1) op → Pending1 m1 A) →
      Pending1 m1 A)
    (onSecond :
      {X : Type} →
      (op : EffectSig.Op (E := t2) X) →
      (EffectSig.Res (E := t2) op → Pending1 m2 A) →
      Pending1 m2 A)
    (onThird :
      {X : Type} →
      (op : EffectSig.Op (E := t3) X) →
      (EffectSig.Res (E := t3) op → Pending1 out A) →
      Pending1 out A)
    (program : Pending1 S A) :
    Eliminated3 t1 t2 t3 S out A :=
  let first := eliminateAt (target := t1) (skip := skip1) (S := S) (out := m1) onFirst program
  let second := eliminateAt (target := t2) (skip := skip2) (S := m1) (out := m2) onSecond first.program
  let third := eliminateAt (target := t3) (skip := skip3) (S := m2) (out := out) onThird second.program
  { program := third.program, discharge := discharge_three first second third }

/--
Eliminate three targets in sequence using first-occurrence semantics for all.
-/
def eliminateThree
    [EffectSig t1] [EffectSig t2] [EffectSig t3]
    [EffectSig S] [EffectSig m1] [EffectSig m2] [EffectSig out]
    [StackRow S] [StackRow m1] [StackRow m2] [StackRow out]
    [SelectOp t1 0 S m1] [SelectOpRow t1 0 S m1]
    [SelectOp t2 0 m1 m2] [SelectOpRow t2 0 m1 m2]
    [SelectOp t3 0 m2 out] [SelectOpRow t3 0 m2 out]
    (onFirst :
      {X : Type} →
      (op : EffectSig.Op (E := t1) X) →
      (EffectSig.Res (E := t1) op → Pending1 m1 A) →
      Pending1 m1 A)
    (onSecond :
      {X : Type} →
      (op : EffectSig.Op (E := t2) X) →
      (EffectSig.Res (E := t2) op → Pending1 m2 A) →
      Pending1 m2 A)
    (onThird :
      {X : Type} →
      (op : EffectSig.Op (E := t3) X) →
      (EffectSig.Res (E := t3) op → Pending1 out A) →
      Pending1 out A)
    (program : Pending1 S A) :
    Eliminated3 t1 t2 t3 S out A :=
  eliminateThreeAt (t1 := t1) (t2 := t2) (t3 := t3) (skip1 := 0) (skip2 := 0) (skip3 := 0)
    (S := S) (m1 := m1) (m2 := m2) (out := out) onFirst onSecond onThird program

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

def elimAbortEnvTwo (env : Nat) :
    Eliminated2 AbortE EnvE Stack4 (EffectSum.Effect VarE DummyEffect) Nat :=
  eliminateTwo (t1 := AbortE) (t2 := EnvE)
    (S := Stack4) (mid := EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))
    (out := EffectSum.Effect VarE DummyEffect)
    (onFirst := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 77)
    (onSecond := fun {_X} op cont =>
      match op with
      | .get => cont env)
    program4

def evalTwo (env state fuel : Nat) : Option (Nat × Nat) :=
  let afterDummy :=
    eliminate (target := DummyEffect) (S := EffectSum.Effect VarE DummyEffect)
      (onTarget := fun {_X} op cont =>
        match op with
        | .ping => cont ())
      (elimAbortEnvTwo env).program
  Var.run (Value := Nat) state fuel (pruneVoidRight afterDummy.program)

def evalTwo_case1 : Option (Nat × Nat) :=
  evalTwo 3 10 48

def evalTwo_case2 : Option (Nat × Nat) :=
  evalTwo 0 10 48

theorem evalTwo_case1_spec : evalTwo_case1 = some (13, 13) := by
  native_decide

theorem evalTwo_case2_spec : evalTwo_case2 = some (10, 77) := by
  native_decide

def elimThree (env : Nat) :
    Eliminated3 AbortE EnvE DummyEffect Stack4 (EffectSum.Effect VarE VoidEffect) Nat :=
  eliminateThree (t1 := AbortE) (t2 := EnvE) (t3 := DummyEffect)
    (S := Stack4)
    (m1 := EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))
    (m2 := EffectSum.Effect VarE DummyEffect)
    (out := EffectSum.Effect VarE VoidEffect)
    (onFirst := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 77)
    (onSecond := fun {_X} op cont =>
      match op with
      | .get => cont env)
    (onThird := fun {_X} op cont =>
      match op with
      | .ping => cont ())
    program4

def evalThree (env state fuel : Nat) : Option (Nat × Nat) :=
  Var.run (Value := Nat) state fuel (pruneVoidRight (elimThree env).program)

def evalThree_case1 : Option (Nat × Nat) :=
  evalThree 3 10 48

def evalThree_case2 : Option (Nat × Nat) :=
  evalThree 0 10 48

theorem evalThree_case1_spec : evalThree_case1 = some (13, 13) := by
  native_decide

theorem evalThree_case2_spec : evalThree_case2 = some (10, 77) := by
  native_decide

def elimFirstAt :
    Eliminated EnvE EffectHandleNPath.Validation.DupStack3
      (EffectSum.Effect EnvE EffectHandleNPath.Validation.Dummy) Nat :=
  eliminateAt (target := EnvE) (skip := 0)
    (S := EffectHandleNPath.Validation.DupStack3)
    (out := EffectSum.Effect EnvE EffectHandleNPath.Validation.Dummy)
    (onTarget := fun {_X} op cont =>
      match op with
      | Env.Op.get => cont (1 : Nat))
    EffectHandleNPath.Validation.dupProgram3

def evalFirstAt : Option Nat :=
  Env.run (Value := Nat) 2 24
    (EffectHandleNPath.Validation.resolveDummy elimFirstAt.program)

def elimSecondAt :
    Eliminated EnvE EffectHandleNPath.Validation.DupStack3
      (EffectSum.Effect EnvE EffectHandleNPath.Validation.Dummy) Nat :=
  eliminateAt (target := EnvE) (skip := 1)
    (S := EffectHandleNPath.Validation.DupStack3)
    (out := EffectSum.Effect EnvE EffectHandleNPath.Validation.Dummy)
    (onTarget := fun {_X} op cont =>
      match op with
      | Env.Op.get => cont (9 : Nat))
    EffectHandleNPath.Validation.dupProgram3

def evalSecondAt : Option Nat :=
  Env.run (Value := Nat) 4 24
    (EffectHandleNPath.Validation.resolveDummy elimSecondAt.program)

theorem evalFirstAt_spec : evalFirstAt = some 12 := by
  native_decide

theorem evalSecondAt_spec : evalSecondAt = some 49 := by
  native_decide

end Validation

end EffectHandleNApi
end Kernel
end Klean
