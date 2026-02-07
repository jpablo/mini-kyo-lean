import Klean.Kernel.EffectSum

/-!
Executable re-association helpers for nested `EffectSum` stacks.

These combinators let us reorder nested binary effect sums while preserving
program behavior, which is useful for bringing a target effect to the head
before applying a head-oriented handler.
-/

namespace Klean
namespace Kernel
namespace EffectReassoc

/-- Swap one binary operation sum. -/
def swapOp [EffectSig E1] [EffectSig E2] :
    EffectSum.Op E1 E2 X → EffectSum.Op E2 E1 X
  | .left op => .right op
  | .right op => .left op

/-- Transport result values across `swapOp`. -/
def swapRes [EffectSig E1] [EffectSig E2] {X : Type} (op : EffectSum.Op E1 E2 X) :
    EffectSig.Res (E := EffectSum.Effect E2 E1) (swapOp op) →
      EffectSig.Res (E := EffectSum.Effect E1 E2) op :=
  match op with
  | .left _ => fun out => out
  | .right _ => fun out => out

/-- Swap a binary effect stack in a pending program. -/
def swap [EffectSig E1] [EffectSig E2] :
    Pending1 (EffectSum.Effect E1 E2) A → Pending1 (EffectSum.Effect E2 E1) A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => swap (thunk ()))
  | .request op cont => .request (swapOp op) (fun out => swap (cont (swapRes op out)))

/-- Re-associate operations: `(E1 + E2) + E3` to `E1 + (E2 + E3)`. -/
def assocRightOp [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    EffectSum.Op (EffectSum.Effect E1 E2) E3 X →
      EffectSum.Op E1 (EffectSum.Effect E2 E3) X
  | .left op12 =>
      match op12 with
      | .left op1 => .left op1
      | .right op2 => .right (.left op2)
  | .right op3 =>
      .right (.right op3)

/-- Re-associate operations: `E1 + (E2 + E3)` to `(E1 + E2) + E3`. -/
def assocLeftOp [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    EffectSum.Op E1 (EffectSum.Effect E2 E3) X →
      EffectSum.Op (EffectSum.Effect E1 E2) E3 X
  | .left op1 =>
      .left (.left op1)
  | .right op23 =>
      match op23 with
      | .left op2 => .left (.right op2)
      | .right op3 => .right op3

/-- Transport result values across `assocRightOp`. -/
def assocRightRes [EffectSig E1] [EffectSig E2] [EffectSig E3] {X : Type}
    (op : EffectSum.Op (EffectSum.Effect E1 E2) E3 X) :
    EffectSig.Res (E := EffectSum.Effect E1 (EffectSum.Effect E2 E3)) (assocRightOp op) →
      EffectSig.Res (E := EffectSum.Effect (EffectSum.Effect E1 E2) E3) op :=
  match op with
  | .left op12 =>
      match op12 with
      | .left _ => fun out => out
      | .right _ => fun out => out
  | .right _ => fun out => out

/-- Transport result values across `assocLeftOp`. -/
def assocLeftRes [EffectSig E1] [EffectSig E2] [EffectSig E3] {X : Type}
    (op : EffectSum.Op E1 (EffectSum.Effect E2 E3) X) :
    EffectSig.Res (E := EffectSum.Effect (EffectSum.Effect E1 E2) E3) (assocLeftOp op) →
      EffectSig.Res (E := EffectSum.Effect E1 (EffectSum.Effect E2 E3)) op :=
  match op with
  | .left _ => fun out => out
  | .right op23 =>
      match op23 with
      | .left _ => fun out => out
      | .right _ => fun out => out

/-- Re-associate a pending program: `(E1 + E2) + E3` to `E1 + (E2 + E3)`. -/
def assocRight [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    Pending1 (EffectSum.Effect (EffectSum.Effect E1 E2) E3) A →
      Pending1 (EffectSum.Effect E1 (EffectSum.Effect E2 E3)) A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => assocRight (thunk ()))
  | .request op cont => .request (assocRightOp op) (fun out => assocRight (cont (assocRightRes op out)))

/-- Re-associate a pending program: `E1 + (E2 + E3)` to `(E1 + E2) + E3`. -/
def assocLeft [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    Pending1 (EffectSum.Effect E1 (EffectSum.Effect E2 E3)) A →
      Pending1 (EffectSum.Effect (EffectSum.Effect E1 E2) E3) A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => assocLeft (thunk ()))
  | .request op cont => .request (assocLeftOp op) (fun out => assocLeft (cont (assocLeftRes op out)))

/--
Handle the middle effect in a 3-effect right-associated stack:
`E1 + (E2 + E3)  ⟶  E1 + E3`.
-/
def handleMiddle [EffectSig E1] [EffectSig E2] [EffectSig E3]
    (onMiddle :
      {X : Type} →
      (op : EffectSig.Op (E := E2) X) →
      (EffectSig.Res (E := E2) op → Pending1 (EffectSum.Effect E1 E3) A) →
      Pending1 (EffectSum.Effect E1 E3) A)
    (program : Pending1 (EffectSum.Effect E1 (EffectSum.Effect E2 E3)) A) :
    Pending1 (EffectSum.Effect E1 E3) A :=
  let s1 : Pending1 (EffectSum.Effect (EffectSum.Effect E2 E3) E1) A :=
    swap (E1 := E1) (E2 := EffectSum.Effect E2 E3) program
  let s2 : Pending1 (EffectSum.Effect E2 (EffectSum.Effect E3 E1)) A :=
    assocRight (E1 := E2) (E2 := E3) (E3 := E1) s1
  let handled : Pending1 (EffectSum.Effect E3 E1) A :=
    EffectSum.handleLeft (E1 := E2) (E2 := EffectSum.Effect E3 E1)
      (onLeft := fun {_X} op cont =>
        let cont13 : EffectSig.Res (E := E2) op → Pending1 (EffectSum.Effect E1 E3) A :=
          fun out => swap (E1 := E3) (E2 := E1) (cont out)
        let out13 := onMiddle op cont13
        swap (E1 := E1) (E2 := E3) out13)
      s2
  swap (E1 := E3) (E2 := E1) handled

/--
Handle the last effect in a 3-effect right-associated stack:
`E1 + (E2 + E3)  ⟶  E1 + E2`.
-/
def handleLast [EffectSig E1] [EffectSig E2] [EffectSig E3]
    (onLast :
      {X : Type} →
      (op : EffectSig.Op (E := E3) X) →
      (EffectSig.Res (E := E3) op → Pending1 (EffectSum.Effect E1 E2) A) →
      Pending1 (EffectSum.Effect E1 E2) A)
    (program : Pending1 (EffectSum.Effect E1 (EffectSum.Effect E2 E3)) A) :
    Pending1 (EffectSum.Effect E1 E2) A :=
  let s1 : Pending1 (EffectSum.Effect (EffectSum.Effect E1 E2) E3) A :=
    assocLeft (E1 := E1) (E2 := E2) (E3 := E3) program
  EffectSum.handleRight (E1 := EffectSum.Effect E1 E2) (E2 := E3) onLast s1

namespace Validation

open Validation1

abbrev AbortE := Abort.Effect String
abbrev EnvE := Env.Effect Nat
abbrev VarE := Var.Effect Nat

/-- Stack where `Abort` is not at head: `Env + (Abort + Var)`. -/
abbrev Stack : Type := EffectSum.Effect EnvE (EffectSum.Effect AbortE VarE)

def envGet : Pending1 Stack Nat :=
  EffectSum.liftLeft (E1 := EnvE) (E2 := EffectSum.Effect AbortE VarE) (Env.get (Value := Nat))

def abortFail : Pending1 Stack Nat :=
  EffectSum.liftRight (E1 := EnvE) (E2 := EffectSum.Effect AbortE VarE)
    (EffectSum.liftLeft (E1 := AbortE) (E2 := VarE)
      (Abort.fail (Error := String) (A := Nat) "boom"))

def varGet : Pending1 Stack Nat :=
  EffectSum.liftRight (E1 := EnvE) (E2 := EffectSum.Effect AbortE VarE)
    (EffectSum.liftRight (E1 := AbortE) (E2 := VarE)
      (Var.get (Value := Nat)))

def varSet (n : Nat) : Pending1 Stack Unit :=
  EffectSum.liftRight (E1 := EnvE) (E2 := EffectSum.Effect AbortE VarE)
    (EffectSum.liftRight (E1 := AbortE) (E2 := VarE)
      (Var.set (Value := Nat) n))

def program : Pending1 Stack Nat :=
  Pending1.flatMap envGet (fun env =>
    if env = 0 then
      abortFail
    else
      Pending1.flatMap varGet (fun st =>
        Pending1.flatMap (varSet (st + env)) (fun _ =>
          .pure (st + env))))

/-- Bring `Abort` to the head via swap+assoc, then handle it. -/
def afterAbort : Pending1 (EffectSum.Effect VarE EnvE) Nat :=
  let s1 : Pending1 (EffectSum.Effect (EffectSum.Effect AbortE VarE) EnvE) Nat :=
    swap (E1 := EnvE) (E2 := EffectSum.Effect AbortE VarE) program
  let s2 : Pending1 (EffectSum.Effect AbortE (EffectSum.Effect VarE EnvE)) Nat :=
    assocRight (E1 := AbortE) (E2 := VarE) (E3 := EnvE) s1
  EffectSum.handleLeft (E1 := AbortE) (E2 := EffectSum.Effect VarE EnvE)
    (onLeft := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 99)
    s2

def afterEnv (env : Nat) : Pending1 VarE Nat :=
  EffectSum.handleRight (E1 := VarE) (E2 := EnvE)
    (onRight := fun {_X} op cont =>
      match op with
      | .get => cont env)
    afterAbort

def eval (env state fuel : Nat) : Option (Nat × Nat) :=
  Var.run (Value := Nat) state fuel (afterEnv env)

def eval_case1 : Option (Nat × Nat) :=
  eval 3 10 32

def eval_case2 : Option (Nat × Nat) :=
  eval 0 10 32

theorem eval_case1_spec : eval_case1 = some (13, 13) := by
  native_decide

theorem eval_case2_spec : eval_case2 = some (10, 99) := by
  native_decide

/-- Same program handled through `handleMiddle` helper instead of manual reorder. -/
def afterAbort_auto : Pending1 (EffectSum.Effect EnvE VarE) Nat :=
  handleMiddle (E1 := EnvE) (E2 := AbortE) (E3 := VarE)
    (onMiddle := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 99)
    program

def afterEnv_auto (env : Nat) : Pending1 VarE Nat :=
  EffectSum.handleLeft (E1 := EnvE) (E2 := VarE)
    (onLeft := fun {_X} op cont =>
      match op with
      | .get => cont env)
    afterAbort_auto

def eval_auto (env state fuel : Nat) : Option (Nat × Nat) :=
  Var.run (Value := Nat) state fuel (afterEnv_auto env)

def eval_auto_case1 : Option (Nat × Nat) :=
  eval_auto 3 10 32

def eval_auto_case2 : Option (Nat × Nat) :=
  eval_auto 0 10 32

theorem eval_auto_case1_spec : eval_auto_case1 = some (13, 13) := by
  native_decide

theorem eval_auto_case2_spec : eval_auto_case2 = some (10, 99) := by
  native_decide

end Validation

end EffectReassoc
end Kernel
end Klean
