import Klean.Kernel.EffectSum

/-!
Three-effect composition helpers built from nested `EffectSum`.

Encoding:
- `Effect E1 E2 E3` means `E1 + (E2 + E3)`.
- handlers can be applied sequentially (leftmost first), mirroring the current
  binary dispatcher model.
-/

namespace Klean
namespace Kernel
namespace EffectSum3

/-- Three-effect sum as a right-associated nested binary sum. -/
abbrev Effect (E1 E2 E3 : Type) : Type :=
  EffectSum.Effect E1 (EffectSum.Effect E2 E3)

/-- Lift an `E1` program into `E1 + (E2 + E3)`. -/
def lift1 [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    Pending1 E1 A → Pending1 (Effect E1 E2 E3) A :=
  EffectSum.liftLeft (E1 := E1) (E2 := EffectSum.Effect E2 E3)

/-- Lift an `E2` program into `E1 + (E2 + E3)`. -/
def lift2 [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    Pending1 E2 A → Pending1 (Effect E1 E2 E3) A := fun program =>
  EffectSum.liftRight (E1 := E1) (E2 := EffectSum.Effect E2 E3)
    (EffectSum.liftLeft (E1 := E2) (E2 := E3) program)

/-- Lift an `E3` program into `E1 + (E2 + E3)`. -/
def lift3 [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    Pending1 E3 A → Pending1 (Effect E1 E2 E3) A := fun program =>
  EffectSum.liftRight (E1 := E1) (E2 := EffectSum.Effect E2 E3)
    (EffectSum.liftRight (E1 := E2) (E2 := E3) program)

/-- Handle the `E1` layer from `E1 + (E2 + E3)`. -/
def handle1 [EffectSig E1] [EffectSig E2] [EffectSig E3]
    (onE1 :
      {X : Type} →
      (op : EffectSig.Op (E := E1) X) →
      (EffectSig.Res (E := E1) op → Pending1 (EffectSum.Effect E2 E3) A) →
      Pending1 (EffectSum.Effect E2 E3) A) :
    Pending1 (Effect E1 E2 E3) A → Pending1 (EffectSum.Effect E2 E3) A :=
  EffectSum.handleLeft (E1 := E1) (E2 := EffectSum.Effect E2 E3) onE1

/-- Sequential helper: handle `E1`, then `E2`, leaving `E3`. -/
def handle12 [EffectSig E1] [EffectSig E2] [EffectSig E3]
    (onE1 :
      {X : Type} →
      (op : EffectSig.Op (E := E1) X) →
      (EffectSig.Res (E := E1) op → Pending1 (EffectSum.Effect E2 E3) A) →
      Pending1 (EffectSum.Effect E2 E3) A)
    (onE2 :
      {X : Type} →
      (op : EffectSig.Op (E := E2) X) →
      (EffectSig.Res (E := E2) op → Pending1 E3 A) →
      Pending1 E3 A)
    (program : Pending1 (Effect E1 E2 E3) A) : Pending1 E3 A :=
  EffectSum.handleLeft (E1 := E2) (E2 := E3) onE2 (handle1 onE1 program)

namespace Validation

open Validation1

abbrev AbortE := Abort.Effect String
abbrev EnvE := Env.Effect Nat
abbrev VarE := Var.Effect Nat

abbrev Eff3 := Effect AbortE EnvE VarE

def program3 : Pending1 Eff3 Nat :=
  Pending1.flatMap
    (lift2 (E1 := AbortE) (E2 := EnvE) (E3 := VarE) (Env.get (Value := Nat)))
    (fun env =>
      Pending1.flatMap
        (lift3 (E1 := AbortE) (E2 := EnvE) (E3 := VarE) (Var.get (Value := Nat)))
        (fun st =>
          if env = 0 then
            lift1 (E1 := AbortE) (E2 := EnvE) (E3 := VarE)
              (Abort.fail (Error := String) (A := Nat) "boom")
          else
            Pending1.flatMap
              (lift3 (E1 := AbortE) (E2 := EnvE) (E3 := VarE) (Var.set (Value := Nat) (st + env)))
              (fun _ => .pure (st * 2 + env))))

def afterAbort : Pending1 (EffectSum.Effect EnvE VarE) Nat :=
  handle1 (E1 := AbortE) (E2 := EnvE) (E3 := VarE)
    (onE1 := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 7)
    program3

def afterAbortEnv (env : Nat) : Pending1 VarE Nat :=
  EffectSum.handleLeft (E1 := EnvE) (E2 := VarE)
    (onLeft := fun {_X} op cont =>
      match op with
      | .get => cont env)
    afterAbort

def eval3 (env state fuel : Nat) : Option (Nat × Nat) :=
  Var.run (Value := Nat) state fuel (afterAbortEnv env)

def eval3_case1 : Option (Nat × Nat) :=
  eval3 3 10 32

def eval3_case2 : Option (Nat × Nat) :=
  eval3 0 10 32

theorem eval3_case1_spec : eval3_case1 = some (13, 23) := by
  native_decide

theorem eval3_case2_spec : eval3_case2 = some (10, 7) := by
  native_decide

end Validation

end EffectSum3
end Kernel
end Klean
