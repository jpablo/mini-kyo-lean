import Klean.Kernel.EffectReassoc

/-!
Typeclass-driven handler selection for right-associated 3-effect stacks.

`HandleAt3` chooses the appropriate elimination path depending on which effect
is targeted (head, middle, or last).
-/

namespace Klean
namespace Kernel
namespace EffectHandle3

/--
Handle target effect `Target` from a right-associated 3-effect stack
`E1 + (E2 + E3)`, producing stack `Out`.
-/
class HandleAt3 (Target E1 E2 E3 Out : Type)
    [EffectSig Target] [EffectSig E1] [EffectSig E2] [EffectSig E3] [EffectSig Out] where
  handle :
    ({X : Type} →
      (op : EffectSig.Op (E := Target) X) →
      (EffectSig.Res (E := Target) op → Pending1 Out A) →
      Pending1 Out A) →
    Pending1 (EffectSum.Effect E1 (EffectSum.Effect E2 E3)) A →
    Pending1 Out A

/-- Generic API: handle one chosen effect from a 3-effect stack. -/
def handleAt3
    [EffectSig Target] [EffectSig E1] [EffectSig E2] [EffectSig E3] [EffectSig Out]
    [HandleAt3 Target E1 E2 E3 Out]
    (onTarget :
      {X : Type} →
      (op : EffectSig.Op (E := Target) X) →
      (EffectSig.Res (E := Target) op → Pending1 Out A) →
      Pending1 Out A)
    (program : Pending1 (EffectSum.Effect E1 (EffectSum.Effect E2 E3)) A) :
    Pending1 Out A :=
  HandleAt3.handle (Target := Target) (E1 := E1) (E2 := E2) (E3 := E3) (Out := Out) onTarget program

instance handleHead
    [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    HandleAt3 E1 E1 E2 E3 (EffectSum.Effect E2 E3) where
  handle onTarget program :=
    EffectSum.handleLeft (E1 := E1) (E2 := EffectSum.Effect E2 E3) onTarget program

instance handleMiddle
    [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    HandleAt3 E2 E1 E2 E3 (EffectSum.Effect E1 E3) where
  handle onTarget program :=
    EffectReassoc.handleMiddle (E1 := E1) (E2 := E2) (E3 := E3) onTarget program

instance handleLast
    [EffectSig E1] [EffectSig E2] [EffectSig E3] :
    HandleAt3 E3 E1 E2 E3 (EffectSum.Effect E1 E2) where
  handle onTarget program :=
    EffectReassoc.handleLast (E1 := E1) (E2 := E2) (E3 := E3) onTarget program

namespace Validation

open Validation1
open EffectReassoc.Validation

def afterAbort_tc : Pending1 (EffectSum.Effect EnvE VarE) Nat :=
  handleAt3 (Target := AbortE) (E1 := EnvE) (E2 := AbortE) (E3 := VarE)
    (onTarget := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 99)
    program

def afterEnv_tc (env : Nat) : Pending1 VarE Nat :=
  EffectSum.handleLeft (E1 := EnvE) (E2 := VarE)
    (onLeft := fun {_X} op cont =>
      match op with
      | .get => cont env)
    afterAbort_tc

def eval_tc (env state fuel : Nat) : Option (Nat × Nat) :=
  Var.run (Value := Nat) state fuel (afterEnv_tc env)

def eval_tc_case1 : Option (Nat × Nat) :=
  eval_tc 3 10 32

def eval_tc_case2 : Option (Nat × Nat) :=
  eval_tc 0 10 32

theorem eval_tc_case1_spec : eval_tc_case1 = some (13, 13) := by
  native_decide

theorem eval_tc_case2_spec : eval_tc_case2 = some (10, 99) := by
  native_decide

end Validation

end EffectHandle3
end Kernel
end Klean
