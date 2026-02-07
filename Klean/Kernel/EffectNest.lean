import Klean.Kernel.EffectSum

/-!
Recursive injection helpers for nested `EffectSum` stacks.

This is a left-biased membership/injection layer:
- head instance injects directly into `Effect E R`
- tail instance recurses into the right branch `R`

It reduces boilerplate (`lift1`/`lift2`/...) as stack depth grows.
-/

namespace Klean
namespace Kernel
namespace EffectNest

/--
`Inject E S` means programs in effect family `E` can be lifted into stack `S`.

Current strategy is left-biased for nested binary sums.
-/
class Inject (E S : Type) [EffectSig E] [EffectSig S] where
  lift : Pending1 E A → Pending1 S A

/-- Lift a single-effect program into a nested effect stack. -/
def lift [EffectSig E] [EffectSig S] [Inject E S] (program : Pending1 E A) : Pending1 S A :=
  Inject.lift (E := E) (S := S) program

/-- Lift a single operation request into a nested effect stack. -/
def suspend [EffectSig E] [EffectSig S] [Inject E S]
    (op : EffectSig.Op (E := E) X) : Pending1 S (EffectSig.Res (E := E) op) :=
  lift (.request op (fun out => .pure out))

@[default_instance 200]
instance injectHead [EffectSig E] [EffectSig R] : Inject E (EffectSum.Effect E R) where
  lift := EffectSum.liftLeft (E1 := E) (E2 := R)

@[default_instance 100]
instance injectSelf [EffectSig E] : Inject E E where
  lift program := program

@[default_instance 100]
instance injectTail [EffectSig E] [EffectSig L] [EffectSig R] [Inject E R] :
    Inject E (EffectSum.Effect L R) where
  lift program :=
    EffectSum.liftRight (E1 := L) (E2 := R) (Inject.lift (E := E) (S := R) program)

namespace Validation

open Validation1

abbrev AbortE := Abort.Effect String
abbrev EnvE := Env.Effect Nat
abbrev VarE := Var.Effect Nat

abbrev Stack3 := EffectSum.Effect AbortE (EffectSum.Effect EnvE VarE)

def programStack : Pending1 Stack3 Nat :=
  Pending1.flatMap
    (suspend (E := EnvE) (S := Stack3) (Env.Op.get (Value := Nat)))
    (fun (env : Nat) =>
      Pending1.flatMap
        (suspend (E := VarE) (S := Stack3) (Var.Op.get (Value := Nat)))
        (fun (st : Nat) =>
          if env = 0 then
            lift (E := AbortE) (S := Stack3)
              (Abort.fail (Error := String) (A := Nat) "boom")
          else
            Pending1.flatMap
              (lift (E := VarE) (S := Stack3)
                (Var.set (Value := Nat) (st + env)))
              (fun _ => .pure (st + env + 1))))

def afterAbort : Pending1 (EffectSum.Effect EnvE VarE) Nat :=
  EffectSum.handleLeft (E1 := AbortE) (E2 := EffectSum.Effect EnvE VarE)
    (onLeft := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 5)
    programStack

def afterEnv (env : Nat) : Pending1 VarE Nat :=
  EffectSum.handleLeft (E1 := EnvE) (E2 := VarE)
    (onLeft := fun {_X} op cont =>
      match op with
      | .get => cont env)
    afterAbort

def evalStack (env state fuel : Nat) : Option (Nat × Nat) :=
  Var.run (Value := Nat) state fuel (afterEnv env)

def evalStack_case1 : Option (Nat × Nat) :=
  evalStack 2 10 32

def evalStack_case2 : Option (Nat × Nat) :=
  evalStack 0 10 32

theorem evalStack_case1_spec : evalStack_case1 = some (12, 13) := by
  native_decide

theorem evalStack_case2_spec : evalStack_case2 = some (10, 5) := by
  native_decide

end Validation

end EffectNest
end Kernel
end Klean
