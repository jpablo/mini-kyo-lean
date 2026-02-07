import Klean.Kernel.EffectNest

/-!
Generic target handling over right-associated nested `EffectSum` stacks.

`RemoveOp` recursively projects each request:
- either it belongs to the target effect (`hit`)
- or it belongs to the residual stack (`pass`)

`handleByRemoveOp` uses that projection to eliminate one target effect from an
arbitrary nested stack position.
-/

namespace Klean
namespace Kernel
namespace EffectHandleN

/-- Terminal no-op effect used as residual marker after removing a final leaf. -/
inductive VoidEffect where

instance : EffectSig VoidEffect where
  Op := fun _ => Empty
  Res := fun {_X} op => nomatch op

/--
Prune a right-branch terminal marker: `E + VoidEffect  ⟶  E`.
-/
def pruneVoidRight [EffectSig E] :
    Pending1 (EffectSum.Effect E VoidEffect) A → Pending1 E A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => pruneVoidRight (thunk ()))
  | .request op cont =>
      match op with
      | .left opE => .request opE (fun out => pruneVoidRight (cont out))
      | .right opV => nomatch opV

/-- Projection evidence for one operation while removing `Target` from `S`. -/
inductive OpProjection (Target S Out : Type) [EffectSig Target] [EffectSig S] [EffectSig Out]
    (X : Type) (op : EffectSig.Op (E := S) X) where
  | hit
      (Y : Type)
      (targetOp : EffectSig.Op (E := Target) Y)
      (toSource : EffectSig.Res (E := Target) targetOp → EffectSig.Res (E := S) op) :
      OpProjection Target S Out X op
  | pass
      (Y : Type)
      (outOp : EffectSig.Op (E := Out) Y)
      (toSource : EffectSig.Res (E := Out) outOp → EffectSig.Res (E := S) op) :
      OpProjection Target S Out X op

/--
Recursive operation-level removal evidence.

Intuition: `RemoveOp Target S Out` means a single operation from stack `S` can
be classified as either:
- handled by `Target`, or
- forwarded to residual stack `Out`.
-/
class RemoveOp (Target S Out : Type) [EffectSig Target] [EffectSig S] [EffectSig Out] where
  project : {X : Type} → (op : EffectSig.Op (E := S) X) → OpProjection Target S Out X op

@[default_instance 200]
instance removeOpHead [EffectSig Target] [EffectSig Out] :
    RemoveOp Target (EffectSum.Effect Target Out) Out where
  project := by
    intro X op
    cases op with
    | left opT =>
        exact OpProjection.hit X opT (fun out => out)
    | right opOut =>
        exact OpProjection.pass X opOut (fun out => out)

@[default_instance 150]
instance removeOpSelf [EffectSig Target] :
    RemoveOp Target Target VoidEffect where
  project := by
    intro X op
    exact OpProjection.hit X op (fun out => out)

@[default_instance 100]
instance removeOpTail
    [EffectSig Target] [EffectSig Head] [EffectSig Rest] [EffectSig OutRest]
    [RemoveOp Target Rest OutRest] :
    RemoveOp Target (EffectSum.Effect Head Rest) (EffectSum.Effect Head OutRest) where
  project := by
    intro X op
    cases op with
    | left opHead =>
        exact OpProjection.pass X (.left opHead) (fun out => out)
    | right opRest =>
        cases (RemoveOp.project (Target := Target) (S := Rest) (Out := OutRest) opRest) with
        | hit Y targetOp toSource =>
            exact OpProjection.hit Y targetOp (fun out => toSource out)
        | pass Y outOp toSource =>
            exact OpProjection.pass Y (.right outOp) (fun out => toSource out)

/--
Handle one target effect from stack `S`, yielding residual stack `Out`.
-/
def handleByRemoveOp
    [EffectSig Target] [EffectSig S] [EffectSig Out]
    [RemoveOp Target S Out]
    (onTarget :
      {X : Type} →
      (op : EffectSig.Op (E := Target) X) →
      (EffectSig.Res (E := Target) op → Pending1 Out A) →
      Pending1 Out A) :
    Pending1 S A → Pending1 Out A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => handleByRemoveOp onTarget (thunk ()))
  | .request op cont =>
      match (RemoveOp.project (Target := Target) (S := S) (Out := Out) op) with
      | .hit _ targetOp toSource =>
          onTarget targetOp (fun out => handleByRemoveOp onTarget (cont (toSource out)))
      | .pass _ outOp toSource =>
          .request outOp (fun out => handleByRemoveOp onTarget (cont (toSource out)))

namespace Validation

open Validation1

abbrev EnvE := Env.Effect Nat
abbrev VarE := Var.Effect Nat
abbrev AbortE := Abort.Effect String

inductive DummyEffect where

inductive DummyOp : Type → Type where
  | ping : DummyOp Unit

instance : EffectSig DummyEffect where
  Op := DummyOp
  Res := fun {_X} op =>
    match op with
    | .ping => Unit

def ping : Pending1 DummyEffect Unit :=
  .request DummyOp.ping (fun u => .pure u)

abbrev Stack4 := EffectSum.Effect EnvE (EffectSum.Effect VarE (EffectSum.Effect AbortE DummyEffect))

def program4 : Pending1 Stack4 Nat :=
  Pending1.flatMap
    (EffectNest.suspend (E := EnvE) (S := Stack4) (Env.Op.get (Value := Nat)))
    (fun (env : Nat) =>
      Pending1.flatMap
        (EffectNest.suspend (E := VarE) (S := Stack4) (Var.Op.get (Value := Nat)))
        (fun (st : Nat) =>
          Pending1.flatMap
            (EffectNest.lift (E := DummyEffect) (S := Stack4) ping)
            (fun _ =>
              if env = 0 then
                EffectNest.lift (E := AbortE) (S := Stack4)
                  (Abort.fail (Error := String) (A := Nat) "boom")
              else
                Pending1.flatMap
                  (EffectNest.lift (E := VarE) (S := Stack4)
                    (Var.set (Value := Nat) (st + env)))
                  (fun _ => .pure (st + env)))))

def afterAbort : Pending1 (EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect)) Nat :=
  handleByRemoveOp (Target := AbortE) (S := Stack4)
    (onTarget := fun {_X} op _cont =>
      match op with
      | .fail _ => .pure 77)
    program4

def afterEnv (env : Nat) : Pending1 (EffectSum.Effect VarE DummyEffect) Nat :=
  handleByRemoveOp (Target := EnvE) (S := EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))
    (onTarget := fun {_X} op cont =>
      match op with
      | .get => cont env)
    afterAbort

def afterDummyRaw (env : Nat) : Pending1 (EffectSum.Effect VarE VoidEffect) Nat :=
  handleByRemoveOp (Target := DummyEffect) (S := EffectSum.Effect VarE DummyEffect)
    (onTarget := fun {_X} op cont =>
      match op with
      | .ping => cont ())
    (afterEnv env)

def afterDummy (env : Nat) : Pending1 VarE Nat :=
  pruneVoidRight (afterDummyRaw env)

def eval4 (env state fuel : Nat) : Option (Nat × Nat) :=
  Var.run (Value := Nat) state fuel (afterDummy env)

def eval4_case1 : Option (Nat × Nat) :=
  eval4 3 10 48

def eval4_case2 : Option (Nat × Nat) :=
  eval4 0 10 48

theorem eval4_case1_spec : eval4_case1 = some (13, 13) := by
  native_decide

theorem eval4_case2_spec : eval4_case2 = some (10, 77) := by
  native_decide

end Validation

end EffectHandleN
end Kernel
end Klean
