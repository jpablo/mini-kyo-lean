import Klean.Kernel.EffectHandleN
import Klean.Kernel.EffectHandleNRow
import Klean.Kernel.EffectHandleNPath

/-!
Generalized duplicate-target selection by occurrence index.

`skip = 0` means eliminate the first (leftmost) occurrence.
`skip = 1` means eliminate the second occurrence, and so on.
-/

namespace Klean
namespace Kernel
namespace EffectHandleNSelect

open EffectHandleN
open EffectHandleNRow

/--
Operation-level selection evidence for choosing the `(skip+1)`-th occurrence of
`target` inside stack `S`, yielding residual stack `out`.
-/
class SelectOp (target : Type) (skip : Nat) (S out : Type)
    [EffectSig target] [EffectSig S] [EffectSig out] where
  project : {X : Type} → (op : EffectSig.Op (E := S) X) → OpProjection target S out X op

/-- Row-level removal witness aligned with `SelectOp` index selection. -/
class SelectOpRow (target : Type) (skip : Nat) (S out : Type)
    [StackRow S] [StackRow out] where
  witness : Row.Remove target (stackRow S) (stackRow out)

@[default_instance 300]
instance selectHere [EffectSig target] [EffectSig rest] :
    SelectOp target 0 (EffectSum.Effect target rest) rest where
  project := fun {X} op =>
    match op with
    | EffectSum.Op.left opT =>
        OpProjection.hit X opT (fun out => out)
    | EffectSum.Op.right opR =>
        OpProjection.pass X opR (fun out => out)

@[default_instance 300]
instance selectHereRow [StackRow rest] :
    SelectOpRow target 0 (EffectSum.Effect target rest) rest where
  witness := by
    simpa [stackRow, Row.singleton, Row.append] using
      (Row.Remove.head (effect := target) (tail := stackRow (S := rest)))

@[default_instance 250]
instance selectSelf [EffectSig target] :
    SelectOp target 0 target EffectHandleN.VoidEffect where
  project := fun {X} op =>
    OpProjection.hit X op (fun out => out)

@[default_instance 250]
instance selectSelfRow [EffectSig target] :
    SelectOpRow target 0 target EffectHandleN.VoidEffect where
  witness := by
    simpa [stackRow, Row.singleton] using
      (Row.Remove.head (effect := target) (tail := Row.empty))

@[default_instance 200]
instance selectSkipTarget
    [EffectSig target] [EffectSig rest] [EffectSig outRest]
    [SelectOp target skip rest outRest] :
    SelectOp target (Nat.succ skip) (EffectSum.Effect target rest) (EffectSum.Effect target outRest) where
  project := fun {X} op =>
    match op with
    | EffectSum.Op.left opT =>
        OpProjection.pass X (.left opT) (fun out => out)
    | EffectSum.Op.right opR =>
        match (SelectOp.project (target := target) (skip := skip) (S := rest) (out := outRest) opR) with
        | OpProjection.hit Y targetOp toSource =>
            OpProjection.hit Y targetOp (fun out => toSource out)
        | OpProjection.pass Y outOp toSource =>
            OpProjection.pass Y (.right outOp) (fun out => toSource out)

@[default_instance 200]
instance selectSkipTargetRow
    [StackRow rest] [StackRow outRest]
    [SelectOpRow target skip rest outRest] :
    SelectOpRow target (Nat.succ skip) (EffectSum.Effect target rest) (EffectSum.Effect target outRest) where
  witness := by
    simpa [stackRow, Row.singleton, Row.append] using
      (Row.Remove.tail (head := target)
        (tail := stackRow (S := rest))
        (out := stackRow (S := outRest))
        (SelectOpRow.witness (target := target) (skip := skip) (S := rest) (out := outRest)))

@[default_instance 100]
instance selectSkipHead
    [EffectSig target] [EffectSig head] [EffectSig rest] [EffectSig outRest]
    [SelectOp target skip rest outRest] :
    SelectOp target skip (EffectSum.Effect head rest) (EffectSum.Effect head outRest) where
  project := fun {X} op =>
    match op with
    | EffectSum.Op.left opHead =>
        OpProjection.pass X (.left opHead) (fun out => out)
    | EffectSum.Op.right opR =>
        match (SelectOp.project (target := target) (skip := skip) (S := rest) (out := outRest) opR) with
        | OpProjection.hit Y targetOp toSource =>
            OpProjection.hit Y targetOp (fun out => toSource out)
        | OpProjection.pass Y outOp toSource =>
            OpProjection.pass Y (.right outOp) (fun out => toSource out)

@[default_instance 100]
instance selectSkipHeadRow
    [StackRow rest] [StackRow outRest]
    [SelectOpRow target skip rest outRest] :
    SelectOpRow target skip (EffectSum.Effect head rest) (EffectSum.Effect head outRest) where
  witness := by
    simpa [stackRow, Row.singleton, Row.append] using
      (Row.Remove.tail (head := head)
        (tail := stackRow (S := rest))
        (out := stackRow (S := outRest))
        (SelectOpRow.witness (target := target) (skip := skip) (S := rest) (out := outRest)))

/--
Eliminate the `(skip+1)`-th occurrence of `target` in stack `S`.
-/
def handleAtIndex
    [EffectSig target] [EffectSig S] [EffectSig out]
    [SelectOp target skip S out]
    (onTarget :
      {X : Type} →
      (op : EffectSig.Op (E := target) X) →
      (EffectSig.Res (E := target) op → Pending1 out A) →
      Pending1 out A) :
    Pending1 S A → Pending1 out A
  | .pure value => .pure value
  | .defer thunk => .defer (fun _ => handleAtIndex (target := target) (skip := skip) (S := S) (out := out) onTarget (thunk ()))
  | .request op cont =>
      match (SelectOp.project (target := target) (skip := skip) (S := S) (out := out) op) with
      | OpProjection.hit _ targetOp toSource =>
          onTarget targetOp (fun v => handleAtIndex (target := target) (skip := skip) (S := S) (out := out) onTarget (cont (toSource v)))
      | OpProjection.pass _ outOp toSource =>
          .request outOp (fun v => handleAtIndex (target := target) (skip := skip) (S := S) (out := out) onTarget (cont (toSource v)))

/-- Canonical row discharge equality induced by index-based selection. -/
theorem stackRow_discharge_at
    [StackRow S] [StackRow out]
    [SelectOpRow target skip S out] :
    Row.toRowSet (stackRow S) = Row.singletonRowSet target ++ Row.toRowSet (stackRow out) := by
  exact Row.toRowSet_remove_discharge
    (SelectOpRow.witness (target := target) (skip := skip) (S := S) (out := out))

namespace Validation

open Validation1
open EffectHandleNPath.Validation

def eliminateFirst : Pending1 EnvE Nat :=
  resolveDummy <|
    handleAtIndex (target := EnvE) (skip := 0) (S := DupStack3) (out := EffectSum.Effect EnvE Dummy)
      (onTarget := fun {_X} op cont =>
        match op with
        | Env.Op.get => cont (1 : Nat))
      dupProgram3

def evalFirstIdx : Option Nat :=
  Env.run (Value := Nat) 2 24 eliminateFirst

def eliminateSecond : Pending1 EnvE Nat :=
  resolveDummy <|
    handleAtIndex (target := EnvE) (skip := 1) (S := DupStack3) (out := EffectSum.Effect EnvE Dummy)
      (onTarget := fun {_X} op cont =>
        match op with
        | Env.Op.get => cont (9 : Nat))
      dupProgram3

def evalSecondIdx : Option Nat :=
  Env.run (Value := Nat) 4 24 eliminateSecond

theorem evalFirstIdx_spec : evalFirstIdx = some 12 := by
  native_decide

theorem evalSecondIdx_spec : evalSecondIdx = some 49 := by
  native_decide

end Validation

end EffectHandleNSelect
end Kernel
end Klean
