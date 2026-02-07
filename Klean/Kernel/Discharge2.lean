import Klean.Kernel.Discharge
import Klean.Kernel.EffectSum

/-!
Two-step row-aware discharge for summed effects.

This composes:
1) executable left-effect handling (`EffectSum.handleLeft`)
2) row-aware discharge for the remaining effect (`Discharge.handleRemoved`)
-/

namespace Klean
namespace Kernel
namespace Discharge2

/--
Handle two effects in sequence, threading explicit row-removal witnesses.

First we handle `E1` from a summed program `EffectSum.Effect E1 E2`, producing a
program in `E2`. Then we discharge `E2` into residual row `S2`.
-/
def handleTwoRemoved [EffectSig E1] [EffectSig E2] {S S1 S2 : Row}
    (_hRemove1 : Row.Remove E1 S S1)
    (hRemove2 : Row.Remove E2 S1 S2)
    (onLeft :
      {X : Type} →
      (op : EffectSig.Op (E := E1) X) →
      (EffectSig.Res (E := E1) op → Pending1 E2 A) →
      Pending1 E2 A)
    (onRight :
      {X : Type} →
      (op : EffectSig.Op (E := E2) X) →
      (EffectSig.Res (E := E2) op → Pending A S2) →
      Pending A S2)
    (program : Pending1 (EffectSum.Effect E1 E2) A) : Pending A S2 :=
  let afterLeft : Pending1 E2 A := EffectSum.handleLeft (E1 := E1) (E2 := E2) onLeft program
  Discharge.handleRemoved (S := S1) (out := S2) hRemove2 onRight afterLeft

/-- Obligations of `handleTwoRemoved` are exactly `S2`. -/
theorem handleTwoRemoved_obligations [EffectSig E1] [EffectSig E2] {S S1 S2 : Row}
    (hRemove1 : Row.Remove E1 S S1)
    (hRemove2 : Row.Remove E2 S1 S2)
    (onLeft :
      {X : Type} →
      (op : EffectSig.Op (E := E1) X) →
      (EffectSig.Res (E := E1) op → Pending1 E2 A) →
      Pending1 E2 A)
    (onRight :
      {X : Type} →
      (op : EffectSig.Op (E := E2) X) →
      (EffectSig.Res (E := E2) op → Pending A S2) →
      Pending A S2)
    (program : Pending1 (EffectSum.Effect E1 E2) A) :
    Pending.obligations (handleTwoRemoved (S := S) (S1 := S1) (S2 := S2) hRemove1 hRemove2 onLeft onRight program) =
      Row.toRowSet S2 := rfl

/--
Semantic obligation shape after two sequential discharges.
-/
theorem handleTwoRemoved_discharge_shape [EffectSig E1] [EffectSig E2] {S S1 S2 : Row}
    (hRemove1 : Row.Remove E1 S S1)
    (hRemove2 : Row.Remove E2 S1 S2)
    (onLeft :
      {X : Type} →
      (op : EffectSig.Op (E := E1) X) →
      (EffectSig.Res (E := E1) op → Pending1 E2 A) →
      Pending1 E2 A)
    (onRight :
      {X : Type} →
      (op : EffectSig.Op (E := E2) X) →
      (EffectSig.Res (E := E2) op → Pending A S2) →
      Pending A S2)
    (program : Pending1 (EffectSum.Effect E1 E2) A) :
    Row.toRowSet S =
      (Row.singletonRowSet E1 ++ Row.singletonRowSet E2) ++
      Pending.obligations (handleTwoRemoved (S := S) (S1 := S1) (S2 := S2) hRemove1 hRemove2 onLeft onRight program) := by
  have h1 : Row.toRowSet S = Row.singletonRowSet E1 ++ Row.toRowSet S1 :=
    Row.toRowSet_remove_discharge hRemove1
  have h2 : Row.toRowSet S1 = Row.singletonRowSet E2 ++ Row.toRowSet S2 :=
    Row.toRowSet_remove_discharge hRemove2
  calc
    Row.toRowSet S = Row.singletonRowSet E1 ++ Row.toRowSet S1 := h1
    _ = Row.singletonRowSet E1 ++ (Row.singletonRowSet E2 ++ Row.toRowSet S2) := by
      rw [h2]
    _ = (Row.singletonRowSet E1 ++ Row.singletonRowSet E2) ++ Row.toRowSet S2 := by
      symm
      exact Row.appendRowSet_assoc _ _ _
    _ = (Row.singletonRowSet E1 ++ Row.singletonRowSet E2) ++
          Pending.obligations (handleTwoRemoved (S := S) (S1 := S1) (S2 := S2) hRemove1 hRemove2 onLeft onRight program) := by
      simp [handleTwoRemoved_obligations (S := S) (S1 := S1) (S2 := S2) hRemove1 hRemove2 onLeft onRight program]

end Discharge2
end Kernel
end Klean
