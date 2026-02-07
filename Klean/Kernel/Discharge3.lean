import Klean.Kernel.Discharge
import Klean.Kernel.EffectSum3

/-!
Three-step row-aware discharge for nested 3-effect sums.
-/

namespace Klean
namespace Kernel
namespace Discharge3

/--
Handle three effects in sequence, threading explicit row-removal witnesses.
-/
def handleThreeRemoved [EffectSig E1] [EffectSig E2] [EffectSig E3]
    (_hRemove1 : Row.Remove E1 S S1)
    (_hRemove2 : Row.Remove E2 S1 S2)
    (hRemove3 : Row.Remove E3 S2 S3)
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
    (onE3 :
      {X : Type} →
      (op : EffectSig.Op (E := E3) X) →
      (EffectSig.Res (E := E3) op → Pending A S3) →
      Pending A S3)
    (program : Pending1 (EffectSum3.Effect E1 E2 E3) A) : Pending A S3 :=
  let after12 : Pending1 E3 A := EffectSum3.handle12 onE1 onE2 program
  Discharge.handleRemoved (S := S2) (out := S3) hRemove3 onE3 after12

/-- Obligations of `handleThreeRemoved` are exactly `S3`. -/
theorem handleThreeRemoved_obligations [EffectSig E1] [EffectSig E2] [EffectSig E3]
    (hRemove1 : Row.Remove E1 S S1)
    (hRemove2 : Row.Remove E2 S1 S2)
    (hRemove3 : Row.Remove E3 S2 S3)
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
    (onE3 :
      {X : Type} →
      (op : EffectSig.Op (E := E3) X) →
      (EffectSig.Res (E := E3) op → Pending A S3) →
      Pending A S3)
    (program : Pending1 (EffectSum3.Effect E1 E2 E3) A) :
    Pending.obligations (handleThreeRemoved (S := S) (S1 := S1) (S2 := S2) (S3 := S3)
      hRemove1 hRemove2 hRemove3 onE1 onE2 onE3 program) = Row.toRowSet S3 := rfl

/--
Semantic obligation shape after three sequential discharges.
-/
theorem handleThreeRemoved_discharge_shape [EffectSig E1] [EffectSig E2] [EffectSig E3]
    (hRemove1 : Row.Remove E1 S S1)
    (hRemove2 : Row.Remove E2 S1 S2)
    (hRemove3 : Row.Remove E3 S2 S3)
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
    (onE3 :
      {X : Type} →
      (op : EffectSig.Op (E := E3) X) →
      (EffectSig.Res (E := E3) op → Pending A S3) →
      Pending A S3)
    (program : Pending1 (EffectSum3.Effect E1 E2 E3) A) :
    Row.toRowSet S =
      ((Row.singletonRowSet E1 ++ Row.singletonRowSet E2) ++ Row.singletonRowSet E3) ++
      Pending.obligations (handleThreeRemoved (S := S) (S1 := S1) (S2 := S2) (S3 := S3)
        hRemove1 hRemove2 hRemove3 onE1 onE2 onE3 program) := by
  have h1 : Row.toRowSet S = Row.singletonRowSet E1 ++ Row.toRowSet S1 :=
    Row.toRowSet_remove_discharge hRemove1
  have h2 : Row.toRowSet S1 = Row.singletonRowSet E2 ++ Row.toRowSet S2 :=
    Row.toRowSet_remove_discharge hRemove2
  have h3 : Row.toRowSet S2 = Row.singletonRowSet E3 ++ Row.toRowSet S3 :=
    Row.toRowSet_remove_discharge hRemove3
  calc
    Row.toRowSet S = Row.singletonRowSet E1 ++ Row.toRowSet S1 := h1
    _ = Row.singletonRowSet E1 ++ (Row.singletonRowSet E2 ++ Row.toRowSet S2) := by
      rw [h2]
    _ = (Row.singletonRowSet E1 ++ Row.singletonRowSet E2) ++ Row.toRowSet S2 := by
      symm
      exact Row.appendRowSet_assoc _ _ _
    _ = (Row.singletonRowSet E1 ++ Row.singletonRowSet E2) ++ (Row.singletonRowSet E3 ++ Row.toRowSet S3) := by
      rw [h3]
    _ = ((Row.singletonRowSet E1 ++ Row.singletonRowSet E2) ++ Row.singletonRowSet E3) ++ Row.toRowSet S3 := by
      symm
      exact Row.appendRowSet_assoc _ _ _
    _ = ((Row.singletonRowSet E1 ++ Row.singletonRowSet E2) ++ Row.singletonRowSet E3) ++
          Pending.obligations (handleThreeRemoved (S := S) (S1 := S1) (S2 := S2) (S3 := S3)
            hRemove1 hRemove2 hRemove3 onE1 onE2 onE3 program) := by
      simp [handleThreeRemoved_obligations (S := S) (S1 := S1) (S2 := S2) (S3 := S3)
        hRemove1 hRemove2 hRemove3 onE1 onE2 onE3 program]

end Discharge3
end Kernel
end Klean
