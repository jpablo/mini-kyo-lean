import Klean.Kernel.ArrowEffect
import Klean.Kernel.Row

/-!
Row-aware handler discharge bridge.

This module connects:
- single-effect request handling (`Pending1` + `ArrowEffect.handleInto`)
- row-level discharge witnesses (`Row.Remove`)

The runtime interpretation is still single-effect, but signatures now carry
explicit row-removal evidence to prepare the multi-effect integration path.
-/

namespace Klean
namespace Kernel
namespace Discharge

/--
Handle a single-effect pending program into residual row `out`, requiring an
explicit witness that handling `E` discharges `S` to `out`.
-/
def handleRemoved [EffectSig E] {S out : Row}
    (_hRemove : Row.Remove E S out)
    (onRequest :
      {X : Type} →
      (op : EffectSig.Op (E := E) X) →
      (EffectSig.Res (E := E) op → Pending A out) →
      Pending A out)
    (program : Pending1 E A) : Pending A out :=
  ArrowEffect.handleInto (S := out) onRequest program

/-- Obligations of `handleRemoved` are exactly the residual row `out`. -/
theorem handleRemoved_obligations [EffectSig E] {S out : Row}
    (hRemove : Row.Remove E S out)
    (onRequest :
      {X : Type} →
      (op : EffectSig.Op (E := E) X) →
      (EffectSig.Res (E := E) op → Pending A out) →
      Pending A out)
    (program : Pending1 E A) :
    Pending.obligations (handleRemoved (S := S) (out := out) hRemove onRequest program) = Row.toRowSet out := rfl

/--
Semantic discharge shape induced by the provided `Remove` witness.
-/
theorem handleRemoved_discharge_shape [EffectSig E] {S out : Row}
    (hRemove : Row.Remove E S out)
    (onRequest :
      {X : Type} →
      (op : EffectSig.Op (E := E) X) →
      (EffectSig.Res (E := E) op → Pending A out) →
      Pending A out)
    (program : Pending1 E A) :
    Row.toRowSet S = Row.singletonRowSet E ++ Pending.obligations (handleRemoved (S := S) (out := out) hRemove onRequest program) := by
  calc
    Row.toRowSet S = Row.singletonRowSet E ++ Row.toRowSet out := Row.toRowSet_remove_discharge hRemove
    _ = Row.singletonRowSet E ++ Pending.obligations (handleRemoved (S := S) (out := out) hRemove onRequest program) := by
      simp [handleRemoved_obligations (S := S) (out := out) hRemove onRequest program]

end Discharge
end Kernel
end Klean
