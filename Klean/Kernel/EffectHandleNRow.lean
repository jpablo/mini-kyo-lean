import Klean.Kernel.EffectHandleN
import Klean.Kernel.Row

/-!
Row-semantic bridge for `EffectHandleN`.

This module maps nested sum stacks to row obligations and provides recursive
`Row.Remove` witnesses aligned with generic target elimination shapes.
-/

namespace Klean
namespace Kernel
namespace EffectHandleNRow

/-- Row view of a runtime effect stack type. -/
class StackRow (S : Type) where
  row : Row

/-- Convenience accessor. -/
def stackRow (S : Type) [StackRow S] : Row :=
  StackRow.row (S := S)

@[default_instance 300]
instance stackRowVoid : StackRow EffectHandleN.VoidEffect where
  row := Row.empty

@[default_instance 200]
instance stackRowSum [StackRow tail] : StackRow (EffectSum.Effect head tail) where
  row := Row.singleton head ++ stackRow tail

@[default_instance 100]
instance stackRowLeaf [EffectSig S] : StackRow S where
  row := Row.singleton S

/--
Row-level removal witness for one generic target elimination step.
-/
class RemoveOpRow (target S out : Type) [StackRow S] [StackRow out] where
  witness : Row.Remove target (stackRow S) (stackRow out)

@[default_instance 200]
instance removeOpRowHead [StackRow out] : RemoveOpRow target (EffectSum.Effect target out) out where
  witness := by
    simpa [stackRow, Row.singleton, Row.append] using
      (Row.Remove.head (effect := target) (tail := stackRow out))

@[default_instance 150]
instance removeOpRowSelf [EffectSig target] : RemoveOpRow target target EffectHandleN.VoidEffect where
  witness := by
    simpa [stackRow, Row.singleton] using
      (Row.Remove.head (effect := target) (tail := Row.empty))

@[default_instance 100]
instance removeOpRowTail
    [StackRow rest] [StackRow outRest]
    [RemoveOpRow target rest outRest] :
    RemoveOpRow target (EffectSum.Effect head rest) (EffectSum.Effect head outRest) where
  witness := by
    simpa [stackRow, Row.singleton, Row.append] using
      (Row.Remove.tail (head := head) (tail := stackRow (S := rest)) (out := stackRow (S := outRest))
        (RemoveOpRow.witness (target := target) (S := rest) (out := outRest)))

/--
Canonical row-set discharge equality induced by `RemoveOpRow`.
-/
theorem stackRow_discharge {target S out : Type} [StackRow S] [StackRow out] [RemoveOpRow target S out] :
    Row.toRowSet (stackRow S) = Row.singletonRowSet target ++ Row.toRowSet (stackRow out) := by
  exact Row.toRowSet_remove_discharge (RemoveOpRow.witness (target := target) (S := S) (out := out))

namespace Validation

open EffectHandleN.Validation

theorem stack4_abort_discharge :
    Row.toRowSet (stackRow Stack4) =
      Row.singletonRowSet AbortE ++
      Row.toRowSet (stackRow (EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))) := by
  simpa using
    (stackRow_discharge (target := AbortE) (S := Stack4)
      (out := EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect)))

theorem stack_after_env_discharge :
    Row.toRowSet (stackRow (EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))) =
      Row.singletonRowSet EnvE ++
      Row.toRowSet (stackRow (EffectSum.Effect VarE DummyEffect)) := by
  simpa using
    (stackRow_discharge (target := EnvE) (S := EffectSum.Effect EnvE (EffectSum.Effect VarE DummyEffect))
      (out := EffectSum.Effect VarE DummyEffect))

theorem stack_after_dummy_discharge :
    Row.toRowSet (stackRow (EffectSum.Effect VarE DummyEffect)) =
      Row.singletonRowSet DummyEffect ++
      Row.toRowSet (stackRow (EffectSum.Effect VarE EffectHandleN.VoidEffect)) := by
  simpa using
    (stackRow_discharge (target := DummyEffect) (S := EffectSum.Effect VarE DummyEffect)
      (out := EffectSum.Effect VarE EffectHandleN.VoidEffect))

end Validation

end EffectHandleNRow
end Kernel
end Klean
