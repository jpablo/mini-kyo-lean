import Klean.Kernel.Pending
import Klean.Kernel.Pending1

/-!
Minimal single-effect `ArrowEffect` façade for Klean.

This module provides:
- generic suspension helpers over `Pending1`
- a fold-based handler eliminator into closed `Pending`

This captures the core "request + continuation handled by interpreter" shape
from Scala `ArrowEffect` in a Lean-friendly single-effect stage.
-/

namespace Klean
namespace Kernel
namespace ArrowEffect

/-- Suspend one typed operation and return its result. -/
def suspend [EffectSig E] (op : EffectSig.Op (E := E) X) :
    Pending1 E (EffectSig.Res (E := E) op) :=
  .request op (fun out => .pure out)

/-- Suspend one typed operation and continue with a custom continuation. -/
def suspendWith [EffectSig E] (op : EffectSig.Op (E := E) X)
    (f : EffectSig.Res (E := E) op → Pending1 E A) : Pending1 E A :=
  .request op f

/--
Fold/eliminate a single-effect pending computation into closed `Pending`.

`onRequest` receives each operation plus a continuation that already targets the
closed result space.
-/
def fold [EffectSig E]
    (onPure : A → Pending B Row.empty)
    (onRequest :
      {X : Type} →
      (op : EffectSig.Op (E := E) X) →
      (EffectSig.Res (E := E) op → Pending B Row.empty) →
      Pending B Row.empty) :
    Pending1 E A → Pending B Row.empty
  | .pure a => onPure a
  | .defer thunk => .defer (fun _ => fold onPure onRequest (thunk ()))
  | .request op cont => onRequest op (fun out => fold onPure onRequest (cont out))

/-- Specialized fold that preserves successful result values. -/
def handle [EffectSig E]
    (onRequest :
      {X : Type} →
      (op : EffectSig.Op (E := E) X) →
      (EffectSig.Res (E := E) op → Pending A Row.empty) →
      Pending A Row.empty) :
    Pending1 E A → Pending A Row.empty :=
  fold (onPure := Pending.pure) (onRequest := onRequest)

end ArrowEffect
end Kernel
end Klean
