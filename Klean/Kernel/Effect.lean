import Klean.Kernel.Pending

/-!
Minimal kernel-level effect helpers.
-/

namespace Klean
namespace Kernel
namespace Effect

/-- Create a deferred pending step. -/
def defer {A : Type} {S : Row} (thunk : Unit → Pending A S) : Pending A S :=
  Pending.defer thunk

end Effect
end Kernel
end Klean
