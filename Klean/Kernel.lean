import Klean.Kernel.Row
import Klean.Kernel.Pending
import Klean.Kernel.Pending1
import Klean.Kernel.Effect
import Klean.Kernel.ArrowEffect
import Klean.Kernel.ContextEffect
import Klean.Kernel.Discharge
import Klean.Kernel.Validation

/-!
Kernel root module for Klean.

This module re-exports the current kernel foundation:
- effect rows (`Row`)
- pending computations (`Pending`)
- single-effect generic pending computations (`Pending1`)
- basic effect helpers (`Effect`)
- single-effect request/handler facade (`ArrowEffect`)
- single-effect context requests/handlers (`ContextEffect`)
- row-aware discharge bridge (`Discharge`)
- validation scenarios (`Validation`)
-/
