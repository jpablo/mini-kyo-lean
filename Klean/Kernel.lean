import Klean.Kernel.Row
import Klean.Kernel.Pending
import Klean.Kernel.Pending1
import Klean.Kernel.Effect
import Klean.Kernel.ArrowEffect
import Klean.Kernel.ContextEffect
import Klean.Kernel.Discharge
import Klean.Kernel.EffectSum
import Klean.Kernel.EffectSum3
import Klean.Kernel.EffectReassoc
import Klean.Kernel.EffectHandle3
import Klean.Kernel.EffectHandleN
import Klean.Kernel.EffectHandleNRow
import Klean.Kernel.EffectHandleNCoupled
import Klean.Kernel.EffectHandleNApi
import Klean.Kernel.EffectHandleNPath
import Klean.Kernel.EffectNest
import Klean.Kernel.Discharge2
import Klean.Kernel.Discharge3
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
- executable 2-effect dispatch combinator (`EffectSum`)
- nested 3-effect composition helpers (`EffectSum3`)
- executable nested-sum re-association transforms (`EffectReassoc`)
- typeclass-driven 3-effect handler selection (`EffectHandle3`)
- generic recursive nested-sum target handling (`EffectHandleN`)
- row-semantic bridge for generic nested handling (`EffectHandleNRow`)
- coupled runtime+row elimination steps (`EffectHandleNCoupled`)
- higher-level generic elimination facade (`EffectHandleNApi`)
- explicit path-based duplicate-target handling (`EffectHandleNPath`)
- recursive nested-sum injection helpers (`EffectNest`)
- two-step row-aware summed-effect discharge (`Discharge2`)
- three-step row-aware nested-sum discharge (`Discharge3`)
- validation scenarios (`Validation`)
-/
