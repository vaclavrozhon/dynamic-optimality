import MultiSplay.InterfaceHistory

/-!
# A component's persistent records inside a shared interface history

A placement records the actual global block IDs, the embedding of elements,
and agreement of values. Retired creators may use local proxies; observable
agreement preserves their actual global identities and all operational data.
Separation of passive records is a further property, not assumed by placement.
-/

namespace MultiSplay.InterfacePlacement

open Splay.Interface

structure Placement {n m : Nat} (component : State n) (whole : State m) where
  element : Element n → Element m
  element_injective : Function.Injective element
  id : Fin component.blocks.length → BlockId
  id_injective : Function.Injective id
  lookup : ∀ i, ∃ block, whole.block? (id i) = some block ∧
    InterfaceHistory.observable (InterfaceEmbedding.block element (component.blocks.get i)) = InterfaceHistory.observable block
  value : ∀ x, whole.value (element x) = component.value x

end MultiSplay.InterfacePlacement
