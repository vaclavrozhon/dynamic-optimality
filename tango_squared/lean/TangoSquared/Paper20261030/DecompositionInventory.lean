import TangoSquared.Paper20261030.SourceRecordInventory

/-!
# Maintained decompositions preserve immutable record identities

Ignore the mutable cache and component-entry marker, and observe any
function of the original key and application payload. The complete
inventory of the balanced physical representation equals the reference
inventory. This includes all off-path components and terminal records.
-/

namespace TangoSquared.Paper20261030.BoundaryObservations

open ColoredStorage AuxiliaryComponent

variable {α κ ι : Type*} {β : κ → Type*}

def unmarked (entry : Sigma (Tagged β)) : Sigma β := ⟨entry.1,entry.2.1⟩

def identifyRecord (identify : Sigma β → ι) (record : Record (β := β)) : ι :=
  identify (unmarked record.2)

theorem closed_inventory (identify : Sigma β → ι) (c : AuxiliaryComponent α κ (Tagged β)) :
    (closed c).inventory (identifyRecord identify) = c.tree.inventory (identifyRecord identify) := by
  exact Source.inventory_setRoot _ _ _ rfl

end TangoSquared.Paper20261030.BoundaryObservations

namespace TangoSquared.Paper20261030.PathDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations

variable {α κ ι : Type*} {β : κ → Type*} [Ord κ]

theorem Represents.inventory (identify : Sigma β → ι) {right : Record (β := β) → Bool}
    {reference : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (represented : Represents right reference c) :
    c.tree.inventory (identifyRecord identify) = reference.inventory (identifyRecord identify) := by
  induction represented with
  | leaf marked same => exact same.inventory (fun entry => identify (unmarked entry))
  | @left record l r lc rc c direction clean hl hr same ihl ihr =>
    change c.tree.inventory (fun record => identify (unmarked record.2)) = _
    rw [same.inventory (fun entry => identify (unmarked entry)),
      append_inventory (fun entry => identify (unmarked entry))]
    change {identifyRecord identify record} + lc.tree.inventory (identifyRecord identify) +
      (closed rc).inventory (identifyRecord identify) = _
    rw [closed_inventory,ihl,ihr,Source.inventory_fork]
  | @right record l r lc rc c direction clean hl hr same ihl ihr =>
    change c.tree.inventory (fun record => identify (unmarked record.2)) = _
    rw [same.inventory (fun entry => identify (unmarked entry)),
      prepend_inventory (fun entry => identify (unmarked entry))]
    change {identifyRecord identify record} + (closed lc).inventory (identifyRecord identify) +
      rc.tree.inventory (identifyRecord identify) = _
    rw [closed_inventory,ihl,ihr,Source.inventory_fork]

theorem Represents.closed_inventory (identify : Sigma β → ι) {right : Record (β := β) → Bool}
    {reference : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (represented : Represents right reference c) :
    (closed c).inventory (identifyRecord identify) = reference.inventory (identifyRecord identify) := by
  rw [BoundaryObservations.closed_inventory,represented.inventory]

end TangoSquared.Paper20261030.PathDecomposition
