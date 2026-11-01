import TangoSquared.Paper20261030.SourceRecordInventory
import TangoSquared.Paper20261030.SourceRecordMap
import Mathlib.Data.Multiset.UnionInter

/-!
# Identifier conservation across a primary head exchange

The active source has an exposed prefix and two boundary records; the
incoming source has one exposed boundary record. Switching heads moves
the incoming boundary and tail into the active source and leaves the old
boundary and tail dormant. Terminal records move with their own tails.

These are proof-side source views, not arguments to a runtime controller.
Their combined inventory is exactly conserved. A global inventory may
also include all untouched components. Its uniqueness implies uniqueness
of each new component and disjointness of their identifiers. Separate
uniqueness hypotheses for the two inputs would not suffice.
-/

namespace TangoSquared.Paper20261030.IdentifiedHeadExchange

open ColoredStorage

variable {α ρ ι : Type*}

structure Boundary (α ρ : Type*) where
  record : ρ
  terminal : Source α ρ
  tail : Source α ρ

def Boundary.tree (boundary : Boundary α ρ) : Source α ρ :=
  .fork boundary.record boundary.terminal boundary.tail

def active (low : ρ) (prefixTree : Source α ρ) (boundary : Boundary α ρ) : Source α ρ :=
  .fork low prefixTree boundary.tree

theorem inventory (identify : ρ → ι) (low : ρ) (prefixTree : Source α ρ)
    (old incoming : Boundary α ρ) :
    (active low prefixTree incoming).inventory identify + old.tree.inventory identify =
      (active low prefixTree old).inventory identify + incoming.tree.inventory identify := by
  simp only [active,Source.inventory_fork]
  ac_rfl

/-- The untouched part is included, so this invariant can be reused by
the next component update as well as by both reconstruction programs. -/
theorem global_unique (identify : ρ → ι) (low : ρ) (prefixTree : Source α ρ)
    (old incoming : Boundary α ρ) (untouched : Multiset ι)
    (unique : ((active low prefixTree old).inventory identify +
      incoming.tree.inventory identify + untouched).Nodup) :
    ((active low prefixTree incoming).inventory identify +
      old.tree.inventory identify + untouched).Nodup := by
  rw [inventory]
  exact unique

theorem component_unique (identify : ρ → ι) (low : ρ) (prefixTree : Source α ρ)
    (old incoming : Boundary α ρ) (untouched : Multiset ι)
    (unique : ((active low prefixTree old).inventory identify +
      incoming.tree.inventory identify + untouched).Nodup) :
    ((active low prefixTree incoming).inventory identify).Nodup ∧
      (old.tree.inventory identify).Nodup ∧
      Disjoint ((active low prefixTree incoming).inventory identify) (old.tree.inventory identify) := by
  exact Multiset.nodup_add.mp
    (Multiset.nodup_add.mp (global_unique identify low prefixTree old incoming untouched unique)).1

/-- Component-local executions preserve the same global invariant when
their checked compiler results preserve their individual inventories. -/
theorem replace_pair (identify : ρ → ι) (old incoming newActive newDormant : Source α ρ)
    (same : newActive.inventory identify + newDormant.inventory identify =
      old.inventory identify + incoming.inventory identify) (untouched : Multiset ι)
    (unique : (old.inventory identify + incoming.inventory identify + untouched).Nodup) :
    (newActive.inventory identify + newDormant.inventory identify + untouched).Nodup := by
  rw [same]
  exact unique

theorem Boundary.mapRecords_tree {τ : Type*} (f : ρ → τ) (boundary : Boundary α ρ) :
    boundary.tree.mapRecords f = .fork (f boundary.record)
      (boundary.terminal.mapRecords f) (boundary.tail.mapRecords f) := rfl

end TangoSquared.Paper20261030.IdentifiedHeadExchange
