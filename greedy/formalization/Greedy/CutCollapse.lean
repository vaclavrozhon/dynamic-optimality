import Greedy.SourceCollapse
import Greedy.AccessDescendants

/-!
After a complete access crosses a historical cut inside a family, every
remaining fragment of that family avoids the cut. Global fragment order
identifies the one possible crossing fragment; the literal source return
removes its crossing. No future consolidation certificate is assumed.
-/

namespace Greedy.ClosedFamilies

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.FrozenHistory

theorem frozen_owner_unique {n next : ℕ} (states : HeapSides n) (inventory : HeapInventory states next)
    (first second : External n) (firstSide secondSide : Bool) (block : Frozen)
    (firstMem : block ∈ (states first firstSide).shrinking)
    (secondMem : block ∈ (states second secondSide).shrinking) : first = second := by
  have places := inventory.locations (encode n (first, firstSide)) (encode n (second, secondSide)) block.id
    (by simp only [table, Equiv.symm_apply_apply]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨block, firstMem, rfl⟩))
    (by simp only [table, Equiv.symm_apply_apply]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨block, secondMem, rfl⟩))
  exact congrArg Prod.fst ((encode n).injective places)

theorem runLinks_cut_collapse {n access clock next cut : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val = 2*access+1)
    (zero : (Snapshot.ofTree comparator).rank source = 0)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (states : HeapSides n) (inv : FamilyOrder.Invariant clock next states)
    (ready : Ready comparator newTree (runLinks source sourceSide reader clock states data.events))
    (side : Bool) (block : Frozen) (member : block ∈ (states source side).shrinking)
    (crosses : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins block)) :
    HeapClosed block.family (AvoidsCut cut) (runLinks source sourceSide reader clock states data.events) := by
  have closed : HeapClosed block.family (fun _ => True) states :=
    family_closed (table states) inv.names (encode n (source, side)) block
      (by simpa [table] using member) (fun _ => True) (by intros; trivial)
  have after := runLinks_closed source sourceSide reader clock states data.events closed
    (by intro _ _ _ _; trivial)
  apply after.with_property (AvoidsCut cut)
  intro slot fragment fragmentMem family
  let owner := ((encode n).symm slot).1
  let direction := ((encode n).symm slot).2
  change fragment ∈ (runLinks source sourceSide reader clock states data.events owner direction).shrinking at fragmentMem
  obtain ⟨old, oldMem, descendant⟩ := runLinks_descendant source sourceSide reader clock states data.events
    owner direction fragment fragmentMem
  by_cases avoids : AvoidsCut cut old
  · exact avoidsCut_hereditary cut descendant avoids
  · have oldCross : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins old) := by
      exact not_not.mp avoids
    have equal := inv.straddling_block_unique owner source direction side old block oldMem member
      (descendant.1.symm.trans family) cut oldCross crosses
    have ownerEq := frozen_owner_unique states inv.ids owner source direction side block (equal ▸ oldMem) member
    exact completed_source_avoids data source real zero _ ready direction fragment
      (by simpa only [ownerEq] using fragmentMem) cut

end Greedy.ClosedFamilies
