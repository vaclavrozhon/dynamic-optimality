import Greedy.RunCutCollapse

/-! Once a membership survives a full access, it is isolated forever. -/

namespace Greedy.FamilyOrder

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.FrozenHistory GreedyMerge.HistoryProcess

theorem membership_block_unique (blocks : List Frozen) (valid : GreedyMerge.HistoryProcess.Valid blocks)
    (first second : Frozen) (firstMem : first ∈ blocks) (secondMem : second ∈ blocks)
    (family : first.family = second.family) (joined : ℕ)
    (firstJoin : joined ∈ joins first) (secondJoin : joined ∈ joins second) : first = second := by
  by_contra different
  have separate := separated_of_members blocks valid.1 first second firstMem secondMem different
  rcases separate with other | forward | backward
  · exact other family
  · exact (Nat.lt_irrefl joined) (forward joined firstJoin joined secondJoin)
  · exact (Nat.lt_irrefl joined) (backward joined secondJoin joined firstJoin)

theorem Invariant.membership_block_unique {n clock next : ℕ} {states : HeapSides n}
    (inv : Invariant clock next states) (firstOwner secondOwner : External n) (firstSide secondSide : Bool)
    (first second : Frozen) (firstMem : first ∈ (states firstOwner firstSide).shrinking)
    (secondMem : second ∈ (states secondOwner secondSide).shrinking) (family : first.family = second.family)
    (joined : ℕ) (firstJoin : joined ∈ joins first) (secondJoin : joined ∈ joins second) : first = second :=
  Greedy.FamilyOrder.membership_block_unique _ (allFrozen_valid (table states) inv.ordered) first second
    (heap_mem_allFrozen states firstOwner firstSide first firstMem) (heap_mem_allFrozen states secondOwner secondSide second secondMem)
    family joined firstJoin secondJoin

end Greedy.FamilyOrder

namespace Greedy.ClosedFamilies

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.FrozenHistory

def Isolated (joined : ℕ) (block : Frozen) : Prop := joined ∈ joins block → joins block ⊆ {joined}

theorem isolated_hereditary (joined : ℕ) : Hereditary (Isolated joined) := by
  intro before after descendant isolated present other otherMem
  exact isolated (descends_joins descendant present) (descends_joins descendant otherMem)

theorem isolated_of_avoids_all_cuts (block : Frozen) (avoids : ∀ cut, AvoidsCut cut block) (joined : ℕ) : Isolated joined block := by
  intro present other otherMem
  apply Finset.mem_singleton.mpr
  by_contra different
  by_cases less : other < joined
  · exact avoids (other+1) ((GreedyForest.straddles_nat_cut_iff (other+1) _).mpr
      ⟨other, otherMem, joined, present, by omega, by omega⟩)
  · exact avoids (joined+1) ((GreedyForest.straddles_nat_cut_iff (joined+1) _).mpr
      ⟨joined, present, other, otherMem, by omega, by omega⟩)

theorem runLinks_isolates {n access clock next joined : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val = 2*access+1)
    (zero : (Snapshot.ofTree comparator).rank source = 0)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (states : HeapSides n) (inv : FamilyOrder.Invariant clock next states)
    (ready : Ready comparator newTree (runLinks source sourceSide reader clock states data.events))
    (side : Bool) (block : Frozen) (member : block ∈ (states source side).shrinking) (present : joined ∈ joins block) :
    HeapClosed block.family (Isolated joined) (runLinks source sourceSide reader clock states data.events) := by
  have closed : HeapClosed block.family (fun _ => True) states :=
    family_closed (table states) inv.names (encode n (source, side)) block
      (by simpa [table] using member) (fun _ => True) (by intros; trivial)
  have after := runLinks_closed source sourceSide reader clock states data.events closed (by intro _ _ _ _; trivial)
  apply after.with_property (Isolated joined)
  intro slot fragment fragmentMem family
  let owner := ((encode n).symm slot).1
  let direction := ((encode n).symm slot).2
  change fragment ∈ (runLinks source sourceSide reader clock states data.events owner direction).shrinking at fragmentMem
  obtain ⟨old, oldMem, descendant⟩ := runLinks_descendant source sourceSide reader clock states data.events owner direction fragment fragmentMem
  intro stillPresent
  have oldPresent := descends_joins descendant stillPresent
  have equal := inv.membership_block_unique owner source direction side old block oldMem member
    (descendant.1.symm.trans family) joined oldPresent present
  have ownerEq := frozen_owner_unique states inv.ids owner source direction side block (equal ▸ oldMem) member
  have isolated := isolated_of_avoids_all_cuts fragment
    (completed_source_avoids data source real zero _ ready direction fragment (by simpa only [ownerEq] using fragmentMem)) joined
  exact isolated stillPresent

theorem afterAccess_isolates {n joined : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition)
    (inv : FamilyOrder.Invariant before.clock before.next before.blocks)
    (valid : (Execution.afterAccess before request K decomposition data).Valid)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking)
    (present : joined ∈ joins block) :
    HeapClosed block.family (Isolated joined) (Execution.afterAccess before request K decomposition data).blocks ∧
      block.family < (Execution.afterAccess before request K decomposition data).next := by
  have prepared := FamilyOrder.convertHeap_invariant before.comparator.externalDepth
    (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks inv
  change FamilyOrder.Invariant before.clock (before.next + Fintype.card (Place n)) (RunJournal.prepared before request) at prepared
  have zero : (Snapshot.ofTree before.comparator).rank (Execution.source request) = 0 :=
    GreedyMerge.AccessFrontier.comparator_zero_of_global before.comparator (Execution.root_minimum _ request root)
  refine ⟨runLinks_isolates data (Execution.source request) rfl zero _ _
    (RunJournal.prepared before request) prepared valid.1 side block member present, ?_⟩
  have past := prepared.names.below (encode n (Execution.source request, side)) block.family
    (FamilyNames.frozen_mem _ block (by simpa [table] using member))
  simpa only [Execution.afterAccess, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using past

theorem remaining_sources_isolated {n joined : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition)
    (inv : FamilyOrder.Invariant before.clock before.next before.blocks)
    (valid : (Execution.afterAccess before request K decomposition data).Valid)
    {last : Execution.State n} {requests : List (Fin n)}
    (rest : Execution.Run K (Execution.afterAccess before request K decomposition data) last requests)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking)
    (present : joined ∈ joins block) : AllSourcesClosed (family := block.family) (Isolated joined) rest := by
  have isolated := afterAccess_isolates before request K root decomposition data inv valid side block member present
  exact all_sources_closed rest isolated.1 (isolated_hereditary joined) isolated.2

end Greedy.ClosedFamilies
