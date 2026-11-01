import Greedy.SnapshotTransport

/-! Preparation preserves both immutable labels and the original creator. -/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

variable {n : ℕ} {history : LabelHistory.History (External n)}

theorem detachAll_snapshots (before : BST 0 n) (key start : ℕ) (states : HeapSides n)
    (snapshots : HeapSnapshots history states) :
    HeapSnapshots history (detachAll before key (conversionNames start) (conversionNames start) states) := by
  have converted := convertHeap_snapshots before.externalDepth
    (fun owner side => growerHasKey key (states owner side)) start states snapshots
  intro owner side entry creator member
  have equal : detachAll before key (conversionNames start) (conversionNames start) states owner side =
      eraseFrozenKey key ((convertHeap before.externalDepth
        (fun owner side => growerHasKey key (states owner side)) start states).1 owner side) := by
    rw [convertHeap_apply]
    rfl
  rw [equal] at member
  exact converted owner side entry creator (tagged_erase key _ _ _ member)

theorem detachPorts_snapshots (before : BST 0 n) (start : ℕ) (ports : List ℕ) (stage : ℕ)
    (states : HeapSides n) (snapshots : HeapSnapshots history states) :
    HeapSnapshots history (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1 := by
  induction ports generalizing stage states with
  | nil => exact snapshots
  | cons key rest ih =>
      apply ih (stage+1)
      exact detachAll_snapshots before key (start + Fintype.card (Place n)*stage) states snapshots

theorem allocateCuts_snapshots (cuts : List (ℕ × ℕ)) (start : ℕ) (states : HeapSides n)
    (snapshots : HeapSnapshots history states) :
    HeapSnapshots history (allocateCuts cuts start states).states := by
  apply snapshots.descendants (after := (allocateCuts cuts start states).states)
    (GrowthJournal.allocateCuts_grower cuts start states)
  intro owner side block member
  have exactState := congrArg Prod.fst (allocateCuts_eq cuts start states)
  dsimp only at exactState
  rw [← exactState] at member
  obtain ⟨old, oldMem, descendant⟩ := prepareCuts_descends (allocateCuts cuts start states).names cuts 0 states owner side block member
  exact ⟨owner, side, old, oldMem, descendant⟩

theorem rebase_snapshots (before after : BST 0 n) (states : HeapSides n)
    (snapshots : HeapSnapshots history states) : HeapSnapshots history (rebaseAll before after states) := by
  apply snapshots.descendants (after := rebaseAll before after states) (fun _ _ => rfl)
  intro owner side block member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, rfl, rfl, List.Sublist.refl _⟩

theorem junction_snapshots (oldOwner newOwner : External n) (lo hi start : ℕ) (states : HeapSides n)
    (snapshots : HeapSnapshots history states) :
    HeapSnapshots history (allocateJunction oldOwner newOwner lo hi start states).states := by
  apply snapshots.descendants (GrowthJournal.junction_grower oldOwner newOwner lo hi start states)
  intro owner side block member
  rw [allocateJunction_eq] at member
  unfold moveJunction at member
  split_ifs at member with old new
  · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
      (states oldOwner side) block (List.mem_append_left _ member)
    exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · change block ∈ (states newOwner side).shrinking ++ _ at member
    rcases List.mem_append.mp member with previous | moved
    · exact ⟨newOwner, side, block, previous, descends_refl _⟩
    · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
        (states oldOwner side) block (List.mem_append_right _ moved)
      exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · exact ⟨owner, side, block, member, descends_refl _⟩

theorem preparation_snapshots (before after : BST 0 n) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (snapshots : HeapSnapshots history states) :
    HeapSnapshots history (preparedForCuts before after start ports owners states) := by
  classical
  have grown := convertHeap_snapshots before.externalDepth
    (fun owner side => decide (GrowerMismatch before after owner (states owner side))) start states snapshots
  rw [← prepareAllGrowers_fresh_eq] at grown
  have removed := detachPorts_snapshots before start ports 1 _ grown
  have sealed := convertHeap_snapshots before.externalDepth (fun owner _ => decide (owner ∈ owners))
    (start + Fintype.card (Place n)*(ports.length+1)) _ removed
  rw [← sealOwners_fresh_eq] at sealed
  simpa only [preparedForCuts, sequenceNames, Nat.mul_zero, Nat.add_zero] using sealed

theorem allocated_preparation_snapshots {depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (snapshots : HeapSnapshots history states) :
    HeapSnapshots history (allocateComparatorPreparation profile ports owners start states).states :=
  allocateCuts_snapshots profile.entries _ _ (preparation_snapshots before after start ports owners states snapshots)

end Greedy.LabelSnapshots
