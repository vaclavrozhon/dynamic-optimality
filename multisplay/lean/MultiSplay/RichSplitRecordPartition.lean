import MultiSplay.RichSplitArchive
import MultiSplay.InterfacePacking

/-! # Exact partition of split records into the surviving components and archive -/

namespace MultiSplay.RichSplit

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element Side)
open Splay.Lazy.Canonical

variable {l r : Nat} {params : Splay.Interface.Parameters}

def retiredRecord {n : Nat} (pivot : Element n) (block : Block n) : Splay.Interface.Block n :=
  if block.owner = pivot then {block.toInterface with mode := .shrinking, elements := []} else block.toInterface

theorem record_eq (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftEq : boundary.left = JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl))
    (rightEq : boundary.right = JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r)
    (id : Fin source.blocks.length) :
    boundary.record id.val (source.blocks.get id).toInterface = retiredRecord (JoinRanks.pivot l r) (source.blocks.get id) := by
  by_cases owner : (source.blocks.get id).owner = JoinRanks.pivot l r
  · rw [retiredRecord, if_pos owner]
    have creator := boundary.record_creator id.val (source.blocks.get id).toInterface
    have passes := boundary.record_passCount id.val (source.blocks.get id).toInterface
    have mode := pivot_record_shrinking left right sl sr source represented boundary leftCreator rightCreator id owner
    have payload := pivot_record_empty left right sl sr source represented boundary leftEq rightEq id owner
    cases record : boundary.record id.val (source.blocks.get id).toInterface
    simp only [record] at creator passes mode payload
    simp only [Splay.Interface.Block.mk.injEq]
    exact ⟨creator, passes, mode, payload⟩
  · rw [retiredRecord, if_neg owner]
    have old := retained_lookup left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator id owner
    exact Option.some.inj ((boundary.final_lookup id.val _ (RichSplitBoundary.interface_lookup source id)).symm.trans old)

theorem final_blocks (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftEq : boundary.left = JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl))
    (rightEq : boundary.right = JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r) :
    boundary.final.blocks = source.blocks.map (retiredRecord (JoinRanks.pivot l r)) := by
  apply List.ext_getElem?
  intro id
  by_cases inside : id < source.blocks.length
  · let richId : Fin source.blocks.length := ⟨id, inside⟩
    have found := boundary.final_lookup id _ (RichSplitBoundary.interface_lookup source richId)
    rw [record_eq left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator richId] at found
    simpa only [Splay.Interface.State.block?, List.getElem?_map, List.getElem?_eq_getElem inside, List.get_eq_getElem, Option.map_some] using found
  · have outside : boundary.final.blocks.length ≤ id := by
      rw [boundary.final_blocks_length]
      simpa only [State.toInterface, List.length_map] using Nat.le_of_not_gt inside
    rw [List.getElem?_eq_none outside, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt inside)]
    rfl

end MultiSplay.RichSplit

namespace MultiSplay.RichRestriction

open Splay.Lazy (State Block Element HeapView)

variable {n m : Nat} {params : Splay.Interface.Parameters}

theorem observable_selected_block (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) (block : Block m) (member : block ∈ source.blocks)
    (inside : block.owner ∈ Set.range embedding.element) :
    InterfaceHistory.observable (InterfaceEmbedding.block embedding.element (BlockEmbedding.block embedding.project block).toInterface) =
      InterfaceHistory.observable block.toInterface := by
  apply InterfaceHistory.observable_eq.mpr
  refine ⟨rfl, rfl, old_elements_map source small embedding stable block member inside, ?_⟩
  intro growing
  change embedding.element (embedding.project block.creator) = block.creator
  apply embedding.element_project
  rw [← (stable.valid.2 block member).2.1 growing]
  exact inside

theorem observable_selected (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) :
    ((state source small embedding).toInterface.blocks.map (InterfaceEmbedding.block embedding.element)).map InterfaceHistory.observable =
      ((source.blocks.filter (fun block => decide (block.owner ∈ Set.range embedding.element))).map Block.toInterface).map InterfaceHistory.observable := by
  classical
  rw [← selected_eq_filter source embedding]
  simp only [state, State.toInterface, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro id member
  exact observable_selected_block source small embedding stable _ (List.get_mem _ id) ((mem_ids source embedding id).mp member)

end MultiSplay.RichRestriction
