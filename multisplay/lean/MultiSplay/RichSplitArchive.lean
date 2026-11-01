import MultiSplay.RichSplitFramed

/-!
# The retired root archive of a common split

Every record formerly owned by the removed common root becomes an empty
shrinking record. Its immutable creator and pass count survive. These records
can therefore remain in the global archive, passive for every future component.
-/

namespace MultiSplay.RichSplit

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element Side)
open Splay.Lazy.Canonical

variable {l r : Nat} {params : Splay.Interface.Parameters}

theorem lookup_rich {n : Nat} (source : State n) {id : Nat} {block : Splay.Interface.Block n}
    (found : source.toInterface.block? id = some block) :
    ∃ richId : Fin source.blocks.length, richId.val = id ∧ (source.blocks.get richId).toInterface = block := by
  have bound : id < source.blocks.length := by
    have lookup : source.toInterface.blocks[id]? = some block := found
    have := (List.getElem?_eq_some_iff.mp lookup).1
    simpa only [State.toInterface, List.length_map] using this
  let richId : Fin source.blocks.length := ⟨id, bound⟩
  exact ⟨richId, rfl, Option.some.inj ((RichSplitBoundary.interface_lookup source richId).symm.trans found)⟩

theorem growing_pivot_covered (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r)
    (id : Fin source.blocks.length) (owner : (source.blocks.get id).owner = JoinRanks.pivot l r)
    (growing : (source.blocks.get id).mode = .growing) :
    id.val = boundary.growingLeft ∨ id.val = boundary.growingRight := by
  obtain ⟨li, liVal, liBlock⟩ := lookup_rich source boundary.growingLeftFound
  obtain ⟨ri, riVal, riBlock⟩ := lookup_rich source boundary.growingRightFound
  have liGrowing : (source.blocks.get li).mode = .growing :=
    (congrArg Splay.Interface.Block.mode liBlock).trans boundary.growingLeftMode
  have riGrowing : (source.blocks.get ri).mode = .growing :=
    (congrArg Splay.Interface.Block.mode riBlock).trans boundary.growingRightMode
  have liOwner : (source.blocks.get li).owner = JoinRanks.pivot l r :=
    ((represented.valid.2 _ (List.get_mem _ li)).2.1 liGrowing).trans
      ((congrArg Splay.Interface.Block.creator liBlock).trans leftCreator)
  have riOwner : (source.blocks.get ri).owner = JoinRanks.pivot l r :=
    ((represented.valid.2 _ (List.get_mem _ ri)).2.1 riGrowing).trans
      ((congrArg Splay.Interface.Block.creator riBlock).trans rightCreator)
  have unique : ∀ i j : Fin source.blocks.length,
      (source.blocks.get i).mode = .growing → (source.blocks.get i).owner = JoinRanks.pivot l r →
      (source.blocks.get j).mode = .growing → (source.blocks.get j).owner = JoinRanks.pivot l r →
      (source.blocks.get i).side = (source.blocks.get j).side → i = j := by
    intro i j ig io jg jo side
    obtain ⟨chosen, _, uniq⟩ := represented.oneGrowingPerSide (JoinRanks.pivot l r) (source.blocks.get i).side
    exact (uniq i ⟨ig, io, rfl⟩).trans (uniq j ⟨jg, jo, side.symm⟩).symm
  have different : (source.blocks.get li).side ≠ (source.blocks.get ri).side := by
    intro same
    have ids := unique li ri liGrowing liOwner riGrowing riOwner same
    have vals := congrArg Fin.val ids
    rw [liVal, riVal] at vals
    exact boundary.growingIdsNe vals.symm
  have covered : (source.blocks.get id).side = (source.blocks.get li).side ∨
      (source.blocks.get id).side = (source.blocks.get ri).side := by
    have twoSides : ∀ a b c : Side, b ≠ c → a = b ∨ a = c := by
      intro a b c
      cases a <;> cases b <;> cases c <;> simp
    exact twoSides _ _ _ different
  rcases covered with same | same
  · exact Or.inl ((congrArg Fin.val (unique id li growing owner liGrowing liOwner same)).trans liVal)
  · exact Or.inr ((congrArg Fin.val (unique id ri growing owner riGrowing riOwner same)).trans riVal)

theorem pivot_record_shrinking (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r)
    (id : Fin source.blocks.length) (owner : (source.blocks.get id).owner = JoinRanks.pivot l r) :
    (boundary.record id.val (source.blocks.get id).toInterface).mode = .shrinking := by
  cases mode : (source.blocks.get id).mode with
  | shrinking =>
      unfold InterfaceForest.SplitBoundary.record
      split_ifs <;> simp_all [Block.toInterface]
  | growing =>
      have covered := growing_pivot_covered left right sl sr source represented boundary leftCreator rightCreator id owner mode
      rcases covered with same | same
      · unfold InterfaceForest.SplitBoundary.record
        rw [← same]
        split_ifs <;> simp_all [Block.toInterface]
      · unfold InterfaceForest.SplitBoundary.record
        rw [← same]
        split_ifs <;> simp_all [Block.toInterface]

theorem pivot_record_empty (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftEq : boundary.left = JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl))
    (rightEq : boundary.right = JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
    (id : Fin source.blocks.length) (owner : (source.blocks.get id).owner = JoinRanks.pivot l r) :
    (boundary.record id.val (source.blocks.get id).toInterface).elements = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x present
  have original := (boundary.record_elements id.val (source.blocks.get id).toInterface).subset present
  have parent := (represented.valid.2 _ (List.get_mem _ id)).parent_eq original
  rw [owner, represented.view_eq] at parent
  have roots := (JoinRootGeometry.priority_parent_pivot_iff left right sl sr x).mp parent
  have globalMem : x ∈ boundary.final.allElements :=
    List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? (boundary.final_lookup id.val _ (RichSplitBoundary.interface_lookup source id)), present⟩
  rw [← leftEq, ← rightEq] at roots
  rcases roots with rfl | rfl
  · exact (boundary.roots_unassigned represented.valid.1).1 globalMem
  · exact (boundary.roots_unassigned represented.valid.1).2 globalMem

end MultiSplay.RichSplit
