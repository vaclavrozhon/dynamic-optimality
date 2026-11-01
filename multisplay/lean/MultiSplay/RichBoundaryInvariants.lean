import MultiSplay.UnbrokenEmbedding
import MultiSplay.RichSplit
import MultiSplay.RichJoinStable
import Splay.Interface.PassCountHistory

/-!
# Persistent splay invariants at common forest boundaries

Restriction keeps the actual pass counters and all selected intervals. Joining
adds only two never-passed growing intervals. The full cross-side unbrokenness
invariant, as well as zero pass counts on growing blocks, therefore survives
both operations without reinitializing any component history.
-/

namespace MultiSplay

open Splay.Rank (Snapshot)
open Splay.Lazy (State Block)
open Splay.Lazy.Canonical
open Splay.Accounting

variable {n m l r : Nat} {params : Splay.Interface.Parameters}

theorem rich_growing_zero_iff (state : State n) :
    Splay.Interface.GrowingPassCountZero state.toInterface ↔
      ∀ block ∈ state.blocks, block.mode = .growing → block.passCount = 0 := by
  constructor
  · intro zero block member growing
    obtain ⟨id, eq⟩ := List.mem_iff_get.mp member
    exact zero id.val block.toInterface (by simpa only [eq] using RichSplitBoundary.interface_lookup state id) growing
  · intro zero id block found growing
    have member : block ∈ state.toInterface.blocks := List.mem_of_getElem? found
    obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp member
    exact zero original originalMem growing

theorem RichRestriction.growing_zero (source : State m) (small : Splay.Lazy.HeapView n)
    (embedding : RichRestriction.Embedding small source.view)
    (zero : Splay.Interface.GrowingPassCountZero source.toInterface) :
    Splay.Interface.GrowingPassCountZero (RichRestriction.state source small embedding).toInterface := by
  rw [rich_growing_zero_iff] at zero ⊢
  intro block member growing
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp member
  exact zero _ (List.get_mem _ id) growing

theorem RichRestriction.unbroken (offset depth : Nat) (fits : offset+n ≤ m)
    (before : Snapshot n) (after : Snapshot m) (small : Splay.Tree.BST 0 n) (big : Splay.Tree.BST 0 m)
    (source : State m) (represented : source.Represents params after big)
    (embedding : RichRestriction.Embedding (canonicalHeapView before small) source.view)
    (elementEq : embedding.element = RankEmbedding.external offset fits)
    (edges : ∀ x edge, incomingEdge? before small x = some edge →
      incomingEdge? after big (RankEmbedding.external offset fits x) = some (RankEmbedding.edge offset depth fits edge))
    (unbroken : PassedBlocksUnbroken after big source) :
    PassedBlocksUnbroken before small (RichRestriction.state source _ embedding) := by
  intro block member positive
  obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
  have inside := (RichRestriction.mem_ids source embedding id).mp idMem
  have oldMem := List.get_mem source.blocks id
  have old := unbroken _ oldMem positive
  have localMem : BlockEmbedding.block embedding.project (source.blocks.get id) ∈
      (RichRestriction.state source _ embedding).blocks := List.mem_map.mpr ⟨id, idMem, rfl⟩
  have localValid := (RichRestriction.valid source _ embedding represented.stable).2 _ localMem
  apply (UnbrokenEmbedding.iff_unbroken offset depth fits before after small big (fun owner side => ?_)
    edges _ _ localValid).mp
  · have ownerEq := embedding.element_project inside
    have elementsEq := RichRestriction.old_elements_map source _ embedding represented.stable _ oldMem inside
    rw [elementEq] at ownerEq elementsEq
    simpa only [canonicalBlockCrossSideUnbroken, BlockEmbedding.block, ownerEq, elementsEq] using old
  · rw [← elementEq, ← represented.view_eq]
    exact embedding.children owner side

theorem RichJoin.unbroken (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr)
    (aUnbroken : PassedBlocksUnbroken (Snapshot.ofTree left).withTruePriority sl a)
    (bUnbroken : PassedBlocksUnbroken (Snapshot.ofTree right).withTruePriority sr b) :
    PassedBlocksUnbroken (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)
      (RichJoin.state left right sl sr a b) := by
  intro block member positive
  change block ∈ _ ++ _ ++ _ at member
  rcases List.mem_append.mp member with old | fresh
  · rcases List.mem_append.mp old with oldLeft | oldRight
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldLeft
      have valid := aRep.valid.2 original originalMem
      rw [aRep.view_eq] at valid
      exact (UnbrokenEmbedding.iff_unbroken 0 1 (by omega) _ _ sl (JoinRanks.tree sl sr)
        (JoinComponentGeometry.left left right sl sr).children (fun _ _ found => JoinAttachment.left_incoming left right sl sr found)
        original a.allElements valid).mpr (aUnbroken original originalMem positive)
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldRight
      have valid := bRep.valid.2 original originalMem
      rw [bRep.view_eq] at valid
      exact (UnbrokenEmbedding.iff_unbroken (0+l+1) 1 (by omega) _ _ sr (JoinRanks.tree sl sr)
        (JoinComponentGeometry.right left right sl sr).children (fun _ _ found => JoinAttachment.right_incoming left right sl sr found)
        original b.allElements valid).mpr (bUnbroken original originalMem positive)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl <;> exact False.elim (positive rfl)

theorem RichJoin.growing_zero (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) (a : State l) (b : State r)
    (aZero : Splay.Interface.GrowingPassCountZero a.toInterface)
    (bZero : Splay.Interface.GrowingPassCountZero b.toInterface) :
    Splay.Interface.GrowingPassCountZero (RichJoin.state left right sl sr a b).toInterface := by
  rw [rich_growing_zero_iff] at aZero bZero ⊢
  intro block member growing
  change block ∈ _ ++ _ ++ _ at member
  rcases List.mem_append.mp member with old | fresh
  · rcases List.mem_append.mp old with oldLeft | oldRight
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldLeft
      exact aZero original originalMem growing
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldRight
      exact bZero original originalMem growing
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl <;> rfl

theorem RichSplit.left_unbroken (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr) source) :
    PassedBlocksUnbroken (Snapshot.ofTree left).withTruePriority sl (RichSplit.leftState left right sl sr source represented) :=
  RichRestriction.unbroken 0 1 (by omega) _ _ _ _ source represented _ rfl
    (fun _ _ found => JoinAttachment.left_incoming left right sl sr found) unbroken

theorem RichSplit.right_unbroken (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr) source) :
    PassedBlocksUnbroken (Snapshot.ofTree right).withTruePriority sr (RichSplit.rightState left right sl sr source represented) :=
  RichRestriction.unbroken (0+l+1) 1 (by omega) _ _ _ _ source represented _ rfl
    (fun _ _ found => JoinAttachment.right_incoming left right sl sr found) unbroken

end MultiSplay
