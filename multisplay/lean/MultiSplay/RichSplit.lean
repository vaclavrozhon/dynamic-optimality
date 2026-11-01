import MultiSplay.RichSplitBoundary
import MultiSplay.RichRestrictionStable
import MultiSplay.JoinComponentGeometry

/-!
# The two stable histories produced by a common split

These histories are restricted from the actual input, including all prior
passes and shrinking records. Their original block IDs survive the strict
split trace. The only neutralized values are the two new component roots.
-/

namespace MultiSplay.RichSplit

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element)
open Splay.Lazy.Canonical
open JoinIntervals (leftEmbedding rightEmbedding)

variable {l r : Nat} {params : Splay.Interface.Parameters}

noncomputable def leftEmbedding (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    RichRestriction.Embedding (canonicalHeapView (Snapshot.ofTree left).withTruePriority sl) source.view where
  element := JoinIntervals.leftEmbedding l r
  injective := RankEmbedding.external_injective _ _
  children := by intro owner side; rw [represented.view_eq]; exact (JoinComponentGeometry.left left right sl sr).children owner side
  gap := by intro x notRoot; rw [represented.view_eq]; exact JoinPriority.left_rawGap left right sl sr notRoot

noncomputable def rightEmbedding (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    RichRestriction.Embedding (canonicalHeapView (Snapshot.ofTree right).withTruePriority sr) source.view where
  element := JoinIntervals.rightEmbedding l r
  injective := RankEmbedding.external_injective _ _
  children := by intro owner side; rw [represented.view_eq]; exact (JoinComponentGeometry.right left right sl sr).children owner side
  gap := by intro x notRoot; rw [represented.view_eq]; exact JoinPriority.right_rawGap left right sl sr notRoot

noncomputable def leftState (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) : State l :=
  RichRestriction.state source _ (leftEmbedding left right sl sr source represented)

noncomputable def rightState (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) : State r :=
  RichRestriction.state source _ (rightEmbedding left right sl sr source represented)

theorem left_represents (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    (leftState left right sl sr source represented).Represents params (Snapshot.ofTree left).withTruePriority sl :=
  ⟨RichRestriction.stable source _ _ represented.stable (canonicalHeapView_heapOrdered _ _), rfl⟩

theorem right_represents (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    (rightState left right sl sr source represented).Represents params (Snapshot.ofTree right).withTruePriority sr :=
  ⟨RichRestriction.stable source _ _ represented.stable (canonicalHeapView_heapOrdered _ _), rfl⟩

/-- The strict split modifies no record owned inside either surviving component. -/
theorem retained_lookup (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftEq : boundary.left = JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl))
    (rightEq : boundary.right = JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r)
    (id : Fin source.blocks.length) (outside : (source.blocks.get id).owner ≠ JoinRanks.pivot l r) :
    boundary.final.block? id.val = some (source.blocks.get id).toInterface := by
  have found := RichSplitBoundary.interface_lookup source id
  have notGrowing : ∀ target block, source.toInterface.block? target = some block → block.mode = .growing →
      block.creator = JoinRanks.pivot l r → id.val ≠ target := by
    intro target block lookup growing creator same
    have eq : (source.blocks.get id).toInterface = block := Option.some.inj (found.symm.trans (same ▸ lookup))
    have oldGrowing : (source.blocks.get id).mode = .growing := (congrArg Splay.Interface.Block.mode eq).trans growing
    have oldCreator : (source.blocks.get id).creator = JoinRanks.pivot l r := (congrArg Splay.Interface.Block.creator eq).trans creator
    exact outside (((represented.valid.2 _ (List.get_mem _ id)).2.1 oldGrowing).trans oldCreator)
  have notSource : ∀ target block child, source.toInterface.block? target = some block → block.elements = [child] →
      source.view.parent child = some (JoinRanks.pivot l r) → id.val ≠ target := by
    intro target block child lookup singleton parent same
    have eq : (source.blocks.get id).toInterface = block := Option.some.inj (found.symm.trans (same ▸ lookup))
    have payload : (source.blocks.get id).elements = [child] := (congrArg Splay.Interface.Block.elements eq).trans singleton
    have oldParent := (represented.valid.2 _ (List.get_mem _ id)).parent_eq (show child ∈ (source.blocks.get id).elements by rw [payload]; simp)
    exact outside (Option.some.inj (oldParent.symm.trans parent))
  apply boundary.retained_lookup _ _ found
  · exact notGrowing _ _ boundary.growingLeftFound boundary.growingLeftMode leftCreator
  · exact notGrowing _ _ boundary.growingRightFound boundary.growingRightMode rightCreator
  · apply notSource _ _ _ boundary.sourceLeftFound boundary.sourceLeftSingleton
    rw [represented.view_eq]
    apply (JoinRootGeometry.priority_parent_pivot_iff left right sl sr boundary.left).mpr
    exact Or.inl leftEq
  · apply notSource _ _ _ boundary.sourceRightFound boundary.sourceRightSingleton
    rw [represented.view_eq]
    apply (JoinRootGeometry.priority_parent_pivot_iff left right sl sr boundary.right).mpr
    exact Or.inr rightEq

end MultiSplay.RichSplit
