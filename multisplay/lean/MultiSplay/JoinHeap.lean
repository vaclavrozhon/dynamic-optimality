import MultiSplay.JoinRanks

/-!
# Exact heap links and gaps retained by a common join

The canonical heap contracts each heavy path to its minimum-rank external
position. Every old internal heap link survives the common join. Only the two
former roots acquire a parent, namely the new pivot. This module proves the
corresponding lookup statements in the actual canonical heap implementation.
-/

namespace MultiSplay.JoinHeap

open Splay.Tree (BST)
open Splay.Rank (External Snapshot)
open Splay.Lazy (HeapView)
open Splay.Lazy.Canonical
open RankEmbedding (external)

/-- The unique incoming-edge implementation returns any certified member
with the selected child, independent of the order of other component records. -/
theorem incoming_of_member {n : Nat} (snapshot : Snapshot n) (source : BST 0 n)
    {edge : Edge n} (member : edge ∈ fullEdges snapshot source) :
    incomingEdge? snapshot source edge.child = some edge := by
  have childMember : edge.child ∈ treeChildren snapshot source le_rfl 0 :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have notRoot : edge.child ≠ canonicalRoot snapshot source :=
    (mem_treeChildren_iff_ne_subtreeOwner snapshot source 0 edge.child).mp childMember
  obtain ⟨chosen, found, chosenMember, childEq⟩ :=
    exists_incomingEdge?_eq_some_of_ne_root snapshot source notRoot
  have noDuplicates := treeChildren_nodup snapshot source le_rfl 0
  have same : chosen = edge := List.inj_on_of_nodup_map noDuplicates chosenMember member childEq
  simpa [same] using found

theorem left_incoming {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize)
    {child : External leftSize} {edge : Edge leftSize}
    (found : incomingEdge? (Snapshot.ofTree left) splayLeft child = some edge) :
    incomingEdge? (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)
        (external 0 (by omega) child) = some (RankEmbedding.edge 0 1 (by omega) edge) := by
  have spec := incomingEdge?_some_mem (Snapshot.ofTree left) splayLeft found
  have member : RankEmbedding.edge 0 1 (by omega) edge ∈
      fullEdges (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight) := by
    rw [JoinRanks.full_edges]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨edge, spec.1, rfl⟩))
  simpa only [RankEmbedding.edge, spec.2] using incoming_of_member _ _ member

theorem right_incoming {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize)
    {child : External rightSize} {edge : Edge rightSize}
    (found : incomingEdge? (Snapshot.ofTree right) splayRight child = some edge) :
    incomingEdge? (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)
        (external (0 + leftSize + 1) (by omega) child) =
      some (RankEmbedding.edge (0 + leftSize + 1) 1 (by omega) edge) := by
  have spec := incomingEdge?_some_mem (Snapshot.ofTree right) splayRight found
  have member : RankEmbedding.edge (0 + leftSize + 1) 1 (by omega) edge ∈
      fullEdges (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight) := by
    rw [JoinRanks.full_edges]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨edge, spec.1, rfl⟩)
  simpa only [RankEmbedding.edge, spec.2] using incoming_of_member _ _ member

theorem left_parent {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize)
    {child owner : External leftSize}
    (parent : canonicalParent (Snapshot.ofTree left) splayLeft child = some owner) :
    canonicalParent (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)
        (external 0 (by omega) child) = some (external 0 (by omega) owner) := by
  simp only [canonicalParent, Option.map_eq_some_iff] at parent
  obtain ⟨edge, found, ownerEq⟩ := parent
  simp only [canonicalParent, left_incoming left right splayLeft splayRight found,
    Option.map_some, RankEmbedding.edge, ownerEq]

theorem right_parent {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize)
    {child owner : External rightSize}
    (parent : canonicalParent (Snapshot.ofTree right) splayRight child = some owner) :
    canonicalParent (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)
        (external (0 + leftSize + 1) (by omega) child) =
      some (external (0 + leftSize + 1) (by omega) owner) := by
  simp only [canonicalParent, Option.map_eq_some_iff] at parent
  obtain ⟨edge, found, ownerEq⟩ := parent
  simp only [canonicalParent, right_incoming left right splayLeft splayRight found,
    Option.map_some, RankEmbedding.edge, ownerEq]

theorem left_rawGap {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize)
    {child : External leftSize} (notRoot : child ≠ canonicalRoot (Snapshot.ofTree left) splayLeft) :
    (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)).rawGap
        (external 0 (by omega) child) =
      (canonicalHeapView (Snapshot.ofTree left) splayLeft).rawGap child := by
  obtain ⟨owner, parent⟩ := exists_canonicalParent_eq_some_of_ne_root (Snapshot.ofTree left) splayLeft notRoot
  have newParent := left_parent left right splayLeft splayRight parent
  simp only [HeapView.rawGap, canonicalHeapView, parent, newParent]
  exact RankEmbedding.gap 0 1 (by omega) (Snapshot.ofTree left)
    (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.left_ranks left right) owner child

theorem right_rawGap {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize)
    {child : External rightSize} (notRoot : child ≠ canonicalRoot (Snapshot.ofTree right) splayRight) :
    (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)).rawGap
        (external (0 + leftSize + 1) (by omega) child) =
      (canonicalHeapView (Snapshot.ofTree right) splayRight).rawGap child := by
  obtain ⟨owner, parent⟩ := exists_canonicalParent_eq_some_of_ne_root (Snapshot.ofTree right) splayRight notRoot
  have newParent := right_parent left right splayLeft splayRight parent
  simp only [HeapView.rawGap, canonicalHeapView, parent, newParent]
  exact RankEmbedding.gap (0 + leftSize + 1) 1 (by omega) (Snapshot.ofTree right)
    (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.right_ranks left right) owner child

theorem left_root_parent {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    canonicalParent (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)
        (external 0 (by omega) (canonicalRoot (Snapshot.ofTree left) splayLeft)) =
      some (JoinRanks.pivot leftSize rightSize) := by
  let rootEdge := edgeFor (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.rootNode splayLeft splayRight) 0 .left
  have member : rootEdge ∈ fullEdges (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight) := by
    rw [JoinRanks.full_edges]
    exact List.mem_append_left _ (List.mem_append_left _ (by simp [rootEdge]))
  have found := incoming_of_member _ _ member
  have childEq : rootEdge.child = external 0 (by omega) (canonicalRoot (Snapshot.ofTree left) splayLeft) :=
    JoinRanks.root_left_child left right splayLeft splayRight
  have ownerEq : rootEdge.owner = JoinRanks.pivot leftSize rightSize :=
    JoinRanks.root_owner left right splayLeft splayRight
  rw [childEq] at found
  simp only [canonicalParent, found, Option.map_some, ownerEq]

theorem right_root_parent {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    canonicalParent (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)
        (external (0 + leftSize + 1) (by omega) (canonicalRoot (Snapshot.ofTree right) splayRight)) =
      some (JoinRanks.pivot leftSize rightSize) := by
  let rootEdge := edgeFor (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.rootNode splayLeft splayRight) 0 .right
  have member : rootEdge ∈ fullEdges (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight) := by
    rw [JoinRanks.full_edges]
    exact List.mem_append_left _ (List.mem_append_left _ (by simp [rootEdge]))
  have found := incoming_of_member _ _ member
  have childEq : rootEdge.child = external (0 + leftSize + 1) (by omega) (canonicalRoot (Snapshot.ofTree right) splayRight) :=
    JoinRanks.root_right_child left right splayLeft splayRight
  have ownerEq : rootEdge.owner = JoinRanks.pivot leftSize rightSize :=
    JoinRanks.root_owner left right splayLeft splayRight
  rw [childEq] at found
  simp only [canonicalParent, found, Option.map_some, ownerEq]

theorem left_root_rawGap {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)).rawGap
        (external 0 (by omega) (canonicalRoot (Snapshot.ofTree left) splayLeft)) = 1 := by
  simp only [HeapView.rawGap, canonicalHeapView, left_root_parent left right splayLeft splayRight]
  exact JoinRanks.left_root_gap left right splayLeft

theorem right_root_rawGap {leftSize rightSize : Nat}
    (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)).rawGap
        (external (0 + leftSize + 1) (by omega) (canonicalRoot (Snapshot.ofTree right) splayRight)) = 1 := by
  simp only [HeapView.rawGap, canonicalHeapView, right_root_parent left right splayLeft splayRight]
  exact JoinRanks.right_root_gap left right splayRight

end MultiSplay.JoinHeap
