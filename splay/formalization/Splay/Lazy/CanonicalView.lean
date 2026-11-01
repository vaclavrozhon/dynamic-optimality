import Splay.Lazy.Canonical

namespace Splay.Lazy.Canonical

open Splay.Rank

/--
Canonical light edges of a full splay-tree shape, selected by comparison-tree
ranks and rooted at depth zero.
-/
noncomputable def fullEdges {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) : List (Edge n) :=
  treeEdges snapshot tree (Nat.le_refl n) 0

@[simp]
theorem length_fullEdges {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) :
    (fullEdges snapshot tree).length = 2 * n := by
  simp [fullEdges]

@[simp]
theorem fullEdges_nodup {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) :
    (fullEdges snapshot tree).Nodup := by
  simpa only [fullEdges] using
    treeEdges_nodup snapshot tree (Nat.le_refl n) 0

/-- The unique heavy-path vertex with no incoming canonical light edge. -/
noncomputable def canonicalRoot {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) : External n :=
  subtreeOwner snapshot tree (Nat.le_refl n)

/-- The canonical root has the snapshot's global minimum rank zero. -/
@[simp]
theorem rank_canonicalRoot_eq_zero {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) :
    snapshot.rank (canonicalRoot snapshot tree) = 0 := by
  obtain ⟨zero, hZero⟩ := snapshot.hasZero
  have hInside :
      subtreeLower tree (Nat.le_refl n) ≤ zero ∧
        zero ≤ subtreeUpper tree (Nat.le_refl n) := by
    constructor
    · simp [subtreeLower]
    · have hLt := zero.isLt
      change zero.val ≤ 2 * n
      change zero.val < 2 * n + 1 at hLt
      omega
  have hRootLe :=
    (subtreeOwner_isMin snapshot tree (Nat.le_refl n)).2.2
      zero hInside.1 hInside.2
  rw [hZero] at hRootLe
  simpa only [canonicalRoot] using Nat.eq_zero_of_le_zero hRootLe

/--
Every non-root external vertex is the child endpoint of a unique canonical
light edge.
-/
theorem existsUnique_fullEdge_child_of_ne_root {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) (child : External n)
    (notRoot : child ≠ canonicalRoot snapshot tree) :
    ∃! edge : Edge n,
      edge ∈ fullEdges snapshot tree ∧ edge.child = child := by
  have childMem :
      child ∈ treeChildren snapshot tree (Nat.le_refl n) 0 := by
    apply
      (mem_treeChildren_iff_ne_subtreeOwner snapshot tree 0 child).2
    simpa only [canonicalRoot] using notRoot
  have childMem' :
      child ∈ (fullEdges snapshot tree).map Edge.child := by
    simpa only [treeChildren, fullEdges] using childMem
  obtain ⟨edge, edgeMem, edgeChild⟩ := List.mem_map.mp childMem'
  refine ⟨edge, ⟨edgeMem, edgeChild⟩, ?_⟩
  intro other otherSpec
  have childrenNodup :
      ((fullEdges snapshot tree).map Edge.child).Nodup := by
    simpa only [treeChildren, fullEdges] using
      treeChildren_nodup snapshot tree (Nat.le_refl n) 0
  exact List.inj_on_of_nodup_map childrenNodup
    otherSpec.1 edgeMem (otherSpec.2.trans edgeChild.symm)

/--
The unique incoming canonical edge, with `none` reserved for the canonical
root.
-/
noncomputable def incomingEdge? {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (child : External n) : Option (Edge n) :=
  if notRoot : child ≠ canonicalRoot snapshot tree then
    some
      (Classical.choose
        (existsUnique_fullEdge_child_of_ne_root
          snapshot tree child notRoot))
  else
    none

/-- A successful incoming-edge lookup returns an edge from the full list. -/
theorem incomingEdge?_some_mem {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    {child : External n} {edge : Edge n}
    (lookup : incomingEdge? snapshot tree child = some edge) :
    edge ∈ fullEdges snapshot tree ∧ edge.child = child := by
  classical
  unfold incomingEdge? at lookup
  split at lookup
  next notRoot =>
    have chosenSpec :=
      (Classical.choose_spec
        (existsUnique_fullEdge_child_of_ne_root
          snapshot tree child notRoot)).1
    have chosenEq : Classical.choose
          (existsUnique_fullEdge_child_of_ne_root
            snapshot tree child notRoot) = edge :=
      Option.some.inj lookup
    simpa only [chosenEq] using chosenSpec
  next isRoot =>
    simp at lookup

/-- Every non-root vertex has a successful incoming-edge lookup. -/
theorem exists_incomingEdge?_eq_some_of_ne_root {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    {child : External n} (notRoot : child ≠ canonicalRoot snapshot tree) :
    ∃ edge,
      incomingEdge? snapshot tree child = some edge ∧
        edge ∈ fullEdges snapshot tree ∧ edge.child = child := by
  classical
  let edge :=
    Classical.choose
      (existsUnique_fullEdge_child_of_ne_root
        snapshot tree child notRoot)
  have edgeSpec :
      edge ∈ fullEdges snapshot tree ∧ edge.child = child :=
    (Classical.choose_spec
      (existsUnique_fullEdge_child_of_ne_root
        snapshot tree child notRoot)).1
  refine ⟨edge, ?_, edgeSpec⟩
  simp only [incomingEdge?, dif_pos notRoot, edge]

/-- The canonical root has no incoming edge. -/
@[simp]
theorem incomingEdge?_canonicalRoot {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    incomingEdge? snapshot tree (canonicalRoot snapshot tree) = none := by
  simp [incomingEdge?]

/-- The incoming-edge lookup fails exactly at the canonical root. -/
theorem incomingEdge?_eq_none_iff {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (child : External n) :
    incomingEdge? snapshot tree child = none ↔
      child = canonicalRoot snapshot tree := by
  classical
  unfold incomingEdge?
  by_cases notRoot : child ≠ canonicalRoot snapshot tree
  · simp [notRoot]
  · have isRoot : child = canonicalRoot snapshot tree :=
      Classical.not_not.mp notRoot
    simp [isRoot]

/-- Canonical heap parent obtained from the owner endpoint of the incoming edge. -/
noncomputable def canonicalParent {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (child : External n) : Option (External n) :=
  (incomingEdge? snapshot tree child).map Edge.owner

/-- The canonical root has no heap parent. -/
@[simp]
theorem canonicalParent_canonicalRoot {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    canonicalParent snapshot tree (canonicalRoot snapshot tree) = none := by
  simp [canonicalParent]

/-- Parent lookup fails exactly at the canonical root. -/
theorem canonicalParent_eq_none_iff {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (child : External n) :
    canonicalParent snapshot tree child = none ↔
      child = canonicalRoot snapshot tree := by
  simp [canonicalParent, incomingEdge?_eq_none_iff]

/-- Every non-root vertex has a canonical heap parent. -/
theorem exists_canonicalParent_eq_some_of_ne_root {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    {child : External n} (notRoot : child ≠ canonicalRoot snapshot tree) :
    ∃ owner, canonicalParent snapshot tree child = some owner := by
  obtain ⟨edge, lookup, _, _⟩ :=
    exists_incomingEdge?_eq_some_of_ne_root
      snapshot tree notRoot
  exact ⟨edge.owner, by simp [canonicalParent, lookup]⟩

/-- Every canonical parent has strictly smaller snapshot rank than its child. -/
theorem rank_canonicalParent_lt {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    {child owner : External n}
    (parent : canonicalParent snapshot tree child = some owner) :
    snapshot.rank owner < snapshot.rank child := by
  simp only [canonicalParent, Option.map_eq_some_iff] at parent
  obtain ⟨edge, lookup, ownerEq⟩ := parent
  have edgeSpec := incomingEdge?_some_mem snapshot tree lookup
  have rankLt :=
    mem_treeEdges_rank_lt snapshot tree (Nat.le_refl n)
      (show edge ∈ treeEdges snapshot tree (Nat.le_refl n) 0 by
        simpa only [fullEdges] using edgeSpec.1)
  simpa only [ownerEq, edgeSpec.2] using rankLt

end Splay.Lazy.Canonical
