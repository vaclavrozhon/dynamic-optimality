import Splay.Accounting.CanonicalSubtreeUnbroken
import Splay.Accounting.RootHeavyPathBoundaryDecomposition
import Splay.Tree.SplaySubtreePersistence

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical

/-- Every nonempty child family of a non-accessed owner lies entirely in
one literal subtree off the search path. -/
theorem exists_offpath_subtree_for_owner {n lower upper : ℕ}
    (snapshot : Snapshot n) (tree : BST lower upper) (bound : upper ≤ n) (depth : ℕ)
    (key : Fin n) (insideLower : lower ≤ key.val) (insideUpper : key.val < upper)
    (rankZero : snapshot.rank (valuePos key) = 0) (owner : External n)
    (nonempty : ∃ edge ∈ treeEdges snapshot tree bound depth, edge.owner = owner)
    (other : owner ≠ valuePos key) :
    ∃ (innerLower innerUpper : ℕ) (inner : BST innerLower innerUpper) (level : ℕ) (occurrence : SubtreeAt inner level tree),
      (key.val < innerLower ∨ innerUpper ≤ key.val) ∧
        ∀ edge ∈ treeEdges snapshot tree bound depth, edge.owner = owner →
          edge ∈ treeEdges snapshot inner (occurrence.bounds.2.trans bound) (depth + level) := by
  induction tree generalizing depth with
  | empty => omega
  | @node lower root upper left right ihLeft ihRight =>
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      let node : AtNode n := ⟨lower, root, upper, left, right, bound⟩
      have rootOwner : node.owner snapshot = valuePos key :=
        atNode_owner_eq_accessed snapshot node key.val insideLower insideUpper key.isLt rankZero
      have notLocal : ∀ edge ∈ edgesAtNode snapshot node depth, edge.owner = owner → False := by
        intro edge member ownerEq
        exact other (ownerEq.symm.trans ((mem_edgesAtNode_valid snapshot node depth member).2.1.trans rootOwner))
      obtain ⟨witness, witnessMember, witnessOwner⟩ := nonempty
      have location : witness ∈ treeEdges snapshot left leftBound (depth + 1) ∨
          witness ∈ treeEdges snapshot right bound (depth + 1) := by
        rcases List.mem_append.mp witnessMember with localOrLeft | inRight
        · rcases List.mem_append.mp localOrLeft with localEdge | inLeft
          · exact (notLocal witness localEdge witnessOwner).elim
          · exact Or.inl inLeft
        · exact Or.inr inRight
      rcases location with onLeft | onRight
      · have witnessHigh : owner.val ≤ 2 * root := by
          rw [← witnessOwner]
          exact (mem_treeEdges_inside snapshot left leftBound onLeft).2.1
        have allLeft : ∀ edge ∈ treeEdges snapshot (.node left right) bound depth, edge.owner = owner →
            edge ∈ treeEdges snapshot left leftBound (depth + 1) := by
          intro edge member ownerEq
          rcases List.mem_append.mp member with localOrLeft | inRight
          · rcases List.mem_append.mp localOrLeft with localEdge | inLeft
            · exact (notLocal edge localEdge ownerEq).elim
            · exact inLeft
          · have low : 2 * (root + 1) ≤ edge.owner.val := (mem_treeEdges_inside snapshot right bound inRight).1
            rw [ownerEq] at low
            omega
        by_cases keyLeft : key.val < root
        · obtain ⟨innerLower, innerUpper, inner, level, occurrence, outside, allInside⟩ :=
            ihLeft leftBound (depth + 1) insideLower keyLeft ⟨witness, onLeft, witnessOwner⟩
          refine ⟨innerLower, innerUpper, inner, level + 1, occurrence.left right, outside, ?_⟩
          intro edge member ownerEq
          have result := allInside edge (allLeft edge member ownerEq) ownerEq
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
        · exact ⟨lower, root, left, 1, SubtreeAt.left .here right, Or.inr (by omega), allLeft⟩
      · have witnessLow : 2 * (root + 1) ≤ owner.val := by
          rw [← witnessOwner]
          exact (mem_treeEdges_inside snapshot right bound onRight).1
        have allRight : ∀ edge ∈ treeEdges snapshot (.node left right) bound depth, edge.owner = owner →
            edge ∈ treeEdges snapshot right bound (depth + 1) := by
          intro edge member ownerEq
          rcases List.mem_append.mp member with localOrLeft | inRight
          · rcases List.mem_append.mp localOrLeft with localEdge | inLeft
            · exact (notLocal edge localEdge ownerEq).elim
            · have high : edge.owner.val ≤ 2 * root := (mem_treeEdges_inside snapshot left leftBound inLeft).2.1
              rw [ownerEq] at high
              omega
          · exact inRight
        by_cases keyRight : root < key.val
        · obtain ⟨innerLower, innerUpper, inner, level, occurrence, outside, allInside⟩ :=
            ihRight bound (depth + 1) (by omega) insideUpper ⟨witness, onRight, witnessOwner⟩
          refine ⟨innerLower, innerUpper, inner, level + 1, SubtreeAt.right left occurrence, outside, ?_⟩
          intro edge member ownerEq
          have result := allInside edge (allRight edge member ownerEq) ownerEq
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
        · exact ⟨root + 1, upper, right, 1, SubtreeAt.right left .here, Or.inl (by omega), allRight⟩

/-- Splaying a different owner preserves a shrinking interval's unbroken
geometry: its whole old child family lies inside one untouched subtree. -/
theorem canonicalBlockCrossSideUnbroken_after_splay_of_owner_ne
    {n : ℕ} (snapshot : Snapshot n) (key : Fin n) {before after : BST 0 n}
    (execution : SplayExecution key.val before after) (rankZero : snapshot.rank (valuePos key) = 0)
    (block : Block n) (other : block.owner ≠ valuePos key)
    (parents : ∀ element ∈ block.elements, canonicalParent snapshot before element = some block.owner)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before block) :
    canonicalBlockCrossSideUnbroken snapshot after block := by
  by_cases empty : block.elements = []
  · exact canonicalBlockCrossSideUnbroken_of_elements_nil snapshot after block empty
  obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil block.elements empty
  obtain ⟨firstEdge, firstLookup, firstOwner⟩ := Option.map_eq_some_iff.mp (parents first firstMember)
  have firstSpec := incomingEdge?_some_mem snapshot before firstLookup
  obtain ⟨innerLower, innerUpper, inner, oldDepth, oldOccurrence, outside, allInside⟩ :=
    exists_offpath_subtree_for_owner snapshot before (Nat.le_refl n) 0 key (Nat.zero_le _) key.isLt rankZero
      block.owner ⟨firstEdge, firstSpec.1, firstOwner⟩ other
  obtain ⟨newDepth, newOccurrence⟩ := execution.preserves_subtree oldOccurrence outside
  apply canonicalBlockCrossSideUnbroken_of_shared_subtree snapshot oldOccurrence newOccurrence block unbroken
  intro element inside
  obtain ⟨edge, lookup, owner⟩ := Option.map_eq_some_iff.mp (parents element inside)
  have spec := incomingEdge?_some_mem snapshot before lookup
  have inCore := allInside edge spec.1 owner
  rw [treeEdges_shift_depth] at inCore
  obtain ⟨localEdge, localMember, equal⟩ := List.mem_map.mp inCore
  exact ⟨localEdge, localMember, (congrArg Edge.child equal).trans spec.2, (congrArg Edge.owner equal).trans owner⟩

end Splay.Accounting
