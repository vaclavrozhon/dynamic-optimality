import Splay.Accounting.JunctionEdgeCorrespondence
import Splay.Accounting.CanonicalCrossSideUnbroken

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical

/-- Membership in the canonical edge enumeration determines the exact lookup,
including its attachment data rather than only its heap-parent projection. -/
theorem incomingEdge_eq_some_of_mem_fullEdges {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {edge : Edge n} (member : edge ∈ fullEdges snapshot tree) :
    incomingEdge? snapshot tree edge.child = some edge := by
  have parent := canonicalParent_eq_some_of_mem_fullEdges snapshot tree edge member
  have notRoot : edge.child ≠ canonicalRoot snapshot tree := by
    intro equal
    rw [equal, canonicalParent_canonicalRoot] at parent
    contradiction
  obtain ⟨incoming, lookup, incomingMember, incomingChild⟩ :=
    exists_incomingEdge?_eq_some_of_ne_root snapshot tree notRoot
  obtain ⟨selected, selectedSpec, unique⟩ := existsUnique_fullEdge_child_of_ne_root snapshot tree edge.child notRoot
  have equal := (unique incoming ⟨incomingMember, incomingChild⟩).trans (unique edge ⟨member, rfl⟩).symm
  simpa only [equal] using lookup

namespace JunctionBendReduction

/-- Ordinary children retain their relative order in the full, cross-side
attachment order through a change of priorities. -/
theorem childStrictlyAbove_of_not_mem_junctionVertices {n : ℕ} (before after : Snapshot n) (tree : BST 0 n)
    {first second : Element n}
    (firstOrdinary : first ∉ junctionVerticesFrom before after tree (Nat.le_refl n))
    (secondOrdinary : second ∉ junctionVerticesFrom before after tree (Nat.le_refl n))
    (above : ChildStrictlyAbove before tree first second) : ChildStrictlyAbove after tree first second := by
  obtain ⟨firstEdge, secondEdge, firstLookup, secondLookup, ordered⟩ := above
  have firstOld := incomingEdge?_some_mem before tree firstLookup
  have secondOld := incomingEdge?_some_mem before tree secondLookup
  obtain ⟨firstNew, firstMember, firstChild, firstBranch, firstKey, firstDepth⟩ :=
    exists_edge_same_attachment_of_not_mem_junctionVertices before after tree (Nat.le_refl n) 0
      firstOld.1 (by simpa only [firstOld.2] using firstOrdinary)
  obtain ⟨secondNew, secondMember, secondChild, secondBranch, secondKey, secondDepth⟩ :=
    exists_edge_same_attachment_of_not_mem_junctionVertices before after tree (Nat.le_refl n) 0
      secondOld.1 (by simpa only [secondOld.2] using secondOrdinary)
  refine ⟨firstNew, secondNew, ?_, ?_, ?_⟩
  · have lookup := incomingEdge_eq_some_of_mem_fullEdges after tree firstMember
    simpa only [firstChild, firstOld.2] using lookup
  · have lookup := incomingEdge_eq_some_of_mem_fullEdges after tree secondMember
    simpa only [secondChild, secondOld.2] using lookup
  · simpa only [edgeStrictlyAbove, firstDepth, secondDepth, firstBranch, secondBranch] using ordered

theorem childStrictlyAbove_iff_of_not_mem_junctionVertices {n : ℕ} (before after : Snapshot n) (tree : BST 0 n)
    {first second : Element n}
    (firstOrdinary : first ∉ junctionVerticesFrom before after tree (Nat.le_refl n))
    (secondOrdinary : second ∉ junctionVerticesFrom before after tree (Nat.le_refl n)) :
    ChildStrictlyAbove before tree first second ↔ ChildStrictlyAbove after tree first second := by
  constructor
  · exact childStrictlyAbove_of_not_mem_junctionVertices before after tree firstOrdinary secondOrdinary
  · exact childStrictlyAbove_of_not_mem_junctionVertices after before tree
      (by simpa only [junctionVerticesFrom_comm after before] using firstOrdinary)
      (by simpa only [junctionVerticesFrom_comm after before] using secondOrdinary)

theorem childBetween_iff_of_not_mem_junctionVertices {n : ℕ} (before after : Snapshot n) (tree : BST 0 n)
    {first middle last : Element n}
    (firstOrdinary : first ∉ junctionVerticesFrom before after tree (Nat.le_refl n))
    (middleOrdinary : middle ∉ junctionVerticesFrom before after tree (Nat.le_refl n))
    (lastOrdinary : last ∉ junctionVerticesFrom before after tree (Nat.le_refl n)) :
    ChildBetween before tree first middle last ↔ ChildBetween after tree first middle last := by
  unfold ChildBetween
  rw [childStrictlyAbove_iff_of_not_mem_junctionVertices before after tree firstOrdinary middleOrdinary,
    childStrictlyAbove_iff_of_not_mem_junctionVertices before after tree middleOrdinary lastOrdinary,
    childStrictlyAbove_iff_of_not_mem_junctionVertices before after tree lastOrdinary middleOrdinary,
    childStrictlyAbove_iff_of_not_mem_junctionVertices before after tree middleOrdinary firstOrdinary]

end JunctionBendReduction
end Splay.Accounting
