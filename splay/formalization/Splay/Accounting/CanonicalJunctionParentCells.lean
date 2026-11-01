import Splay.Accounting.JunctionCutOwnerUniformity
import Splay.Accounting.JunctionExceptionalChildren

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy.Canonical

theorem exists_edge_of_canonicalParent {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {child owner : External n} (parent : canonicalParent snapshot tree child = some owner) :
    ∃ edge ∈ fullEdges snapshot tree, edge.owner = owner ∧ edge.child = child := by
  simp only [canonicalParent, Option.map_eq_some_iff] at parent
  obtain ⟨edge, found, ownerEq⟩ := parent
  have source := incomingEdge?_some_mem snapshot tree found
  exact ⟨edge, source.1, ownerEq, source.2⟩

theorem canonicalSide_eq_edge_side {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {edge : Edge n} (member : edge ∈ fullEdges snapshot tree) :
    canonicalSide snapshot tree edge.child = edge.side := by
  have parent := canonicalParent_eq_some_of_mem_fullEdges snapshot tree edge member
  have canonicalOrder := canonicalSide_order snapshot tree parent
  have edgeOrder := mem_treeEdges_side_order snapshot tree (Nat.le_refl n) member
  cases actualSide : canonicalSide snapshot tree edge.child <;> cases edgeSide : edge.side <;>
    simp only [actualSide, edgeSide] at canonicalOrder edgeOrder ⊢ <;> omega

/-- Ordinary children retain their side in the actual canonical heap maps. -/
theorem canonicalSide_eq_of_not_mem_junctionExceptions {n : ℕ} (before after : Snapshot n) (tree : BST 0 n)
    {child owner : External n} (parent : canonicalParent before tree child = some owner)
    (ordinary : child ∉ junctionExceptionsFrom before after tree (Nat.le_refl n)) :
    canonicalSide after tree child = canonicalSide before tree child := by
  obtain ⟨old, oldMember, _, childEq⟩ := exists_edge_of_canonicalParent before tree parent
  obtain ⟨next, nextMember, nextChild, _, _, _, side⟩ :=
    exists_edge_same_attachment_side_of_not_mem_exceptions before after tree (Nat.le_refl n) 0 oldMember
      (by simpa only [childEq] using ordinary)
  have oldSide := canonicalSide_eq_edge_side before tree oldMember
  have nextSide := canonicalSide_eq_edge_side after tree nextMember
  rw [nextChild, childEq] at nextSide
  rw [childEq] at oldSide
  exact nextSide.trans (side.trans oldSide.symm)

/-- Two ordinary siblings in the same numerical junction cell have the
same new canonical parent. The correspondence witnesses are constructed
from the two actual snapshots. -/
theorem canonicalParents_eq_of_sameCutCell {n : ℕ} (before after : Snapshot n) (tree : BST 0 n)
    {first second owner : External n}
    (firstParent : canonicalParent before tree first = some owner)
    (secondParent : canonicalParent before tree second = some owner)
    (firstOrdinary : first ∉ junctionExceptionsFrom before after tree (Nat.le_refl n))
    (secondOrdinary : second ∉ junctionExceptionsFrom before after tree (Nat.le_refl n))
    (sameCell : SameCutCell (junctionCutsFrom before after tree (Nat.le_refl n)) first second) :
    canonicalParent after tree first = canonicalParent after tree second := by
  obtain ⟨firstEdge, firstMember, firstOwner, firstChild⟩ := exists_edge_of_canonicalParent before tree firstParent
  obtain ⟨secondEdge, secondMember, secondOwner, secondChild⟩ := exists_edge_of_canonicalParent before tree secondParent
  obtain ⟨firstNext, firstNextMember, firstNextChild, _, firstAttachment, _, _⟩ :=
    exists_edge_same_attachment_side_of_not_mem_exceptions before after tree (Nat.le_refl n) 0 firstMember
      (by simpa only [firstChild] using firstOrdinary)
  obtain ⟨secondNext, secondNextMember, secondNextChild, _, secondAttachment, _, _⟩ :=
    exists_edge_same_attachment_side_of_not_mem_exceptions before after tree (Nat.le_refl n) 0 secondMember
      (by simpa only [secondChild] using secondOrdinary)
  have ownersEq := edge_owners_eq_of_sameCutCell before after tree (Nat.le_refl n) 0 firstMember secondMember
    firstNextMember secondNextMember firstAttachment secondAttachment (firstOwner.trans secondOwner.symm)
    (by simpa only [firstChild, secondChild] using sameCell)
  have firstNewParent := canonicalParent_eq_some_of_mem_fullEdges after tree firstNext firstNextMember
  have secondNewParent := canonicalParent_eq_some_of_mem_fullEdges after tree secondNext secondNextMember
  rw [firstNextChild, firstChild] at firstNewParent
  rw [secondNextChild, secondChild] at secondNewParent
  rw [firstNewParent, secondNewParent, ownersEq]

/-- The cuts needed for relocation include every exceptional vertex, so an
ordinary block cannot straddle a singleton that changes its placement. -/
noncomputable def relocationCutsFrom {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) : Finset ℕ :=
  junctionCutsFrom before after tree upper_le_n ∪ (junctionExceptionsFrom before after tree upper_le_n).image Fin.val

theorem relocationCutsFrom_card_le {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    (relocationCutsFrom before after tree upper_le_n).card ≤ 10 * junctionCountFrom before after tree upper_le_n := by
  have unionBound := Finset.card_union_le (junctionCutsFrom before after tree upper_le_n)
    ((junctionExceptionsFrom before after tree upper_le_n).image Fin.val)
  have imageBound : ((junctionExceptionsFrom before after tree upper_le_n).image Fin.val).card ≤
      (junctionExceptionsFrom before after tree upper_le_n).card := Finset.card_image_le
  have cuts := junctionCutsFrom_card_le before after tree upper_le_n
  have exceptions := junctionExceptionsFrom_card_le before after tree upper_le_n
  unfold relocationCutsFrom
  omega

theorem relocationCutsFrom_comm {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    relocationCutsFrom before after tree upper_le_n = relocationCutsFrom after before tree upper_le_n := by
  rw [relocationCutsFrom, relocationCutsFrom, junctionCutsFrom_comm before after, junctionExceptionsFrom_comm before after]

/-- Every position between ordinary endpoints of one relocation cell is
ordinary as well. This excludes new singleton intruders into its interior. -/
theorem not_mem_exceptions_of_between_same_relocationCell {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) {first second middle : External n}
    (same : SameCutCell (relocationCutsFrom before after tree upper_le_n) first second)
    (firstOrdinary : first ∉ junctionExceptionsFrom before after tree upper_le_n)
    (secondOrdinary : second ∉ junctionExceptionsFrom before after tree upper_le_n)
    (between : first.val ≤ middle.val ∧ middle.val ≤ second.val ∨
      second.val ≤ middle.val ∧ middle.val ≤ first.val) :
    middle ∉ junctionExceptionsFrom before after tree upper_le_n := by
  intro exceptional
  have firstNe : first.val ≠ middle.val := fun equal => firstOrdinary ((Fin.ext equal).symm ▸ exceptional)
  have secondNe : second.val ≠ middle.val := fun equal => secondOrdinary ((Fin.ext equal).symm ▸ exceptional)
  have cutMember : middle.val ∈ relocationCutsFrom before after tree upper_le_n :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨middle, exceptional, rfl⟩)
  have separated := same middle.val cutMember
  omega

end Splay.Accounting.JunctionBendReduction
