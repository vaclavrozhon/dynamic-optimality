import Splay.Lazy.CanonicalHeapView
import Splay.Accounting.WholeSplayHeapLinks

namespace Splay.Rank.Snapshot

/-- Increasing ranks only on `changed` cannot displace an interval minimum
outside that set. The statement concerns actual minima, independently of the
size of their old heavy paths. -/
def MinimumChangesFrom {n : ℕ} (before after : Snapshot n)
    (changed : Finset (External n)) : Prop :=
  ∀ lower upper (nonempty : lower ≤ upper),
    before.intervalMin lower upper nonempty ∉ changed →
      after.intervalMin lower upper nonempty = before.intervalMin lower upper nonempty

theorem minimumChangesFrom_of_rank_raise {n : ℕ} (before after : Snapshot n)
    (changed : Finset (External n))
    (increases : ∀ element, before.rank element ≤ after.rank element)
    (unchanged : ∀ element ∉ changed, after.rank element = before.rank element) :
    before.MinimumChangesFrom after changed := by
  intro lower upper nonempty ordinary
  symm
  apply after.intervalMin_unique
  have minimum := before.intervalMin_isMin lower upper nonempty
  refine ⟨minimum.1, minimum.2.1, ?_⟩
  intro element lowerBound upperBound
  rw [unchanged _ ordinary]
  exact (minimum.2.2 element lowerBound upperBound).trans (increases element)

end Splay.Rank.Snapshot

namespace Splay.Lazy.Canonical

open Splay.Rank

namespace AtNode

theorem owner_eq_of_minimumChangesFrom {n : ℕ} (node : AtNode n)
    {before after : Snapshot n} {changed : Finset (External n)}
    (changes : before.MinimumChangesFrom after changed)
    (ordinary : node.owner before ∉ changed) :
    node.owner after = node.owner before :=
  changes node.wholeLower node.wholeUpper node.whole_nonempty ordinary

theorem branchMin_eq_of_minimumChangesFrom {n : ℕ} (node : AtNode n)
    {before after : Snapshot n} {changed : Finset (External n)}
    (changes : before.MinimumChangesFrom after changed)
    (branch : TernaryBranch) (ordinary : node.branchMin before branch ∉ changed) :
    node.branchMin after branch = node.branchMin before branch :=
  changes (node.branchLower branch) (node.branchUpper branch) (node.branch_nonempty branch) ordinary

theorem heavyBranch_eq_of_owner_eq {n : ℕ} (node : AtNode n)
    {before after : Snapshot n} (same : node.owner after = node.owner before) :
    node.heavyBranch after = node.heavyBranch before := by
  have oldContains := node.owner_in_heavyBranch before
  have newContains := node.owner_in_heavyBranch after
  rw [same] at newContains
  obtain ⟨_, _, unique⟩ := TernaryBranch.existsUnique_contains node.root (node.owner before).val
  exact (unique _ newContains).trans (unique _ oldContains).symm

end AtNode

/-- Every old local light edge whose two endpoints avoid the changed ranks
survives literally, including its attachment node, depth, and side. -/
theorem mem_edgesAtNode_of_minimumChangesFrom {n : ℕ}
    {before after : Snapshot n} {changed : Finset (External n)}
    (changes : before.MinimumChangesFrom after changed)
    (node : AtNode n) (depth : ℕ) {edge : Edge n}
    (member : edge ∈ edgesAtNode before node depth)
    (ownerOrdinary : edge.owner ∉ changed) (childOrdinary : edge.child ∉ changed) :
    edge ∈ edgesAtNode after node depth := by
  obtain ⟨branch, light, rfl⟩ := List.mem_map.mp member
  have ownerEq := node.owner_eq_of_minimumChangesFrom changes ownerOrdinary
  have childEq := node.branchMin_eq_of_minimumChangesFrom changes branch childOrdinary
  have heavyEq := node.heavyBranch_eq_of_owner_eq ownerEq
  apply List.mem_map.mpr
  refine ⟨branch, ?_, ?_⟩
  · rw [mem_lightBranches_iff, heavyEq]
    exact (mem_lightBranches_iff before node branch).mp light
  · simp only [edgeFor, ownerEq, childEq]

/-- Raising a bounded set of ranks only changes edges incident to the old
heavy paths of that set. No bound on their numbers of children is assumed. -/
theorem mem_treeEdges_of_minimumChangesFrom {n lower upper : ℕ}
    {before after : Snapshot n} {changed : Finset (External n)}
    (changes : before.MinimumChangesFrom after changed)
    (tree : Tree.BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ)
    {edge : Edge n} (member : edge ∈ treeEdges before tree upper_le_n depth)
    (ownerOrdinary : edge.owner ∉ changed) (childOrdinary : edge.child ∉ changed) :
    edge ∈ treeEdges after tree upper_le_n depth := by
  induction tree generalizing depth with
  | empty => exact member
  | @node lower root upper left right ihLeft ihRight =>
      simp only [treeEdges, List.mem_append] at member ⊢
      rcases member with (localEdge | leftEdge) | rightEdge
      · exact Or.inl (Or.inl (mem_edgesAtNode_of_minimumChangesFrom changes _ _ localEdge ownerOrdinary childOrdinary))
      · exact Or.inl (Or.inr (ihLeft _ _ leftEdge))
      · exact Or.inr (ihRight _ _ rightEdge)

/-- In particular every old ordinary parent-child relation is preserved. -/
theorem canonicalParent_eq_of_minimumChangesFrom {n : ℕ}
    {before after : Snapshot n} {changed : Finset (External n)}
    (changes : before.MinimumChangesFrom after changed) (tree : Tree.BST 0 n)
    {owner child : External n} (parent : canonicalParent before tree child = some owner)
    (ownerOrdinary : owner ∉ changed) (childOrdinary : child ∉ changed) :
    canonicalParent after tree child = some owner := by
  have link := (Accounting.mem_heapLinks_iff_parent before tree owner child).mpr parent
  obtain ⟨edge, member, endpoints⟩ := List.mem_map.mp (List.mem_toFinset.mp link)
  have ownerEq := congrArg Prod.fst endpoints
  have childEq := congrArg Prod.snd endpoints
  change edge.owner = owner at ownerEq
  change edge.child = child at childEq
  have survives := mem_treeEdges_of_minimumChangesFrom changes tree (Nat.le_refl n) 0 member
    (by simpa only [ownerEq] using ownerOrdinary) (by simpa only [childEq] using childOrdinary)
  have result := Accounting.canonicalParent_eq_some_of_mem_fullEdges after tree edge survives
  simpa only [ownerEq, childEq] using result

end Splay.Lazy.Canonical
