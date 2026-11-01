import RotationIntervalMin
import Splay.Lazy.CanonicalView
import Splay.Rank.FromTree

/-!
Actual canonical heap-edge correspondence under a comparator rotation while
the refinement is fixed. Except for the two rotated records, an old light
edge remains a light edge at the same attachment and branch. Its parent
either stays fixed or changes from the demoted record to the promoted record.

This is structural bulk-transfer correspondence, not yet its ordered block
splice or the geometric proof that transferred nonjunction children are
outer segments.
-/

namespace GreedyMerge.ComparatorHeap

open Splay.Tree
open Splay.Tree.BST
open Splay.Rank
open Splay.Lazy.Canonical

theorem snapshot_min_nat {n : ℕ} (comparator : BST 0 n)
    (lo hi : External n) (hne : lo ≤ hi) :
    Splay.Tree.IsIntervalMin comparator.externalDepth lo.val hi.val
      ((Snapshot.ofTree comparator).intervalMin lo hi hne).val := by
  have hmin := (Snapshot.ofTree comparator).intervalMin_isMin lo hi hne
  refine ⟨hmin.1, hmin.2.1, ?_⟩
  intro position hpLo hpHi
  let key : External n := ⟨position, by have := hi.isLt; omega⟩
  exact hmin.2.2 key hpLo hpHi

theorem snapshot_min_changes {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after)
    (lo hi : External n) (hne : lo ≤ hi) :
    (Snapshot.ofTree before).intervalMin lo hi hne =
        (Snapshot.ofTree after).intervalMin lo hi hne ∨
      (((Snapshot.ofTree before).intervalMin lo hi hne).val = 2 * a + 1 ∧
        ((Snapshot.ofTree after).intervalMin lo hi hne).val = 2 * b + 1) := by
  have oldMin := snapshot_min_nat before lo hi hne
  have newMin := snapshot_min_nat after lo hi hne
  obtain ⟨minimum, hminimum, hunique⟩ :=
    after.existsUnique_intervalExternalDepthMin (Nat.zero_le lo.val) hne
      (show hi.val ≤ 2 * n by have := hi.isLt; omega)
  rcases step.intervalMin oldMin with hstay | ⟨ha, hb⟩
  · left
    exact Fin.ext ((hunique _ hstay).trans (hunique _ newMin).symm)
  · right
    exact ⟨ha, (hunique _ newMin).trans (hunique _ hb).symm⟩

theorem node_owner_changes {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (node : AtNode n) :
    node.owner (Snapshot.ofTree before) = node.owner (Snapshot.ofTree after) ∨
      ((node.owner (Snapshot.ofTree before)).val = 2 * a + 1 ∧
        (node.owner (Snapshot.ofTree after)).val = 2 * b + 1) := by
  exact snapshot_min_changes step node.wholeLower node.wholeUpper node.whole_nonempty

theorem branch_min_changes {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (node : AtNode n)
    (branch : TernaryBranch) :
    node.branchMin (Snapshot.ofTree before) branch =
        node.branchMin (Snapshot.ofTree after) branch ∨
      ((node.branchMin (Snapshot.ofTree before) branch).val = 2 * a + 1 ∧
        (node.branchMin (Snapshot.ofTree after) branch).val = 2 * b + 1) := by
  exact snapshot_min_changes step (node.branchLower branch) (node.branchUpper branch)
    (node.branch_nonempty branch)

theorem local_nonport_edge {n a b depth attachmentDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b depth before after)
    (node : AtNode n) (edge : Edge n)
    (valid : edge.Valid (Snapshot.ofTree before) node attachmentDepth)
    (notA : edge.child.val ≠ 2 * a + 1) (notB : edge.child.val ≠ 2 * b + 1) :
    ∃ newEdge, newEdge ∈ edgesAtNode (Snapshot.ofTree after) node attachmentDepth ∧
      newEdge.child = edge.child ∧
      (newEdge.owner = edge.owner ∨
        (edge.owner.val = 2 * a + 1 ∧ newEdge.owner.val = 2 * b + 1)) ∧
      newEdge.attachmentKey = edge.attachmentKey ∧
      newEdge.attachmentDepth = edge.attachmentDepth ∧ newEdge.branch = edge.branch := by
  have hchildOld := valid.2.2.1
  have hownerOld := valid.2.1
  have hchild : node.branchMin (Snapshot.ofTree after) edge.branch = edge.child := by
    rcases branch_min_changes step node edge.branch with hstay | ⟨ha, _⟩
    · exact hstay.symm.trans hchildOld.symm
    · exact False.elim (notA (by simpa only [hchildOld] using ha))
  have howners := node_owner_changes step node
  have hne : node.branchMin (Snapshot.ofTree after) edge.branch ≠
      node.owner (Snapshot.ofTree after) := by
    intro heq
    rcases howners with hstay | ⟨_, hb⟩
    · apply valid.child_ne_owner
      exact hchild.symm.trans (heq.trans (hstay.symm.trans hownerOld.symm))
    · apply notB
      exact congrArg Fin.val (hchild.symm.trans heq) |>.trans hb
  have hlight : edge.branch ≠ node.heavyBranch (Snapshot.ofTree after) := by
    intro heq
    apply hne
    rw [heq]
    exact (node.owner_eq_branchMin_heavy (Snapshot.ofTree after)).symm
  let newEdge := edgeFor (Snapshot.ofTree after) node attachmentDepth edge.branch
  have hmember : newEdge ∈ edgesAtNode (Snapshot.ofTree after) node attachmentDepth := by
    apply List.mem_map.mpr
    exact ⟨edge.branch, (mem_lightBranches_iff _ _ _).2 hlight, rfl⟩
  refine ⟨newEdge, hmember, hchild, ?_, ?_, ?_, rfl⟩
  · rcases howners with hstay | ⟨ha, hb⟩
    · exact Or.inl (hstay.symm.trans hownerOld.symm)
    · exact Or.inr ⟨by simpa only [hownerOld] using ha, hb⟩
  · exact valid.attachmentKey_eq.symm
  · exact valid.2.2.2.2.2.1.symm

/-- Every nonport canonical heap edge has a concrete counterpart in the
new full light-edge decomposition at the identical attachment. -/
theorem tree_nonport_edge {n lo hi a b depth attachmentDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b depth before after)
    (tree : BST lo hi) (hhi : hi ≤ n) (edge : Edge n)
    (member : edge ∈ treeEdges (Snapshot.ofTree before) tree hhi attachmentDepth)
    (notA : edge.child.val ≠ 2 * a + 1) (notB : edge.child.val ≠ 2 * b + 1) :
    ∃ newEdge, newEdge ∈ treeEdges (Snapshot.ofTree after) tree hhi attachmentDepth ∧
      newEdge.child = edge.child ∧
      (newEdge.owner = edge.owner ∨
        (edge.owner.val = 2 * a + 1 ∧ newEdge.owner.val = 2 * b + 1)) ∧
      newEdge.attachmentKey = edge.attachmentKey ∧
      newEdge.attachmentDepth = edge.attachmentDepth ∧ newEdge.branch = edge.branch := by
  induction tree generalizing attachmentDepth with
  | empty => simp [treeEdges] at member
  | @node lo root hi left right ihLeft ihRight =>
      simp only [treeEdges, List.mem_append] at member ⊢
      rcases member with (hhere | hleft) | hright
      · obtain ⟨newEdge, hnew, hrest⟩ := local_nonport_edge step _ edge
          (mem_edgesAtNode_valid _ _ _ hhere) notA notB
        exact ⟨newEdge, Or.inl (Or.inl hnew), hrest⟩
      · obtain ⟨newEdge, hnew, hrest⟩ := ihLeft _ hleft
        exact ⟨newEdge, Or.inl (Or.inr hnew), hrest⟩
      · obtain ⟨newEdge, hnew, hrest⟩ := ihRight hhi hright
        exact ⟨newEdge, Or.inr hnew, hrest⟩

theorem parent_of_fullEdge {n : ℕ} (snapshot : Snapshot n)
    (tree : BST 0 n) (edge : Edge n) (member : edge ∈ fullEdges snapshot tree) :
    canonicalParent snapshot tree edge.child = some edge.owner := by
  have hchildMem : edge.child ∈ treeChildren snapshot tree (Nat.le_refl n) 0 := by
    exact List.mem_map.mpr ⟨edge, member, rfl⟩
  have hnotRoot : edge.child ≠ canonicalRoot snapshot tree :=
    (mem_treeChildren_iff_ne_subtreeOwner snapshot tree 0 edge.child).1 hchildMem
  obtain ⟨found, lookup, hfoundMem, hfoundChild⟩ :=
    exists_incomingEdge?_eq_some_of_ne_root snapshot tree hnotRoot
  obtain ⟨selected, hselected, hunique⟩ :=
    existsUnique_fullEdge_child_of_ne_root snapshot tree edge.child hnotRoot
  have hsame : found = edge :=
    (hunique found ⟨hfoundMem, hfoundChild⟩).trans (hunique edge ⟨member, rfl⟩).symm
  simp [canonicalParent, lookup, hsame]

theorem nonport_parent_some {n a b depth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b depth before after)
    (tree : BST 0 n) (child oldParent : External n)
    (parent : canonicalParent (Snapshot.ofTree before) tree child = some oldParent)
    (notA : child.val ≠ 2 * a + 1) (notB : child.val ≠ 2 * b + 1) :
    ∃ newParent,
      canonicalParent (Snapshot.ofTree after) tree child = some newParent ∧
      (newParent = oldParent ∨ (oldParent.val = 2 * a + 1 ∧ newParent.val = 2 * b + 1)) := by
  simp only [canonicalParent, Option.map_eq_some_iff] at parent
  obtain ⟨edge, lookup, howner⟩ := parent
  have hspec := incomingEdge?_some_mem (Snapshot.ofTree before) tree lookup
  obtain ⟨newEdge, hnewMem, hnewChild, hnewOwner, _⟩ :=
    tree_nonport_edge step tree (Nat.le_refl n) edge hspec.1
      (by simpa only [hspec.2] using notA) (by simpa only [hspec.2] using notB)
  refine ⟨newEdge.owner, ?_, ?_⟩
  · have hnew := parent_of_fullEdge (Snapshot.ofTree after) tree newEdge hnewMem
    simpa only [hnewChild, hspec.2] using hnew
  · rcases hnewOwner with hsame | ⟨ha, hb⟩
    · exact Or.inl (hsame.trans howner)
    · exact Or.inr ⟨by simpa only [howner] using ha, hb⟩

/-- In the actual canonical heap, every record other than the two rotated
records either keeps its parent or moves from the demoted to the promoted
record. There are no other unaccounted parent changes. -/
theorem nonport_parent_changes {n a b depth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b depth before after)
    (tree : BST 0 n) (child : External n)
    (notA : child.val ≠ 2 * a + 1) (notB : child.val ≠ 2 * b + 1) :
    canonicalParent (Snapshot.ofTree after) tree child =
        canonicalParent (Snapshot.ofTree before) tree child ∨
      ∃ oldParent newParent,
        canonicalParent (Snapshot.ofTree before) tree child = some oldParent ∧
        canonicalParent (Snapshot.ofTree after) tree child = some newParent ∧
        oldParent.val = 2 * a + 1 ∧ newParent.val = 2 * b + 1 := by
  cases hparent : canonicalParent (Snapshot.ofTree before) tree child with
  | some oldParent =>
      obtain ⟨newParent, hnew, hsame | ⟨ha, hb⟩⟩ :=
        nonport_parent_some step tree child oldParent hparent notA notB
      · exact Or.inl (hnew.trans (congrArg some hsame))
      · exact Or.inr ⟨oldParent, newParent, rfl, hnew, ha, hb⟩
  | none =>
      have hroot := (canonicalParent_eq_none_iff (Snapshot.ofTree before) tree child).1 hparent
      have hroots := snapshot_min_changes step
        (subtreeLower tree (Nat.le_refl n)) (subtreeUpper tree (Nat.le_refl n))
        (subtree_nonempty tree (Nat.le_refl n))
      change canonicalRoot (Snapshot.ofTree before) tree =
          canonicalRoot (Snapshot.ofTree after) tree ∨
        ((canonicalRoot (Snapshot.ofTree before) tree).val = 2 * a + 1 ∧
          (canonicalRoot (Snapshot.ofTree after) tree).val = 2 * b + 1) at hroots
      rcases hroots with hsame | ⟨ha, _⟩
      · left
        have hnewRoot := hroot.trans hsame
        exact (canonicalParent_eq_none_iff (Snapshot.ofTree after) tree child).2 hnewRoot
      · exact False.elim (notA (by simpa only [hroot] using ha))

end GreedyMerge.ComparatorHeap

#print axioms GreedyMerge.ComparatorHeap.tree_nonport_edge
#print axioms GreedyMerge.ComparatorHeap.nonport_parent_changes
