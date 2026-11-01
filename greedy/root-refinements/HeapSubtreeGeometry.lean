import ComparatorHeapEdges
import Splay.Tree.SubtreeAt
import Mathlib.Order.Interval.Finset.Fin

/-!
Canonical heap geometry needed by the rank-boundary administration census.
This begins with concrete light-edge decomposition: the children internal
to any BST subtree are exactly its external interval except its minimum.
Every external record in such an interval is consequently a heap descendant
of the subtree minimum in the full canonical heap.
-/

namespace GreedyMerge.HeapGeometry

open Splay.Tree
open Splay.Tree.BST
open Splay.Rank
open Splay.Lazy.Canonical
open ComparatorHeap

theorem mem_subtree_children_iff {n lo hi : ℕ}
    (snapshot : Snapshot n) (tree : BST lo hi) (hhi : hi ≤ n)
    (depth : ℕ) (child : External n) :
    child ∈ treeChildren snapshot tree hhi depth ↔
      child ≠ subtreeOwner snapshot tree hhi ∧
        subtreeLower tree hhi ≤ child ∧ child ≤ subtreeUpper tree hhi := by
  classical
  let children := treeChildren snapshot tree hhi depth
  let root := subtreeOwner snapshot tree hhi
  let interval := Finset.Icc (subtreeLower tree hhi) (subtreeUpper tree hhi)
  have hlo := tree.lower_le_upper
  have hrootInside := subtreeOwner_isMin snapshot tree hhi
  have hrootMem : root ∈ interval := Finset.mem_Icc.mpr ⟨hrootInside.1, hrootInside.2.1⟩
  have hsubset : children.toFinset ⊆ interval.erase root := by
    intro element helement
    have hmember : element ∈ children := List.mem_toFinset.mp helement
    have hnotRoot : element ≠ root := by
      intro heq
      apply subtreeOwner_not_mem_treeChildren snapshot tree hhi depth
      simpa only [children, root, heq] using hmember
    obtain ⟨edge, hedge, hchild⟩ := List.mem_map.mp hmember
    have hinside := mem_treeEdges_inside snapshot tree hhi hedge
    apply Finset.mem_erase.mpr
    refine ⟨hnotRoot, Finset.mem_Icc.mpr ?_⟩
    simpa only [hchild] using hinside.2.2
  have hchildrenCard : children.toFinset.card = 2 * tree.size := by
    rw [List.toFinset_card_of_nodup (treeChildren_nodup snapshot tree hhi depth)]
    exact length_treeChildren snapshot tree hhi depth
  have hintervalCard : interval.card = 2 * tree.size + 1 := by
    rw [Fin.card_Icc]
    simp only [subtreeUpper, subtreeLower]
    have hsize := tree.size_add_lower_eq_upper
    omega
  have htargetCard : (interval.erase root).card = 2 * tree.size := by
    rw [Finset.card_erase_of_mem hrootMem, hintervalCard]
    omega
  have heq : children.toFinset = interval.erase root := by
    apply Finset.eq_of_subset_of_card_le hsubset
    omega
  change child ∈ children ↔ _
  rw [← List.mem_toFinset, heq, Finset.mem_erase, Finset.mem_Icc]

theorem subtree_edge_mem {n innerLo innerHi lo hi depth : ℕ}
    (snapshot : Snapshot n) {inner : BST innerLo innerHi} {tree : BST lo hi}
    (occurrence : SubtreeAt inner depth tree) (hhi : hi ≤ n)
    (startDepth : ℕ) (edge : Edge n)
    (member : edge ∈ treeEdges snapshot inner (Nat.le_trans occurrence.bounds.2 hhi)
      (startDepth + depth)) :
    edge ∈ treeEdges snapshot tree hhi startDepth := by
  induction occurrence generalizing startDepth with
  | here => simpa using member
  | @left lo root hi depth leftTree occurrence rightTree ih =>
      have hrootHi := rightTree.lower_le_upper
      have hbound : root ≤ n := by omega
      have hmember : edge ∈ treeEdges snapshot inner
          (Nat.le_trans occurrence.bounds.2 hbound) ((startDepth + 1) + depth) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member
      have hleft := ih hbound (startDepth + 1) hmember
      simp only [treeEdges, List.mem_append]
      exact Or.inl (Or.inr hleft)
  | @right lo root hi depth leftTree rightTree occurrence ih =>
      have hmember : edge ∈ treeEdges snapshot inner
          (Nat.le_trans occurrence.bounds.2 hhi) ((startDepth + 1) + depth) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member
      have hright := ih hhi (startDepth + 1) hmember
      simp only [treeEdges, List.mem_append]
      exact Or.inr hright

inductive Ancestor {α : Type*} (parent : α → Option α) : α → α → Prop
  | refl (record : α) : Ancestor parent record record
  | step {ancestor middle child : α} (edge : parent child = some middle)
      (previous : Ancestor parent ancestor middle) : Ancestor parent ancestor child

namespace Ancestor

theorem rank_le {α : Type*} {parent : α → Option α} (rank : α → ℕ)
    (ordered : ∀ child owner, parent child = some owner → rank owner < rank child)
    {ancestor child : α} (path : Ancestor parent ancestor child) : rank ancestor ≤ rank child := by
  induction path with
  | refl => exact Nat.le_refl _
  | step edge previous ih =>
      have h := ordered _ _ edge
      omega

theorem rank_lt_of_ne {α : Type*} {parent : α → Option α} (rank : α → ℕ)
    (ordered : ∀ child owner, parent child = some owner → rank owner < rank child)
    {ancestor child : α} (path : Ancestor parent ancestor child) (hne : ancestor ≠ child) :
    rank ancestor < rank child := by
  cases path with
  | refl => exact False.elim (hne rfl)
  | step edge previous =>
      have hlow := previous.rank_le rank ordered
      have hstep := ordered _ _ edge
      omega

theorem comparable {α : Type*} {parent : α → Option α} {first second child : α}
    (hfirst : Ancestor parent first child) (hsecond : Ancestor parent second child) :
    Ancestor parent first second ∨ Ancestor parent second first := by
  induction hfirst generalizing second with
  | refl => exact Or.inr hsecond
  | @step middle child edge previous ih =>
      cases hsecond with
      | refl => exact Or.inl (.step edge previous)
      | @step other child otherEdge otherPrevious =>
          have heq : other = middle := Option.some.inj (otherEdge.symm.trans edge)
          subst other
          exact ih otherPrevious

theorem eq_of_rank_eq {α : Type*} {parent : α → Option α} (rank : α → ℕ)
    (ordered : ∀ child owner, parent child = some owner → rank owner < rank child)
    {first second child : α} (hfirst : Ancestor parent first child)
    (hsecond : Ancestor parent second child) (heq : rank first = rank second) : first = second := by
  by_contra hne
  rcases hfirst.comparable hsecond with h | h
  · have hlt := h.rank_lt_of_ne rank ordered hne
    omega
  · have hlt := h.rank_lt_of_ne rank ordered (Ne.symm hne)
    omega

end Ancestor

noncomputable def Ancestors {n : ℕ} (snapshot : Snapshot n)
    (tree : BST 0 n) (child : External n) : Finset (External n) := by
  classical
  exact Finset.univ.filter fun owner => Ancestor (canonicalParent snapshot tree) owner child

theorem ancestor_card_le_rank_succ {n : ℕ} (snapshot : Snapshot n)
    (tree : BST 0 n) (child : External n) :
    (Ancestors snapshot tree child).card ≤
      snapshot.rank child + 1 := by
  classical
  let ancestors := Finset.univ.filter fun owner => Ancestor (canonicalParent snapshot tree) owner child
  have ordered : ∀ child owner, canonicalParent snapshot tree child = some owner →
      snapshot.rank owner < snapshot.rank child := by
    intro child owner parent
    exact rank_canonicalParent_lt snapshot tree parent
  have hinj : Set.InjOn snapshot.rank (ancestors : Set (External n)) := by
    intro first hfirst second hsecond heq
    have hf := (Finset.mem_filter.mp hfirst).2
    have hs := (Finset.mem_filter.mp hsecond).2
    exact hf.eq_of_rank_eq snapshot.rank ordered hs heq
  have hsubset : ancestors.image snapshot.rank ⊆ Finset.range (snapshot.rank child + 1) := by
    intro value hvalue
    obtain ⟨owner, howner, rfl⟩ := Finset.mem_image.mp hvalue
    have hpath := (Finset.mem_filter.mp howner).2
    have hrank := hpath.rank_le snapshot.rank ordered
    exact Finset.mem_range.mpr (by omega)
  have hcardImage := Finset.card_image_of_injOn hinj
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_range, hcardImage] at hcard
  exact hcard

/-- Every external record inside a literal subtree lies below that
subtree's selected minimum in the actual full canonical heap. -/
theorem subtree_owner_ancestor {n lo hi depth : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n) (inner : BST lo hi)
    (occurrence : SubtreeAt inner depth tree) (child : External n)
    (hchildLo : 2 * lo ≤ child.val) (hchildHi : child.val ≤ 2 * hi) :
    Ancestor (canonicalParent snapshot tree)
      (subtreeOwner snapshot inner occurrence.bounds.2) child := by
  generalize hrank : snapshot.rank child = rank
  induction rank using Nat.strong_induction_on generalizing child with
  | h rank ih =>
      let root := subtreeOwner snapshot inner occurrence.bounds.2
      by_cases hroot : child = root
      · subst child
        exact .refl root
      · have hmember : child ∈ treeChildren snapshot inner occurrence.bounds.2 depth := by
          apply (mem_subtree_children_iff snapshot inner occurrence.bounds.2 depth child).2
          exact ⟨hroot, hchildLo, hchildHi⟩
        obtain ⟨edge, hedge, hchild⟩ := List.mem_map.mp hmember
        have hinside := mem_treeEdges_inside snapshot inner occurrence.bounds.2 hedge
        have hstrict := mem_treeEdges_rank_lt snapshot inner occurrence.bounds.2 hedge
        have hglobal : edge ∈ fullEdges snapshot tree := by
          apply subtree_edge_mem snapshot occurrence (Nat.le_refl n) 0 edge
          simpa using hedge
        have hparent := parent_of_fullEdge snapshot tree edge hglobal
        have hprev := ih (snapshot.rank edge.owner) (by simpa [hchild, hrank] using hstrict)
          edge.owner hinside.1 hinside.2.1 rfl
        apply Ancestor.step (middle := edge.owner)
        · simpa only [hchild] using hparent
        · exact hprev

/-- Literal subtree external intervals sharing a record are nested. -/
theorem subtree_intervals_nested
    {firstLo firstHi secondLo secondHi lo hi firstDepth secondDepth : ℕ}
    {first : BST firstLo firstHi} {second : BST secondLo secondHi} {tree : BST lo hi}
    (firstOccurrence : SubtreeAt first firstDepth tree)
    (secondOccurrence : SubtreeAt second secondDepth tree) (record : ℕ)
    (firstLower : 2 * firstLo ≤ record) (firstUpper : record ≤ 2 * firstHi)
    (secondLower : 2 * secondLo ≤ record) (secondUpper : record ≤ 2 * secondHi) :
    (firstLo ≤ secondLo ∧ secondHi ≤ firstHi) ∨
      (secondLo ≤ firstLo ∧ firstHi ≤ secondHi) := by
  induction firstOccurrence generalizing secondDepth with
  | here => exact Or.inl secondOccurrence.bounds
  | @left lo root hi depth leftTree occurrence rightTree ih =>
      cases secondOccurrence with
      | here => exact Or.inr (occurrence.left rightTree).bounds
      | left other right => exact ih other
      | right left other =>
          have hf := occurrence.bounds
          have hs := other.bounds
          omega
  | @right lo root hi depth leftTree rightTree occurrence ih =>
      cases secondOccurrence with
      | here => exact Or.inr (SubtreeAt.right leftTree occurrence).bounds
      | left other right =>
          have hf := occurrence.bounds
          have hs := other.bounds
          omega
      | right left other => exact ih other

/-- Every recorded light edge comes from a literal internal-node occurrence. -/
theorem tree_edge_occurrence {n lo hi : ℕ}
    (snapshot : Snapshot n) (tree : BST lo hi) (hhi : hi ≤ n)
    (startDepth : ℕ) (edge : Edge n)
    (member : edge ∈ treeEdges snapshot tree hhi startDepth) :
    ∃ (node : AtNode n) (depth : ℕ),
      SubtreeAt (.node node.left node.right) depth tree ∧
        edge.Valid snapshot node (startDepth + depth) := by
  induction tree generalizing startDepth with
  | empty => simp [treeEdges] at member
  | @node lo root hi left right ihLeft ihRight =>
      let node : AtNode n := ⟨lo, root, hi, left, right, hhi⟩
      have hroot : root ≤ n := by have := right.lower_le_upper; omega
      simp only [treeEdges, List.mem_append] at member
      rcases member with (localMember | leftMember) | rightMember
      · exact ⟨node, 0, .here, by
          simpa only [Nat.add_zero] using mem_edgesAtNode_valid snapshot node startDepth localMember⟩
      · obtain ⟨inner, depth, occurrence, valid⟩ := ihLeft hroot (startDepth + 1) leftMember
        exact ⟨inner, depth + 1, occurrence.left right, by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valid⟩
      · obtain ⟨inner, depth, occurrence, valid⟩ := ihRight hhi (startDepth + 1) rightMember
        exact ⟨inner, depth + 1, SubtreeAt.right left occurrence, by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valid⟩

/-- A real heap parent relation has a concrete subtree interval containing
both endpoints, selected by the parent's minimum. -/
theorem parent_occurrence {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {child owner : External n} (parent : canonicalParent snapshot tree child = some owner) :
    ∃ (node : AtNode n) (depth : ℕ),
      SubtreeAt (.node node.left node.right) depth tree ∧
      node.owner snapshot = owner ∧
      node.wholeLower ≤ child ∧ child ≤ node.wholeUpper := by
  simp only [canonicalParent, Option.map_eq_some_iff] at parent
  obtain ⟨edge, lookup, ownerEq⟩ := parent
  have edgeSpec := incomingEdge?_some_mem snapshot tree lookup
  obtain ⟨node, depth, occurrence, valid⟩ :=
    tree_edge_occurrence snapshot tree (Nat.le_refl n) 0 edge edgeSpec.1
  refine ⟨node, depth, occurrence, valid.2.1.symm.trans ownerEq, ?_⟩
  have inside := node.branchMin_in_whole snapshot edge.branch
  simpa only [← valid.2.2.1, edgeSpec.2] using inside

/-- Every record between a parent and its child lies below that parent. -/
theorem parent_spans_ancestor {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {child owner record : External n}
    (parent : canonicalParent snapshot tree child = some owner)
    (between : (owner ≤ record ∧ record ≤ child) ∨
      (child ≤ record ∧ record ≤ owner)) :
    Ancestor (canonicalParent snapshot tree) owner record := by
  obtain ⟨node, depth, occurrence, ownerEq, childLo, childHi⟩ :=
    parent_occurrence snapshot tree parent
  have ownerMin := node.owner_isMin snapshot
  rw [ownerEq] at ownerMin
  have inside : node.wholeLower ≤ record ∧ record ≤ node.wholeUpper := by
    rcases between with h | h
    · exact ⟨le_trans ownerMin.1 h.1, le_trans h.2 childHi⟩
    · exact ⟨le_trans childLo h.1, le_trans h.2 ownerMin.2.1⟩
  have path := subtree_owner_ancestor snapshot tree (.node node.left node.right)
    occurrence record inside.1 inside.2
  change Ancestor (canonicalParent snapshot tree) (node.owner snapshot) record at path
  rwa [ownerEq] at path

/-- An owner whose two children straddle a cut is an ancestor of the cut
record.  This is proved from actual canonical light edges, without an
assumed ordered-heap axiom. -/
theorem children_span_ancestor {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {left right owner record : External n}
    (leftParent : canonicalParent snapshot tree left = some owner)
    (rightParent : canonicalParent snapshot tree right = some owner)
    (leftLe : left ≤ record) (rightLe : record ≤ right) :
    Ancestor (canonicalParent snapshot tree) owner record := by
  obtain ⟨leftNode, leftDepth, leftOccurrence, leftOwner, leftLo, leftHi⟩ :=
    parent_occurrence snapshot tree leftParent
  obtain ⟨rightNode, rightDepth, rightOccurrence, rightOwner, rightLo, rightHi⟩ :=
    parent_occurrence snapshot tree rightParent
  have leftMin := leftNode.owner_isMin snapshot
  have rightMin := rightNode.owner_isMin snapshot
  rw [leftOwner] at leftMin
  rw [rightOwner] at rightMin
  have nested := subtree_intervals_nested leftOccurrence rightOccurrence owner.val
    leftMin.1 leftMin.2.1 rightMin.1 rightMin.2.1
  rcases nested with h | h
  · have insideLo : 2 * leftNode.lower ≤ record.val := le_trans leftLo leftLe
    have insideHi : record.val ≤ 2 * leftNode.upper := by
      have hi : right.val ≤ 2 * rightNode.upper := rightHi
      have hr : record.val ≤ right.val := rightLe
      omega
    have path := subtree_owner_ancestor snapshot tree (.node leftNode.left leftNode.right)
      leftOccurrence record insideLo insideHi
    change Ancestor (canonicalParent snapshot tree) (leftNode.owner snapshot) record at path
    rwa [leftOwner] at path
  · have insideLo : 2 * rightNode.lower ≤ record.val := by
      have lo : 2 * leftNode.lower ≤ left.val := leftLo
      have hl : left.val ≤ record.val := leftLe
      omega
    have insideHi : record.val ≤ 2 * rightNode.upper := le_trans rightLe rightHi
    have path := subtree_owner_ancestor snapshot tree (.node rightNode.left rightNode.right)
      rightOccurrence record insideLo insideHi
    change Ancestor (canonicalParent snapshot tree) (rightNode.owner snapshot) record at path
    rwa [rightOwner] at path

noncomputable def SpanningOwners {n : ℕ} (snapshot : Snapshot n)
    (tree : BST 0 n) (record : External n) : Finset (External n) := by
  classical
  exact Finset.univ.filter fun owner => ∃ left right,
    canonicalParent snapshot tree left = some owner ∧
    canonicalParent snapshot tree right = some owner ∧
    left ≤ record ∧ record ≤ right

/-- There are at most rank(cut)+1 actual heap owners with children on both
sides of a cut.  A consecutive side-block partition can charge at most a
constant number of spanning blocks to each such owner. -/
theorem spanning_owners_card {n : ℕ} (snapshot : Snapshot n)
    (tree : BST 0 n) (record : External n) :
    (SpanningOwners snapshot tree record).card ≤ snapshot.rank record + 1 := by
  classical
  apply le_trans (Finset.card_le_card ?_) (ancestor_card_le_rank_succ snapshot tree record)
  intro owner member
  obtain ⟨left, right, hl, hr, hlo, hhi⟩ := (Finset.mem_filter.mp member).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    children_span_ancestor snapshot tree hl hr hlo hhi⟩

end GreedyMerge.HeapGeometry

#print axioms GreedyMerge.HeapGeometry.subtree_owner_ancestor

#print axioms GreedyMerge.HeapGeometry.children_span_ancestor
#print axioms GreedyMerge.HeapGeometry.spanning_owners_card
