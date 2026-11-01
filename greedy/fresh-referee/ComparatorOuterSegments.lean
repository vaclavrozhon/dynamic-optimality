import Mathlib
import HeapSubtreeGeometry

namespace GreedyMerge.ComparatorOuter

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.ComparatorHeap GreedyMerge.HeapGeometry

/-- Only the minimum of a literal refinement subtree can have a heap
child outside its interval. Every other record's children stay inside.
This derives the needed geometric confinement from actual attachment
occurrences and laminar subtree intervals. -/
theorem nonroot_children_stay_inside {n lo hi depth : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n) (inner : BST lo hi)
    (occurrence : SubtreeAt inner depth tree) (owner child : External n)
    (ownerLo : 2*lo ≤ owner.val) (ownerHi : owner.val ≤ 2*hi)
    (notRoot : owner ≠ subtreeOwner snapshot inner occurrence.bounds.2)
    (parent : canonicalParent snapshot tree child=some owner) :
    2*lo ≤ child.val ∧ child.val ≤ 2*hi := by
  obtain ⟨node,nodeDepth,nodeOccurrence,nodeOwner,childLo,childHi⟩ :=
    parent_occurrence snapshot tree parent
  have ownerMin := node.owner_isMin snapshot
  rw [nodeOwner] at ownerMin
  have nested := subtree_intervals_nested occurrence nodeOccurrence owner.val
    ownerLo ownerHi ownerMin.1 ownerMin.2.1
  rcases nested with nodeInside | innerInside
  · constructor
    · have hc : 2*node.lower ≤ child.val := childLo
      omega
    · have hc : child.val ≤ 2*node.upper := childHi
      omega
  · have hmin : Splay.Rank.IsIntervalMin snapshot.rank
        (subtreeLower inner occurrence.bounds.2) (subtreeUpper inner occurrence.bounds.2) owner := by
      refine ⟨ownerLo,ownerHi,?_⟩
      intro key keyLo keyHi
      apply ownerMin.2.2 key
      · change 2*node.lower ≤ key.val
        change 2*lo ≤ key.val at keyLo
        omega
      · change key.val ≤ 2*node.upper
        change key.val ≤ 2*hi at keyHi
        omega
    have heq := snapshot.intervalMin_unique (subtreeLower inner occurrence.bounds.2)
      (subtreeUpper inner occurrence.bounds.2) (subtree_nonempty inner occurrence.bounds.2) hmin
    exact False.elim (notRoot heq)

/-- Given a literal subtree whose minimum changes a→b, all old children
of b lie inside that subtree, and all final children of a lie inside it.
The geometry does not require the subtree to be the lowest junction. -/
theorem receiver_and_source_confined {n lo hi depth : ℕ}
    (oldSnap newSnap : Snapshot n) (tree : BST 0 n) (inner : BST lo hi)
    (occurrence : SubtreeAt inner depth tree) (a b : External n)
    (oldRoot : subtreeOwner oldSnap inner occurrence.bounds.2=a)
    (newRoot : subtreeOwner newSnap inner occurrence.bounds.2=b) (different : a≠b) :
    (∀ child, canonicalParent oldSnap tree child=some b → 2*lo ≤ child.val ∧ child.val ≤ 2*hi) ∧
    (∀ child, canonicalParent newSnap tree child=some a → 2*lo ≤ child.val ∧ child.val ≤ 2*hi) := by
  have oldMin := subtreeOwner_isMin oldSnap inner occurrence.bounds.2
  have newMin := subtreeOwner_isMin newSnap inner occurrence.bounds.2
  rw [oldRoot] at oldMin
  rw [newRoot] at newMin
  constructor
  · intro child parent
    apply nonroot_children_stay_inside oldSnap tree inner occurrence b child newMin.1 newMin.2.1
      (by simpa [oldRoot] using Ne.symm different) parent
  · intro child parent
    apply nonroot_children_stay_inside newSnap tree inner occurrence a child oldMin.1 oldMin.2.1
      (by simpa [newRoot] using different) parent

/-- Every old child of a lying outside a literal subtree whose root owner
changes a→b must transfer to b. Thus the two complete outer source segments
are transferred; they cannot be punctured by an unchanged old child. -/
theorem outside_source_child_transfers {n lo hi subtreeDepth a b rotationDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (tree : BST 0 n) (inner : BST lo hi) (occurrence : SubtreeAt inner subtreeDepth tree)
    (oldRecord newRecord child : External n)
    (oldValue : oldRecord.val=2*a+1) (newValue : newRecord.val=2*b+1)
    (different : oldRecord≠newRecord)
    (oldRoot : subtreeOwner (Snapshot.ofTree before) inner occurrence.bounds.2=oldRecord)
    (newRoot : subtreeOwner (Snapshot.ofTree after) inner occurrence.bounds.2=newRecord)
    (oldParent : canonicalParent (Snapshot.ofTree before) tree child=some oldRecord)
    (outside : child.val<2*lo ∨ 2*hi<child.val) :
    canonicalParent (Snapshot.ofTree after) tree child=some newRecord := by
  have oldMin := subtreeOwner_isMin (Snapshot.ofTree before) inner occurrence.bounds.2
  have newMin := subtreeOwner_isMin (Snapshot.ofTree after) inner occurrence.bounds.2
  rw [oldRoot] at oldMin
  rw [newRoot] at newMin
  have notA : child.val≠2*a+1 := by
    have hLo : 2*lo ≤ oldRecord.val := oldMin.1
    have hHi : oldRecord.val ≤ 2*hi := oldMin.2.1
    omega
  have notB : child.val≠2*b+1 := by
    have hLo : 2*lo ≤ newRecord.val := newMin.1
    have hHi : newRecord.val ≤ 2*hi := newMin.2.1
    omega
  obtain ⟨parent,hparent,hsame | ⟨_,hnew⟩⟩ :=
    nonport_parent_some step tree child oldRecord oldParent notA notB
  · rw [hsame] at hparent
    have confined := (receiver_and_source_confined (Snapshot.ofTree before)
      (Snapshot.ofTree after) tree inner occurrence oldRecord newRecord oldRoot newRoot different).2 child hparent
    omega
  · have heq : parent=newRecord := Fin.ext (hnew.trans newValue.symm)
    simpa [heq] using hparent

/-- Any record outside the junction interval is on the same side of the
old and new owners, and farther outward than every record inside it. -/
theorem outside_order_geometry {lo hi : ℕ} {a b child inner : ℕ}
    (aLo : 2*lo ≤ a) (aHi : a ≤ 2*hi)
    (bLo : 2*lo ≤ b) (bHi : b ≤ 2*hi)
    (innerLo : 2*lo ≤ inner) (innerHi : inner ≤ 2*hi)
    (outside : child<2*lo ∨ 2*hi<child) :
    (child < a ∧ child < b ∧ child < inner) ∨ (a < child ∧ b < child ∧ inner < child) := by
  omega

theorem disjoint_subtree_nonport_edge {n lo hi a b rotationDepth attachmentDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (inner : BST lo hi) (hhi : hi ≤ n) (edge : Edge n)
    (member : edge ∈ treeEdges (Snapshot.ofTree before) inner hhi attachmentDepth)
    (notA : edge.child.val≠2*a+1) (notB : edge.child.val≠2*b+1)
    (excluded : (2*a+1<2*lo ∨ 2*hi<2*a+1) ∨ (2*b+1<2*lo ∨ 2*hi<2*b+1)) :
    ∃ newEdge, newEdge ∈ treeEdges (Snapshot.ofTree after) inner hhi attachmentDepth ∧
      newEdge.child=edge.child ∧ newEdge.owner=edge.owner := by
  obtain ⟨newEdge,newMember,newChild,newOwner,_⟩ :=
    tree_nonport_edge step inner hhi edge member notA notB
  refine ⟨newEdge,newMember,newChild,?_⟩
  rcases newOwner with hsame | ⟨ha,hb⟩
  · exact hsame
  · have oldInside := mem_treeEdges_inside (Snapshot.ofTree before) inner hhi member
    have newInside := mem_treeEdges_inside (Snapshot.ofTree after) inner hhi newMember
    have oaLo : 2*lo ≤ edge.owner.val := oldInside.1
    have oaHi : edge.owner.val ≤ 2*hi := oldInside.2.1
    have nbLo : 2*lo ≤ newEdge.owner.val := newInside.1
    have nbHi : newEdge.owner.val ≤ 2*hi := newInside.2.1
    omega

/-- Within a literal subtree excluding at least one rotated record, every
nonroot nonport record keeps its actual global heap parent. -/
theorem disjoint_subtree_parent_preserved {n lo hi subtreeDepth a b rotationDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (tree : BST 0 n) (inner : BST lo hi) (occurrence : SubtreeAt inner subtreeDepth tree)
    (child : External n) (childLo : 2*lo ≤ child.val) (childHi : child.val ≤ 2*hi)
    (notRoot : child≠subtreeOwner (Snapshot.ofTree before) inner occurrence.bounds.2)
    (notA : child.val≠2*a+1) (notB : child.val≠2*b+1)
    (excluded : (2*a+1<2*lo ∨ 2*hi<2*a+1) ∨ (2*b+1<2*lo ∨ 2*hi<2*b+1)) :
    canonicalParent (Snapshot.ofTree after) tree child = canonicalParent (Snapshot.ofTree before) tree child := by
  have childMember : child ∈ treeChildren (Snapshot.ofTree before) inner occurrence.bounds.2 subtreeDepth :=
    (mem_subtree_children_iff (Snapshot.ofTree before) inner occurrence.bounds.2 subtreeDepth child).2
      ⟨notRoot,childLo,childHi⟩
  obtain ⟨edge,member,childEq⟩ := List.mem_map.mp childMember
  obtain ⟨newEdge,newMember,newChild,newOwner⟩ :=
    disjoint_subtree_nonport_edge step inner occurrence.bounds.2 edge member
      (by simpa [childEq] using notA) (by simpa [childEq] using notB) excluded
  have oldGlobal : edge ∈ fullEdges (Snapshot.ofTree before) tree := by
    apply subtree_edge_mem (Snapshot.ofTree before) occurrence (Nat.le_refl n) 0 edge
    simpa using member
  have newGlobal : newEdge ∈ fullEdges (Snapshot.ofTree after) tree := by
    apply subtree_edge_mem (Snapshot.ofTree after) occurrence (Nat.le_refl n) 0 newEdge
    simpa using newMember
  have oldParent := parent_of_fullEdge (Snapshot.ofTree before) tree edge oldGlobal
  have newParent := parent_of_fullEdge (Snapshot.ofTree after) tree newEdge newGlobal
  have oldParent' : canonicalParent (Snapshot.ofTree before) tree child=some edge.owner := by
    simpa [childEq] using oldParent
  rw [oldParent']
  simpa [newChild,childEq,newOwner] using newParent

def Separated {n : ℕ} (node : AtNode n) (a b : ℕ) : Prop :=
  ∀ branch : TernaryBranch,
    ¬ (branch.Contains node.root a ∧ branch.Contains node.root b)

/-- At a separated junction every individual ternary port keeps its
minimum identity. Only the winner among the three ports switches. -/
theorem separated_branch_min_fixed {n a b rotationDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (node : AtNode n) (separated : Separated node (2*a+1) (2*b+1))
    (branch : TernaryBranch) :
    node.branchMin (Snapshot.ofTree before) branch = node.branchMin (Snapshot.ofTree after) branch := by
  rcases branch_min_changes step node branch with hsame | ⟨ha,hb⟩
  · exact hsame
  · have oldContains := node.branchMin_in_branch (Snapshot.ofTree before) branch
    have newContains := node.branchMin_in_branch (Snapshot.ofTree after) branch
    rw [ha] at oldContains
    rw [hb] at newContains
    exact False.elim (separated branch ⟨oldContains,newContains⟩)

/-- Every record inside a separated junction, apart from its three port
roots, keeps its global parent. Together with the outer-transfer theorem,
this excludes unaccounted inner bulk transfers. -/
theorem inside_junction_nonport_preserved {n a b rotationDepth subtreeDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (tree : BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) subtreeDepth tree)
    (separated : Separated node (2*a+1) (2*b+1))
    (child : External n) (childLo : 2*node.lower ≤ child.val) (childHi : child.val ≤ 2*node.upper)
    (notPorts : ∀ branch, child≠node.branchMin (Snapshot.ofTree before) branch)
    (notA : child.val≠2*a+1) (notB : child.val≠2*b+1) :
    canonicalParent (Snapshot.ofTree after) tree child = canonicalParent (Snapshot.ofTree before) tree child := by
  have hlo := node.lower_le_root
  have hhi := node.root_lt_upper
  by_cases hleft : child.val≤2*node.root
  · have leftOccurrence : SubtreeAt node.left (1+subtreeDepth) tree :=
      (SubtreeAt.left SubtreeAt.here node.right).trans occurrence
    have excluded : (2*a+1<2*node.lower ∨ 2*node.root<2*a+1) ∨
        (2*b+1<2*node.lower ∨ 2*node.root<2*b+1) := by
      have h := separated TernaryBranch.left
      simp only [TernaryBranch.Contains] at h
      omega
    apply disjoint_subtree_parent_preserved step tree node.left leftOccurrence child childLo hleft
      (by simpa only [AtNode.branchMin,AtNode.branchLower,AtNode.branchUpper,AtNode.wholeLower,
        subtreeOwner,subtreeLower,subtreeUpper] using notPorts TernaryBranch.left) notA notB excluded
  · by_cases hright : 2*node.root+2≤child.val
    · have rightOccurrence : SubtreeAt node.right (1+subtreeDepth) tree :=
        (SubtreeAt.right node.left SubtreeAt.here).trans occurrence
      have excluded : (2*a+1<2*(node.root+1) ∨ 2*node.upper<2*a+1) ∨
          (2*b+1<2*(node.root+1) ∨ 2*node.upper<2*b+1) := by
        have h := separated TernaryBranch.right
        simp only [TernaryBranch.Contains] at h
        omega
      apply disjoint_subtree_parent_preserved step tree node.right rightOccurrence child (by omega) childHi
        (by simpa only [AtNode.branchMin,AtNode.branchLower,AtNode.branchUpper,AtNode.wholeUpper,
          subtreeOwner,subtreeLower,subtreeUpper,Nat.mul_add,Nat.mul_one] using notPorts TernaryBranch.right) notA notB excluded
    · have heq : child=node.branchMin (Snapshot.ofTree before) .middle := by
        apply Fin.ext
        have h := node.branchMin_in_branch (Snapshot.ofTree before) .middle
        simp only [TernaryBranch.Contains] at h
        omega
      exact False.elim (notPorts .middle heq)

/-- A separated junction exists for every two distinct external records:
this is the actual lowest common ternary ancestor in the fixed refinement. -/
theorem exists_separated_junction {n lo hi : ℕ} (tree : BST lo hi) (hhi : hi ≤ n)
    (a b : External n) (aLo : 2*lo ≤ a.val) (aHi : a.val ≤ 2*hi)
    (bLo : 2*lo ≤ b.val) (bHi : b.val ≤ 2*hi) (different : a≠b) :
    ∃ (node : AtNode n) (depth : ℕ), SubtreeAt (.node node.left node.right) depth tree ∧
      2*node.lower ≤ a.val ∧ a.val ≤ 2*node.upper ∧
      2*node.lower ≤ b.val ∧ b.val ≤ 2*node.upper ∧ Separated node a.val b.val := by
  induction tree with
  | empty =>
      apply False.elim
      apply different
      apply Fin.ext
      omega
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      by_cases bothLeft : a.val≤2*q ∧ b.val≤2*q
      · obtain ⟨node,depth,occurrence,rest⟩ :=
          ihLeft (by omega) aLo bothLeft.1 bLo bothLeft.2
        exact ⟨node,depth+1,occurrence.left right,rest⟩
      · by_cases bothRight : 2*(q+1)≤a.val ∧ 2*(q+1)≤b.val
        · obtain ⟨node,depth,occurrence,rest⟩ :=
            ihRight hhi bothRight.1 aHi bothRight.2 bHi
          exact ⟨node,depth+1,SubtreeAt.right left occurrence,rest⟩
        · let node : AtNode n := ⟨lo,q,hi,left,right,hhi⟩
          refine ⟨node,0,SubtreeAt.here,aLo,aHi,bLo,bHi,?_⟩
          intro branch
          cases branch with
          | left =>exact bothLeft
          | right =>
              change ¬(2*q+2≤a.val ∧ 2*q+2≤b.val)
              omega
          | middle =>
              change ¬(a.val=2*q+1 ∧ b.val=2*q+1)
              intro heq
              exact different (Fin.ext (by omega))

/-- Exact outside-set characterization away from the three junction ports.
Combined with ordered child lists, this says precisely that bulk movement
is a left outer segment and a right outer segment. -/
theorem bulk_transfer_iff_outside {n a b rotationDepth subtreeDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (tree : BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) subtreeDepth tree)
    (separated : Separated node (2*a+1) (2*b+1))
    (oldRecord newRecord child : External n)
    (oldValue : oldRecord.val=2*a+1) (newValue : newRecord.val=2*b+1)
    (different : oldRecord≠newRecord)
    (oldRoot : subtreeOwner (Snapshot.ofTree before) (.node node.left node.right) occurrence.bounds.2=oldRecord)
    (newRoot : subtreeOwner (Snapshot.ofTree after) (.node node.left node.right) occurrence.bounds.2=newRecord)
    (oldParent : canonicalParent (Snapshot.ofTree before) tree child=some oldRecord)
    (notPorts : ∀ branch, child≠node.branchMin (Snapshot.ofTree before) branch)
    (notA : child.val≠2*a+1) (notB : child.val≠2*b+1) :
    canonicalParent (Snapshot.ofTree after) tree child=some newRecord ↔
      child.val<2*node.lower ∨ 2*node.upper<child.val := by
  constructor
  · intro newParent
    by_contra hnot
    have inside := inside_junction_nonport_preserved step tree node occurrence separated child
      (by omega) (by omega) notPorts notA notB
    rw [oldParent,newParent] at inside
    exact different (Option.some.inj inside).symm
  · intro outside
    exact outside_source_child_transfers step tree (.node node.left node.right) occurrence
      oldRecord newRecord child oldValue newValue different oldRoot newRoot oldParent outside

theorem junction_owners_are_ports {n a b rotationDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (node : AtNode n) (separated : Separated node (2*a+1) (2*b+1)) :
    (∃ branch, node.branchMin (Snapshot.ofTree before) branch=node.owner (Snapshot.ofTree before)) ∧
    (∃ branch, node.branchMin (Snapshot.ofTree before) branch=node.owner (Snapshot.ofTree after)) := by
  constructor
  · exact ⟨node.heavyBranch (Snapshot.ofTree before),
      (node.owner_eq_branchMin_heavy (Snapshot.ofTree before)).symm⟩
  · refine ⟨node.heavyBranch (Snapshot.ofTree after),?_⟩
    rw [separated_branch_min_fixed step node separated]
    exact (node.owner_eq_branchMin_heavy (Snapshot.ofTree after)).symm

theorem junction_ports_pairwise_distinct {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    [node.branchMin snapshot .left,node.branchMin snapshot .middle,node.branchMin snapshot .right].Nodup := by
  have hl := node.branchMin_in_branch snapshot .left
  have hm := node.branchMin_in_branch snapshot .middle
  have hr := node.branchMin_in_branch snapshot .right
  simp only [TernaryBranch.Contains] at hl hm hr
  have hLM : node.branchMin snapshot .left≠node.branchMin snapshot .middle := by
    intro h;have hh := congrArg Fin.val h;omega
  have hLR : node.branchMin snapshot .left≠node.branchMin snapshot .right := by
    intro h;have hh := congrArg Fin.val h;omega
  have hMR : node.branchMin snapshot .middle≠node.branchMin snapshot .right := by
    intro h;have hh := congrArg Fin.val h;omega
  simp [hLM,hLR,hMR]

/-- The edit certificate needs only the three paid port exclusions.
The demoted and promoted records are automatically among those ports. -/
theorem bulk_transfer_iff_outside_three_ports {n a b rotationDepth subtreeDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (tree : BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) subtreeDepth tree)
    (separated : Separated node (2*a+1) (2*b+1))
    (oldRecord newRecord child : External n)
    (oldValue : oldRecord.val=2*a+1) (newValue : newRecord.val=2*b+1)
    (different : oldRecord≠newRecord)
    (oldRoot : subtreeOwner (Snapshot.ofTree before) (.node node.left node.right) occurrence.bounds.2=oldRecord)
    (newRoot : subtreeOwner (Snapshot.ofTree after) (.node node.left node.right) occurrence.bounds.2=newRecord)
    (oldParent : canonicalParent (Snapshot.ofTree before) tree child=some oldRecord)
    (notPorts : ∀ branch, child≠node.branchMin (Snapshot.ofTree before) branch) :
    canonicalParent (Snapshot.ofTree after) tree child=some newRecord ↔
      child.val<2*node.lower ∨ 2*node.upper<child.val := by
  have oldRoot' : node.owner (Snapshot.ofTree before)=oldRecord := oldRoot
  have newRoot' : node.owner (Snapshot.ofTree after)=newRecord := newRoot
  obtain ⟨⟨oldBranch,oldPort⟩,⟨newBranch,newPort⟩⟩ := junction_owners_are_ports step node separated
  rw [oldRoot'] at oldPort
  rw [newRoot'] at newPort
  have notA : child.val≠2*a+1 := by
    intro h
    have heq : child=oldRecord := Fin.ext (h.trans oldValue.symm)
    exact notPorts oldBranch (heq.trans oldPort.symm)
  have notB : child.val≠2*b+1 := by
    intro h
    have heq : child=newRecord := Fin.ext (h.trans newValue.symm)
    exact notPorts newBranch (heq.trans newPort.symm)
  exact bulk_transfer_iff_outside step tree node occurrence separated oldRecord newRecord child
    oldValue newValue different oldRoot newRoot oldParent notPorts notA notB

theorem rotation_endpoint_depths {lo hi a b depth : ℕ} {before after : BST lo hi}
    (step : KeyRotationAt a b depth before after) :
    lo≤a ∧ a<hi ∧ lo≤b ∧ b<hi ∧
      before.externalDepth (2*a+1)=depth ∧ before.externalDepth (2*b+1)=depth+1 ∧
      after.externalDepth (2*b+1)=depth ∧ after.externalDepth (2*a+1)=depth+1 := by
  induction step with
  | @right lo promoted demoted hi left middle right =>
      have hl := left.lower_le_upper
      have hm := middle.lower_le_upper
      have hr := right.lower_le_upper
      refine ⟨by omega,by omega,by omega,by omega,?_,?_,?_,?_⟩
      · simp
      · rw [externalDepth_node_of_lt_root _ _ (by omega),externalDepth_root]
      · simp
      · rw [externalDepth_node_of_root_lt _ _ (by omega),externalDepth_root]
  | @left lo demoted promoted hi left middle right =>
      have hl := left.lower_le_upper
      have hm := middle.lower_le_upper
      have hr := right.lower_le_upper
      refine ⟨by omega,by omega,by omega,by omega,?_,?_,?_,?_⟩
      · simp
      · rw [externalDepth_node_of_root_lt _ _ (by omega),externalDepth_root]
      · simp
      · rw [externalDepth_node_of_lt_root _ _ (by omega),externalDepth_root]
  | @leftContext a b depth lo root hi before after step right ih =>
      rcases ih with ⟨haLo,haHi,hbLo,hbHi,haOld,hbOld,hbNew,haNew⟩
      have hr := right.lower_le_upper
      refine ⟨haLo,by omega,hbLo,by omega,?_,?_,?_,?_⟩
      · rw [externalDepth_node_of_lt_root _ _ (by omega),haOld]
      · rw [externalDepth_node_of_lt_root _ _ (by omega),hbOld]
      · rw [externalDepth_node_of_lt_root _ _ (by omega),hbNew]
      · rw [externalDepth_node_of_lt_root _ _ (by omega),haNew]
  | @rightContext a b depth lo root hi left before after step ih =>
      rcases ih with ⟨haLo,haHi,hbLo,hbHi,haOld,hbOld,hbNew,haNew⟩
      have hl := left.lower_le_upper
      refine ⟨by omega,haHi,by omega,hbHi,?_,?_,?_,?_⟩
      · rw [externalDepth_node_of_root_lt _ _ (by omega),haOld]
      · rw [externalDepth_node_of_root_lt _ _ (by omega),hbOld]
      · rw [externalDepth_node_of_root_lt _ _ (by omega),hbNew]
      · rw [externalDepth_node_of_root_lt _ _ (by omega),haNew]

/-- If the old junction owner is the demoted record, its new owner is
forced to be the promoted record. This uses actual comparator depths,
not a supplied minimum-change choice. -/
theorem node_owner_forced_change {n a b rotationDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (node : AtNode n) (promotedRecord : External n)
    (promotedValue : promotedRecord.val=2*b+1)
    (promotedLo : node.wholeLower≤promotedRecord) (promotedHi : promotedRecord≤node.wholeUpper)
    (oldOwner : (node.owner (Snapshot.ofTree before)).val=2*a+1) :
    node.owner (Snapshot.ofTree after)=promotedRecord := by
  have data := rotation_endpoint_depths step
  rcases node_owner_changes step node with hsame | ⟨_,hnew⟩
  · have hnewOwner : (node.owner (Snapshot.ofTree after)).val=2*a+1 := by
      rw [←hsame];exact oldOwner
    have hmin := (node.owner_isMin (Snapshot.ofTree after)).2.2 promotedRecord promotedLo promotedHi
    change after.externalDepth (node.owner (Snapshot.ofTree after)).val ≤
      after.externalDepth promotedRecord.val at hmin
    rw [hnewOwner,promotedValue,data.2.2.2.2.2.2.2,data.2.2.2.2.2.2.1] at hmin
    omega
  · exact Fin.ext (hnew.trans promotedValue.symm)

#print axioms nonroot_children_stay_inside
#print axioms receiver_and_source_confined
#print axioms outside_source_child_transfers
#print axioms inside_junction_nonport_preserved
#print axioms exists_separated_junction
#print axioms bulk_transfer_iff_outside
#print axioms bulk_transfer_iff_outside_three_ports
#print axioms node_owner_forced_change

end GreedyMerge.ComparatorOuter
