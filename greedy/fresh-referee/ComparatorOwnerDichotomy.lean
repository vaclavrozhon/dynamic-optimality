import ComparatorOuterSegments

/-!
A literal fork with unchanged owner forces every canonical heap parent to
stay unchanged. Combined with the actual fork-existence theorem, this
closes the missing structural branch of universal comparator administration.
-/
namespace GreedyMerge.ComparatorOuter

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.ComparatorHeap

theorem separated_interval_minimal {n lo hi a b depth : ℕ} (node : AtNode n)
    {tree : BST lo hi} (occurrence : SubtreeAt (.node node.left node.right) depth tree)
    (separated : Separated node a b)
    (aLo : 2*node.lower ≤ a) (aHi : a ≤ 2*node.upper)
    (bLo : 2*node.lower ≤ b) (bHi : b ≤ 2*node.upper)
    {otherLo otherHi otherDepth : ℕ} {other : BST otherLo otherHi}
    (otherOccurrence : SubtreeAt other otherDepth tree)
    (otherALo : 2*otherLo ≤ a) (otherAHi : a ≤ 2*otherHi)
    (otherBLo : 2*otherLo ≤ b) (otherBHi : b ≤ 2*otherHi) :
    otherLo ≤ node.lower ∧ node.upper ≤ otherHi := by
  induction occurrence generalizing otherLo otherHi otherDepth with
  | here =>
      cases otherOccurrence with
      | here => exact ⟨le_refl _,le_refl _⟩
      | left inside right =>
          have bounds := inside.bounds
          have excluded := separated TernaryBranch.left
          simp only [TernaryBranch.Contains] at excluded
          omega
      | right left inside =>
          have bounds := inside.bounds
          have excluded := separated TernaryBranch.right
          simp only [TernaryBranch.Contains] at excluded
          omega
  | @left lo root hi depth left occurrence right ih =>
      cases otherOccurrence with
      | here =>
          have bounds := occurrence.bounds
          have order := right.lower_le_upper
          omega
      | left inside right => exact ih inside otherALo otherAHi otherBLo otherBHi
      | right left inside =>
          have one := occurrence.bounds
          have two := inside.bounds
          omega
  | @right lo root hi depth left right occurrence ih =>
      cases otherOccurrence with
      | here =>
          have bounds := occurrence.bounds
          have order := left.lower_le_upper
          omega
      | left inside right =>
          have one := occurrence.bounds
          have two := inside.bounds
          omega
      | right left inside => exact ih inside otherALo otherAHi otherBLo otherBHi

theorem subtreeOwner_restrict {n smallLo smallHi largeLo largeHi : ℕ}
    (snapshot : Snapshot n) (small : BST smallLo smallHi) (large : BST largeLo largeHi)
    (smallBound : smallHi ≤ n) (largeBound : largeHi ≤ n)
    (lower : largeLo ≤ smallLo) (upper : smallHi ≤ largeHi)
    (ownerLo : 2*smallLo ≤ (subtreeOwner snapshot large largeBound).val)
    (ownerHi : (subtreeOwner snapshot large largeBound).val ≤ 2*smallHi) :
    subtreeOwner snapshot large largeBound = subtreeOwner snapshot small smallBound := by
  apply snapshot.intervalMin_unique
  refine ⟨ownerLo,ownerHi,?_⟩
  intro record lo hi
  apply (subtreeOwner_isMin snapshot large largeBound).2.2 record
  · change 2*largeLo ≤ record.val
    change 2*smallLo ≤ record.val at lo
    omega
  · change record.val ≤ 2*largeHi
    change record.val ≤ 2*smallHi at hi
    omega

theorem unchanged_fork_all_owners {n a b rotationDepth forkDepth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b rotationDepth before after) (tree : BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) forkDepth tree)
    (separated : Separated node (2*a+1) (2*b+1))
    (aLo : 2*node.lower ≤ 2*a+1) (aHi : 2*a+1 ≤ 2*node.upper)
    (bLo : 2*node.lower ≤ 2*b+1) (bHi : 2*b+1 ≤ 2*node.upper)
    (unchanged : node.owner (Snapshot.ofTree before)=node.owner (Snapshot.ofTree after))
    {lo hi depth : ℕ} (inner : BST lo hi) (innerOccurrence : SubtreeAt inner depth tree) :
    subtreeOwner (Snapshot.ofTree before) inner innerOccurrence.bounds.2 =
      subtreeOwner (Snapshot.ofTree after) inner innerOccurrence.bounds.2 := by
  have changes := snapshot_min_changes step (subtreeLower inner innerOccurrence.bounds.2)
    (subtreeUpper inner innerOccurrence.bounds.2) (subtree_nonempty inner innerOccurrence.bounds.2)
  rcases changes with same | ⟨oldValue,newValue⟩
  · exact same
  · have oldMin := subtreeOwner_isMin (Snapshot.ofTree before) inner innerOccurrence.bounds.2
    have newMin := subtreeOwner_isMin (Snapshot.ofTree after) inner innerOccurrence.bounds.2
    change (subtreeOwner (Snapshot.ofTree before) inner innerOccurrence.bounds.2).val = _ at oldValue
    change (subtreeOwner (Snapshot.ofTree after) inner innerOccurrence.bounds.2).val = _ at newValue
    have containsA : 2*lo ≤ 2*a+1 ∧ 2*a+1 ≤ 2*hi := by
      have lower : 2*lo ≤ (subtreeOwner (Snapshot.ofTree before) inner innerOccurrence.bounds.2).val := oldMin.1
      have upper : (subtreeOwner (Snapshot.ofTree before) inner innerOccurrence.bounds.2).val ≤ 2*hi := oldMin.2.1
      simpa only [oldValue] using And.intro lower upper
    have containsB : 2*lo ≤ 2*b+1 ∧ 2*b+1 ≤ 2*hi := by
      have lower : 2*lo ≤ (subtreeOwner (Snapshot.ofTree after) inner innerOccurrence.bounds.2).val := newMin.1
      have upper : (subtreeOwner (Snapshot.ofTree after) inner innerOccurrence.bounds.2).val ≤ 2*hi := newMin.2.1
      simpa only [newValue] using And.intro lower upper
    have inside := separated_interval_minimal node occurrence separated aLo aHi bLo bHi
      innerOccurrence containsA.1 containsA.2 containsB.1 containsB.2
    have oldRestricted := subtreeOwner_restrict (Snapshot.ofTree before) (.node node.left node.right) inner
      occurrence.bounds.2 innerOccurrence.bounds.2 inside.1 inside.2
      (by simpa only [oldValue] using aLo) (by simpa only [oldValue] using aHi)
    have newRestricted := subtreeOwner_restrict (Snapshot.ofTree after) (.node node.left node.right) inner
      occurrence.bounds.2 innerOccurrence.bounds.2 inside.1 inside.2
      (by simpa only [newValue] using bLo) (by simpa only [newValue] using bHi)
    exact oldRestricted.trans (unchanged.trans newRestricted.symm)

theorem heavyBranch_eq_of_owner_eq {n : ℕ} (oldSnap newSnap : Snapshot n) (node : AtNode n)
    (same : node.owner oldSnap=node.owner newSnap) : node.heavyBranch oldSnap=node.heavyBranch newSnap := by
  have oldBranch := node.owner_in_heavyBranch oldSnap
  have newBranch := node.owner_in_heavyBranch newSnap
  rw [same] at oldBranch
  cases oldEq : node.heavyBranch oldSnap <;> cases newEq : node.heavyBranch newSnap <;>
    simp only [oldEq,newEq,TernaryBranch.Contains] at oldBranch newBranch <;> first | rfl | omega

theorem edgesAtNode_eq_of_minima_eq {n : ℕ} (oldSnap newSnap : Snapshot n) (node : AtNode n) (depth : ℕ)
    (owner : node.owner oldSnap=node.owner newSnap)
    (branches : ∀ branch, node.branchMin oldSnap branch=node.branchMin newSnap branch) :
    edgesAtNode oldSnap node depth=edgesAtNode newSnap node depth := by
  have heavy := heavyBranch_eq_of_owner_eq oldSnap newSnap node owner
  simp only [edgesAtNode,lightBranches,heavy]
  congr 1
  funext branch
  simp only [edgeFor,owner,branches]

theorem treeEdges_eq_of_owners_eq {n lo hi : ℕ} (oldSnap newSnap : Snapshot n)
    (tree : BST lo hi) (bound : hi ≤ n)
    (owners : ∀ {innerLo innerHi depth : ℕ} (inner : BST innerLo innerHi)
      (occurrence : SubtreeAt inner depth tree),
      subtreeOwner oldSnap inner (le_trans occurrence.bounds.2 bound)=
        subtreeOwner newSnap inner (le_trans occurrence.bounds.2 bound)) (depth : ℕ) :
    treeEdges oldSnap tree bound depth=treeEdges newSnap tree bound depth := by
  induction tree generalizing depth with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      have boundLeft : root ≤ n := by have := right.lower_le_upper; omega
      have nodeEdges := edgesAtNode_eq_of_minima_eq oldSnap newSnap ⟨lo,root,hi,left,right,bound⟩ depth
        (owners (.node left right) SubtreeAt.here) (by
          intro branch
          cases branch with
          | left => exact owners left (SubtreeAt.left SubtreeAt.here right)
          | right => exact owners right (SubtreeAt.right left SubtreeAt.here)
          | middle =>
              apply Fin.ext
              have one := (AtNode.mk lo root hi left right bound).branchMin_in_branch oldSnap .middle
              have two := (AtNode.mk lo root hi left right bound).branchMin_in_branch newSnap .middle
              simp only [TernaryBranch.Contains] at one two
              omega)
      simp only [treeEdges]
      rw [nodeEdges]
      rw [ihLeft boundLeft (fun inner occurrence => owners inner (occurrence.left right))]
      rw [ihRight bound (fun inner occurrence => owners inner (SubtreeAt.right left occurrence))]

theorem parents_eq_of_owners_eq {n : ℕ} (oldSnap newSnap : Snapshot n) (tree : BST 0 n)
    (owners : ∀ {lo hi depth : ℕ} (inner : BST lo hi) (occurrence : SubtreeAt inner depth tree),
      subtreeOwner oldSnap inner occurrence.bounds.2=subtreeOwner newSnap inner occurrence.bounds.2)
    (record : External n) : canonicalParent newSnap tree record=canonicalParent oldSnap tree record := by
  have edges := treeEdges_eq_of_owners_eq oldSnap newSnap tree (le_refl n) owners 0
  have roots : canonicalRoot oldSnap tree=canonicalRoot newSnap tree := owners tree SubtreeAt.here
  cases parent : canonicalParent oldSnap tree record with
  | none =>
      have oldRoot := (canonicalParent_eq_none_iff oldSnap tree record).mp parent
      exact (canonicalParent_eq_none_iff newSnap tree record).mpr (oldRoot.trans roots)
  | some owner =>
      simp only [canonicalParent,Option.map_eq_some_iff] at parent
      obtain ⟨edge,lookup,equal⟩ := parent
      have spec := incomingEdge?_some_mem oldSnap tree lookup
      have newMember : edge ∈ fullEdges newSnap tree := by
        change edge ∈ treeEdges newSnap tree (le_refl n) 0
        rw [←edges]
        exact spec.1
      have newParent := parent_of_fullEdge newSnap tree edge newMember
      simpa only [spec.2,equal] using newParent

theorem unchanged_fork_all_parents {n a b rotationDepth forkDepth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b rotationDepth before after) (tree : BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) forkDepth tree)
    (separated : Separated node (2*a+1) (2*b+1))
    (aLo : 2*node.lower ≤ 2*a+1) (aHi : 2*a+1 ≤ 2*node.upper)
    (bLo : 2*node.lower ≤ 2*b+1) (bHi : 2*b+1 ≤ 2*node.upper)
    (unchanged : node.owner (Snapshot.ofTree before)=node.owner (Snapshot.ofTree after)) :
    ∀ record, canonicalParent (Snapshot.ofTree after) tree record=canonicalParent (Snapshot.ofTree before) tree record := by
  apply parents_eq_of_owners_eq
  exact unchanged_fork_all_owners step tree node occurrence separated aLo aHi bLo bHi unchanged

/-- Geometric certificate of the only possible changed fork. The owner
identities are read from the actual comparator minima. -/
structure ChangedJunction {n : ℕ} (before after tree : BST 0 n) (a b : ℕ) where
  node : AtNode n
  depth : ℕ
  occurrence : SubtreeAt (.node node.left node.right) depth tree
  separated : Separated node (2*a+1) (2*b+1)
  oldValue : (node.owner (Snapshot.ofTree before)).val=2*a+1
  newValue : (node.owner (Snapshot.ofTree after)).val=2*b+1
  different : node.owner (Snapshot.ofTree before)≠node.owner (Snapshot.ofTree after)

inductive RotationPlan {n : ℕ} (before after tree : BST 0 n) (a b : ℕ) where
  | quiet (parents : ∀ record, canonicalParent (Snapshot.ofTree after) tree record=
      canonicalParent (Snapshot.ofTree before) tree record)
  | junction (certificate : ChangedJunction before after tree a b)

/-- The actual comparator rotation supplies a complete case certificate;
there is no assumed junction, parent-support set, or administration budget. -/
theorem rotationPlan_nonempty {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (tree : BST 0 n) :
    Nonempty (RotationPlan before after tree a b) := by
  obtain ⟨aLo,aHi,bLo,bHi,aOld,bOld,bNew,aNew⟩ := rotation_endpoint_depths step
  let oldRecord : External n := ⟨2*a+1,by omega⟩
  let newRecord : External n := ⟨2*b+1,by omega⟩
  have different : oldRecord≠newRecord := by
    intro equal
    have keyEqual := congrArg Fin.val equal
    change 2*a+1=2*b+1 at keyEqual
    rw [keyEqual] at aOld
    omega
  obtain ⟨node,forkDepth,occurrence,nodeALo,nodeAHi,nodeBLo,nodeBHi,separated⟩ :=
    exists_separated_junction tree (le_refl n) oldRecord newRecord (by omega) (by dsimp [oldRecord];omega)
      (by omega) (by dsimp [newRecord];omega) different
  by_cases same : node.owner (Snapshot.ofTree before)=node.owner (Snapshot.ofTree after)
  · exact ⟨.quiet (unchanged_fork_all_parents step tree node occurrence separated
      nodeALo nodeAHi nodeBLo nodeBHi same)⟩
  · rcases node_owner_changes step node with impossible | ⟨oldValue,newValue⟩
    · exact False.elim (same impossible)
    · exact ⟨.junction ⟨node,forkDepth,occurrence,separated,oldValue,newValue,same⟩⟩

noncomputable def rotationPlan {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (tree : BST 0 n) :
    RotationPlan before after tree a b := Classical.choice (rotationPlan_nonempty step tree)

#print axioms separated_interval_minimal
#print axioms unchanged_fork_all_owners
#print axioms unchanged_fork_all_parents
#print axioms rotationPlan_nonempty

end GreedyMerge.ComparatorOuter
