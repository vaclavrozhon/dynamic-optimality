import InheritedGapEdges

namespace GreedyMerge.AccessSurvivors
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.AccessFrontier GreedyMerge.ExpandedFringe GreedyMerge.PathPlateau
open GreedyMerge.ExpansionRotations GreedyMerge.PlateauBridge GreedyMerge.IntervalRootOracle
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule

theorem hasChild_iff_hasPair {n lo hi : ℕ} (snapshot : Snapshot n) (tree : BST lo hi)
    (upper : hi ≤ n) (depth : ℕ) (owner : External n) (child : ℕ) :
    HasChild snapshot tree upper depth owner child ↔
      HasPair snapshot tree upper depth owner.val child := by
  constructor
  · rintro ⟨edge,member,parent,key⟩
    exact ⟨edge,member,congrArg Fin.val parent,key⟩
  · rintro ⟨edge,member,parent,key⟩
    exact ⟨edge,member,Fin.ext parent,key⟩

/-- Once the accessed real key is the ordinary BST root, its canonical
heap children are exactly the minima of the two literal child subtrees. -/
theorem root_children_zero {n lo root hi : ℕ} (snapshot : Snapshot n)
    (left : BST lo root) (right : BST (root+1) hi) (upper : hi ≤ n)
    (record : External n) (real : record.val=2*root+1) (zero : snapshot.rank record=0)
    (depth child : ℕ) :
    HasChild snapshot (.node left right) upper depth record child ↔
      child=(subtreeOwner snapshot left (by have := right.lower_le_upper; omega)).val ∨
      child=(subtreeOwner snapshot right upper).val := by
  have leftBound := left.lower_le_upper
  have rightBound := right.lower_le_upper
  have rootUpper : root ≤ n := by omega
  let node : AtNode n := ⟨lo,root,hi,left,right,upper⟩
  have owner : node.owner snapshot=record :=
    owner_eq_of_zero snapshot (.node left right) upper record zero (by omega)
  have noLeft := no_child_outside snapshot left rootUpper (depth+1) record
    (Or.inr (by omega)) child
  have noRight := no_child_outside snapshot right upper (depth+1) record
    (Or.inl (by omega)) child
  rw [hasChild_node_iff]
  rw [local_child_iff snapshot node depth record owner child]
  simp only [noLeft,noRight,or_false]
  change (child ≠ record.val ∧
    (child=(subtreeOwner snapshot left rootUpper).val ∨
      child=2*root+1 ∨ child=(subtreeOwner snapshot right upper).val)) ↔ _
  have leftInside := subtreeOwner_bounds snapshot left rootUpper
  have rightInside := subtreeOwner_bounds snapshot right upper
  constructor
  · rintro ⟨different,alternatives⟩
    rcases alternatives with first | middle | last
    · exact Or.inl first
    · omega
    · exact Or.inr last
  · intro alternatives
    refine ⟨?_,?_⟩
    · rcases alternatives with first | last <;> omega
    · rcases alternatives with first | last
      · exact Or.inl first
      · exact Or.inr (Or.inr last)

/-- Both survivors of the actual two-sided consolidation retain exactly
the access record as parent in the new canonical heap. This characterizes
all new root children, rather than only constructing two candidate edges. -/
theorem expanded_root_children {n access root : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner owner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (left : BST 0 root) (right : BST (root+1) p.count)
    (projection : Projection
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner (.node left right))
    (atAccess : p.separator root=access) (record : External n)
    (real : record.val=2*access+1) (zero : (Snapshot.ofTree comparator).rank record=0)
    (child : ℕ) :
    HasPair (Snapshot.ofTree comparator) (p.expand (.node left right)) (Nat.le_refl n) 0 record.val child ↔
      child=AtomOwner p.separator gapOwner (treeOwner owner left) ∨
      child=AtomOwner p.separator gapOwner (treeOwner owner right) := by
  have rootBound := right.lower_le_upper
  have topUpper : p.separator p.count ≤ n := by rw [p.endpoint]
  have rootUpper : p.separator root ≤ n := (p.increasing.monotone (by omega : root ≤ p.count)).trans topUpper
  have fact := root_children_zero (Snapshot.ofTree comparator)
    (Expand 0 p.separator p.gaps left) (Expand 0 p.separator p.gaps right) topUpper record
    (by simpa only [atAccess] using real) zero 0 child
  rw [hasChild_iff_hasPair] at fact
  erw [expanded_owner_value comparator p gapOwner owner minima left (by omega) projection.2.1 rootUpper,
    expanded_owner_value comparator p gapOwner owner minima right (Nat.le_refl p.count) projection.2.2 topUpper] at fact
  change HasPair (Snapshot.ofTree comparator)
    (castUpper p.endpoint (Expand 0 p.separator p.gaps (.node left right))) _ _ _ _ ↔ _
  rw [hasPair_castUpper (Snapshot.ofTree comparator) p.endpoint _ topUpper (Nat.le_refl n) 0 record.val child]
  exact fact

end GreedyMerge.AccessSurvivors

#print axioms GreedyMerge.AccessSurvivors.expanded_root_children
