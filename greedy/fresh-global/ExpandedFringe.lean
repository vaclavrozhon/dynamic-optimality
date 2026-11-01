import AccessConsolidation

/-!
Static substitution of actual old gap subtrees into the canonical atom
projection. Projected consolidation edges are identified with concrete
canonical light edges of the fully expanded real-key tree.
-/
namespace GreedyMerge.ExpandedFringe
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.PathPlateau GreedyMerge.AccessFrontier GreedyMerge.AccessConsolidation
open GreedyMerge.IntervalRootOracle GreedyMerge.PlateauBridge
open GreedyMerge.OrderedAtoms GreedyMerge.ExpansionRotations
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule

/-- A minimum in an ordered contraction is a minimum after expanding all
of its atoms; the rank of each representative is its actual record rank. -/
theorem ordered_min_expands {rank cut representative : ℕ → ℕ}
    {count lo hi minimum : ℕ} (cutOrder : StrictMono cut)
    (owners : AtomOwners rank cut representative count)
    (bound : hi < count)
    (minimumSpec : Splay.Tree.IsIntervalMin (fun atom => rank (representative atom))
      lo hi minimum) :
    Splay.Tree.IsIntervalMin rank (cut lo) (cut (hi+1)-1) (representative minimum) := by
  have inside := owner_inside_range cutOrder owners minimumSpec.1 minimumSpec.2.1 bound
  refine ⟨inside.1, by omega, ?_⟩
  intro record lower upper
  have recordUpper : record < cut (hi+1) := by
    have positive := cutOrder (by omega : 0 < hi+1)
    omega
  have indexRange := locate_range cut cutOrder lower recordUpper
  have zeroLower := cutOrder.monotone (Nat.zero_le lo)
  have localRange := locate_bounds cut cutOrder (by omega : cut 0 ≤ record)
  have atomMin := owners (locate cut cutOrder record) (by omega)
  exact (minimumSpec.2.2 _ indexRange.1 indexRange.2).trans
    (atomMin.1.2.2 record localRange.1 (by omega))

theorem expanded_owner_value {n access lo hi : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner owner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (skeleton : BST lo hi) (bound : hi ≤ p.count)
    (projection : Projection
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner skeleton)
    (upper : p.separator hi ≤ n) :
    (subtreeOwner (Snapshot.ofTree comparator) (Expand 0 p.separator p.gaps skeleton) upper).val =
      AtomOwner p.separator gapOwner (treeOwner owner skeleton) := by
  have atomMin := treeOwner_min _ owner skeleton projection
  have fullMin := ordered_min_expands (cut_strictMono 0 p.separator p.gaps)
    (gap_owners_are_atom_owners minima) (by omega : 2*hi < 2*p.count+1) atomMin.1
  rw [cut_even, cut_odd] at fullMin
  simp only [Nat.add_sub_cancel] at fullMin
  let record : External n := ⟨AtomOwner p.separator gapOwner (treeOwner owner skeleton),
    by have := fullMin.2.1; omega⟩
  have spec : Splay.Rank.IsIntervalMin (Snapshot.ofTree comparator).rank
      (subtreeLower (Expand 0 p.separator p.gaps skeleton) upper)
      (subtreeUpper (Expand 0 p.separator p.gaps skeleton) upper) record := by
    refine ⟨fullMin.1, fullMin.2.1, ?_⟩
    intro other lower upper
    exact fullMin.2.2 other.val lower upper
  have equal := (Snapshot.ofTree comparator).intervalMin_unique _ _
    (subtree_nonempty (Expand 0 p.separator p.gaps skeleton) upper) spec
  exact (congrArg Fin.val equal).symm

def HasPair {n lo hi : ℕ} (snapshot : Snapshot n) (tree : BST lo hi)
    (upper : hi ≤ n) (depth parent child : ℕ) : Prop :=
  ∃ edge ∈ treeEdges snapshot tree upper depth,
    edge.owner.val = parent ∧ edge.child.val = child

/-- Every atom-projection edge occurs as an actual light edge after full
gap substitution, including its concrete real/null record identities. -/
theorem projection_edge_expands {n access lo hi : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner owner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (skeleton : BST lo hi) (bound : hi ≤ p.count)
    (projection : Projection
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner skeleton)
    (localOwners : LocalOwners
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner lo hi)
    (upper : p.separator hi ≤ n) (depth parent child : ℕ)
    (member : (parent,child) ∈ edges owner skeleton) :
    HasPair (Snapshot.ofTree comparator) (Expand 0 p.separator p.gaps skeleton) upper depth
      (AtomOwner p.separator gapOwner parent) (AtomOwner p.separator gapOwner child) := by
  induction skeleton generalizing depth with
  | empty => simp [edges] at member
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have rootUpper : p.separator root ≤ n :=
        (p.increasing.monotone (by omega : root ≤ hi)).trans upper
      let actualLeft := Expand 0 p.separator p.gaps left
      let actualRight := Expand 0 p.separator p.gaps right
      let node : AtNode n := ⟨GapLower 0 p.separator lo, p.separator root,
        p.separator hi, actualLeft, actualRight, upper⟩
      have leftLoc : LocalOwners
          (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner lo root := by
        intro q lower higher
        exact localOwners q lower (by omega)
      have rightLoc : LocalOwners
          (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner (root+1) hi := by
        intro q lower higher
        exact localOwners q (by omega) higher
      simp only [edges, List.mem_append] at member
      rcases member with (leftMember | rightMember) | localMember
      · obtain ⟨edge, edgeMember, parentEq, childEq⟩ :=
          ihLeft (by omega) projection.2.1 leftLoc rootUpper (depth+1) leftMember
        refine ⟨edge, ?_, parentEq, childEq⟩
        change edge ∈ edgesAtNode (Snapshot.ofTree comparator) node depth ++
          treeEdges (Snapshot.ofTree comparator) actualLeft rootUpper (depth+1) ++
          treeEdges (Snapshot.ofTree comparator) actualRight upper (depth+1)
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr edgeMember)))
      · obtain ⟨edge, edgeMember, parentEq, childEq⟩ :=
          ihRight bound projection.2.2 rightLoc upper (depth+1) rightMember
        refine ⟨edge, ?_, parentEq, childEq⟩
        change edge ∈ edgesAtNode (Snapshot.ofTree comparator) node depth ++
          treeEdges (Snapshot.ofTree comparator) actualLeft rootUpper (depth+1) ++
          treeEdges (Snapshot.ofTree comparator) actualRight upper (depth+1)
        exact List.mem_append.mpr (Or.inr edgeMember)
      · obtain ⟨localChild, localChildMember, pairEq⟩ := List.mem_map.mp localMember
        have parentEq : owner root = parent := (Prod.mk.inj pairEq).1
        have childEq : localChild = child := (Prod.mk.inj pairEq).2
        subst parent
        subst localChild
        have ownerValue := expanded_owner_value comparator p gapOwner owner minima
          (.node left right) bound projection upper
        change (node.owner (Snapshot.ofTree comparator)).val =
          AtomOwner p.separator gapOwner (owner root) at ownerValue
        have leftValue := expanded_owner_value comparator p gapOwner owner minima
          left (by omega) projection.2.1 rootUpper
        have rightValue := expanded_owner_value comparator p gapOwner owner minima
          right bound projection.2.2 upper
        have localSpec := List.mem_filter.mp localChildMember
        have childDifferent : child ≠ owner root := by simpa only [bne_iff_ne] using localSpec.2
        have childIn := localSpec.1
        change child ∈ [treeOwner owner left, 2*root+1, treeOwner owner right] at childIn
        have childBounds : 2*lo ≤ child ∧ child ≤ 2*hi := by
          have leftBounds := treeOwner_bounds _ owner left projection.2.1
          have rightBounds := treeOwner_bounds _ owner right projection.2.2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at childIn
          rcases childIn with rfl | rfl | rfl <;> omega
        have strict := projection.1.2 child childBounds.1 childBounds.2 childDifferent
        dsimp only at strict
        have newChildDifferent : AtomOwner p.separator gapOwner child ≠
            (node.owner (Snapshot.ofTree comparator)).val := by
          rw [ownerValue]
          intro equal
          rw [equal] at strict
          exact Nat.lt_irrefl _ strict
        have ports : AtomOwner p.separator gapOwner child =
              (node.branchMin (Snapshot.ofTree comparator) .left).val ∨
            AtomOwner p.separator gapOwner child = 2*node.root+1 ∨
            AtomOwner p.separator gapOwner child =
              (node.branchMin (Snapshot.ofTree comparator) .right).val := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at childIn
          rcases childIn with equal | equal | equal
          · left
            change AtomOwner p.separator gapOwner child =
              (subtreeOwner (Snapshot.ofTree comparator) actualLeft rootUpper).val
            rw [equal, leftValue]
          · exact Or.inr (Or.inl (by rw [equal, owner_odd]))
          · right; right
            change AtomOwner p.separator gapOwner child =
              (subtreeOwner (Snapshot.ofTree comparator) actualRight upper).val
            rw [equal, rightValue]
        obtain ⟨edge, edgeMember, actualParent, actualChild⟩ :=
          (local_child_iff (Snapshot.ofTree comparator) node depth
            (node.owner (Snapshot.ofTree comparator)) rfl _).2 ⟨newChildDifferent, ports⟩
        refine ⟨edge, ?_, (congrArg Fin.val actualParent).trans ownerValue, actualChild⟩
        change edge ∈ edgesAtNode (Snapshot.ofTree comparator) node depth ++
          treeEdges (Snapshot.ofTree comparator) actualLeft rootUpper (depth+1) ++
          treeEdges (Snapshot.ofTree comparator) actualRight upper (depth+1)
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl edgeMember)))

theorem hasPair_castUpper {n lo hi finish : ℕ} (snapshot : Snapshot n)
    (equal : hi = finish) (tree : BST lo hi) (upper : hi ≤ n) (upper' : finish ≤ n)
    (depth parent child : ℕ) :
    HasPair snapshot (GreedyMerge.PathPlateau.castUpper equal tree) upper' depth parent child ↔
      HasPair snapshot tree upper depth parent child := by
  cases equal
  rfl

/-- Every event of the concrete two-sided schedule installs its prescribed
edge of the actual raised canonical heap, after all original gap interiors
are restored. The expansion equality is supplied by the actual-surface
theorem `canonical_after_raise_is_expansion`. -/
theorem scheduled_edge_in_new_tree {n access root : ℕ} (comparator oldTree newTree : BST 0 n)
    (p : Decomposition oldTree access) (gapOwner owner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (left : BST 0 root) (right : BST (root+1) p.count)
    (projection : Projection
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner (.node left right))
    (localOwners : LocalOwners
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner 0 p.count)
    (expansion : newTree = p.expand (.node left right)) (parent child : ℕ)
    (member : (parent,child) ∈ (schedule owner left ++ schedule owner right).map
      (fun event => (AtomOwner p.separator gapOwner event.1, AtomOwner p.separator gapOwner event.2))) :
    HasPair (Snapshot.ofTree comparator) newTree (Nat.le_refl n) 0 parent child := by
  obtain ⟨event, eventMember, mapped⟩ := List.mem_map.mp member
  have rootBound := right.lower_le_upper
  have edgeMember : event ∈ edges owner (.node left right) := by
    rcases List.mem_append.mp eventMember with first | second
    · have edge := (schedule_perm_edges _ owner left projection.2.1
        (by intro q hq hqu; exact localOwners q hq (by omega))).mem_iff.mp first
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl edge)))
    · have edge := (schedule_perm_edges _ owner right projection.2.2
        (by intro q hq hqu; exact localOwners q (by omega) hqu)).mem_iff.mp second
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr edge)))
  have actual := projection_edge_expands comparator p gapOwner owner minima
    (.node left right) (Nat.le_refl p.count) projection localOwners
    (by rw [p.endpoint]) 0 event.1 event.2 edgeMember
  have parentEq := (Prod.mk.inj mapped).1
  have childEq := (Prod.mk.inj mapped).2
  rw [parentEq, childEq] at actual
  rw [expansion]
  exact (hasPair_castUpper (Snapshot.ofTree comparator) p.endpoint _ _ (Nat.le_refl n)
    0 parent child).2 actual

end GreedyMerge.ExpandedFringe

#print axioms GreedyMerge.ExpandedFringe.expanded_owner_value
#print axioms GreedyMerge.ExpandedFringe.projection_edge_expands
#print axioms GreedyMerge.ExpandedFringe.scheduled_edge_in_new_tree
