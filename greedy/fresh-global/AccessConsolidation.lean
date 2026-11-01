import AccessFrontier
import FringeSchedule

/-!
Actual surface accesses supply the atom projection and the explicit legal
consolidation schedule. All atom minima and owners are constructed from the
ordinary comparator and the extracted old search-path gaps.
-/
namespace GreedyMerge.AccessConsolidation
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.SearchGaps GreedyMerge.PathPlateau GreedyMerge.AccessFrontier
open GreedyMerge.IntervalRootOracle GreedyMerge.PlateauBridge
open GreedyMerge.OrderedAtoms GreedyMerge.ExpansionRotations
open GreedyMerge.ComparatorAtoms GreedyMerge.Fringe GreedyMerge.Fringe.Schedule

theorem atom_interval_min_exists {n access lo hi : ℕ} (comparator : BST 0 n)
    {tree : BST 0 n} (p : Decomposition tree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (order : lo ≤ hi) (bound : hi ≤ 2*p.count) :
    ∃ owner, UniqueMin (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom))
      lo hi owner := by
  have cutOrder := cut_strictMono 0 p.separator p.gaps
  have cutUpper := cutOrder.monotone (by omega : hi+1 ≤ 2*p.count+1)
  rw [cut_odd, p.endpoint] at cutUpper
  have cutNonempty := cutOrder (by omega : lo < hi+1)
  obtain ⟨record, minimum⟩ := exists_uniqueMin_external comparator
    (Nat.zero_le (Cut 0 p.separator lo))
    (by omega : Cut 0 p.separator lo ≤ Cut 0 p.separator (hi+1)-1)
    (by omega : Cut 0 p.separator (hi+1)-1 ≤ 2*n)
  exact ⟨_, contract_min cutOrder (gap_owners_are_atom_owners minima)
    order (by omega) minimum⟩

theorem atom_intervals_unique {n access : ℕ} (comparator : BST 0 n)
    {tree : BST 0 n} (p : Decomposition tree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i)) :
    UniqueIntervals (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom))
      0 (2*p.count) := by
  intro lo hi first second _ upper hfirst hsecond
  obtain ⟨owner, minimum⟩ := atom_interval_min_exists (lo := lo) (hi := hi) comparator p gapOwner minima
    (by have := hfirst.1; have := hfirst.2.1; omega) upper
  exact (GreedyMerge.SharpProjection.eq_of_isMin minimum hfirst).trans
    (GreedyMerge.SharpProjection.eq_of_isMin minimum hsecond).symm

theorem canonical_cartesian {lo hi : ℕ} (rank : ℕ → ℕ) (tree : BST lo hi)
    (canonical : GreedyMerge.IntervalRootOracle.Canonical rank tree) :
    GreedyMerge.Plateau.Cartesian (GreedyMerge.Plateau.Priority rank) tree := by
  induction tree with
  | empty => trivial
  | node left right ihLeft ihRight =>
      exact ⟨canonical.1.2.2.1, ihLeft canonical.2.1, ihRight canonical.2.2⟩

/-- The exact local and full atom owners are extracted from the actual
comparator; no projection or forest-shape assertion is supplied. -/
theorem actual_projection_exists {n access : ℕ} (comparator : BST 0 n)
    {tree : BST 0 n} (p : Decomposition tree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (skeleton : BST 0 p.count)
    (canonical : GreedyMerge.IntervalRootOracle.Canonical
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) skeleton) :
    ∃ owner, LocalOwners
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner 0 p.count ∧
      Projection (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom))
        owner skeleton := by
  classical
  have existsLocal : ∀ q, q < p.count → ∃ owner,
      UniqueMin (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom))
        (2*q) (2*q+2) owner := by
    intro q hq
    exact atom_interval_min_exists comparator p gapOwner minima (by omega) (by omega)
  let owner := fun q => if hq : q < p.count then Classical.choose (existsLocal q hq) else 0
  have localOwners : LocalOwners
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner 0 p.count := by
    intro q _ hq
    dsimp only [owner]
    rw [dif_pos hq]
    exact Classical.choose_spec (existsLocal q hq)
  exact ⟨owner, localOwners,
    projection_of_cartesian _ owner skeleton (canonical_cartesian _ skeleton canonical)
      localOwners (atom_intervals_unique comparator p gapOwner minima)⟩

theorem access_mem_path {lo hi access : ℕ} (tree : BST lo hi)
    (lower : lo ≤ access) (upper : access < hi) : access ∈ PathKeys access tree := by
  induction tree with
  | empty => omega
  | @node lo root hi left right ihLeft ihRight =>
      simp only [PathKeys]
      split_ifs with equal goLeft
      · simp [equal]
      · exact Finset.mem_insert_of_mem (ihLeft lower goLeft)
      · exact Finset.mem_insert_of_mem (ihRight (by omega) upper)

theorem skeleton_root_is_access {n access root : ℕ} (comparator : BST 0 n)
    {tree : BST 0 n} (p : Decomposition tree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (left : BST 0 root) (right : BST (root+1) p.count)
    (canonical : GreedyMerge.IntervalRootOracle.Canonical
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) (.node left right))
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access) :
    p.separator root = access := by
  obtain ⟨index, indexBound, indexEq⟩ := p.complete access
    (access_mem_path tree (Nat.zero_le access) global.1)
  let ranks := fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)
  have minimum : Splay.Tree.IsIntervalMin ranks 0 (2*p.count) (2*index+1) := by
    refine ⟨Nat.zero_le _, by omega, ?_⟩
    intro other _ _
    change comparator.externalDepth (AtomOwner p.separator gapOwner (2*index+1)) ≤ _
    rw [owner_odd, ← indexEq, comparator_zero_of_global comparator global]
    exact Nat.zero_le _
  have unique := unique_of_min minimum (by
    intro first second hf hs
    exact atom_intervals_unique comparator p gapOwner minima 0 (2*p.count) first second
      (Nat.zero_le _) (Nat.le_refl _) hf hs)
  have position := GreedyMerge.ProjectionRotation.root_of_min canonical unique
  have rootEq : root = index := by
    unfold leftPort at position
    omega
  simpa only [rootEq] using indexEq.symm

/-- Rank-preserving renaming sends a literal adjacent-root link to a
literal link of actual records. Injectivity is unnecessary for this local
lemma because strict winner/loser ranks already separate the endpoints. -/
theorem link_map {rank map : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (link : Link (fun atom => rank (map atom)) event before after) :
    Link rank (map event.1, map event.2) (before.map map) (after.map map) := by
  cases link with
  | left pre post order =>
      simpa only [List.map_append, List.map_cons] using
        Link.left (pre.map map) (post.map map) order
  | right pre post order =>
      simpa only [List.map_append, List.map_cons] using
        Link.right (pre.map map) (post.map map) order

theorem run_map {rank map : ℕ → ℕ} {events : List (ℕ × ℕ)} {before after : List ℕ}
    (run : Run (fun atom => rank (map atom)) events before after) :
    Run rank (events.map fun event => (map event.1,map event.2))
      (before.map map) (after.map map) := by
  induction run with
  | nil roots => exact Run.nil _
  | cons first rest ih => exact Run.cons (link_map first) ih

theorem atoms_eq_range {count : ℕ} (tree : BST 0 count) : atoms tree = List.range (2*count+1) := by
  apply List.Pairwise.eq_of_mem_iff (atoms_pairwise tree) List.pairwise_lt_range
  intro atom
  rw [atoms_mem_iff, List.mem_range]
  omega

theorem schedule_length {lo hi : ℕ} (owner : ℕ → ℕ) (tree : BST lo hi) :
    (schedule owner tree).length = 2*(hi-lo) := by
  induction tree with
  | empty => simp [schedule]
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have localLength : (localSchedule owner left right).length = 2 := by
        unfold localSchedule
        split_ifs <;> rfl
      simp only [schedule, List.length_append, ihLeft, ihRight, localLength]
      omega

theorem two_sided_run {count root : ℕ} (rank owner : ℕ → ℕ)
    (left : BST 0 root) (right : BST (root+1) count)
    (projection : Projection rank owner (.node left right))
    (localOwners : LocalOwners rank owner 0 count) :
    Run rank (schedule owner left ++ schedule owner right) (atoms left ++ atoms right)
      [treeOwner owner left, treeOwner owner right] := by
  have hroot := right.lower_le_upper
  have first := schedule_run rank owner left projection.2.1
    (by intro q hq hqu; exact localOwners q hq (by omega))
  have second := schedule_run rank owner right projection.2.2
    (by intro q hq hqu; exact localOwners q (by omega) hqu)
  have first' := first.frame [] (atoms right)
  have second' := second.frame [treeOwner owner left] []
  have run := first'.append (by simpa only [List.append_nil, List.nil_append] using second')
  simpa only [List.nil_append, List.singleton_append] using run

theorem old_children_iff_two_sides {n access root : ℕ} (comparator tree : BST 0 n)
    (p : Decomposition tree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (left : BST 0 root) (right : BST (root+1) p.count)
    (atAccess : p.separator root = access)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (record : External n) (real : record.val = 2*access+1) (value : ℕ) :
    HasChild (Snapshot.ofTree comparator) tree (Nat.le_refl n) 0 record value ↔
      value ∈ (atoms left ++ atoms right).map (AtomOwner p.separator gapOwner) := by
  let f := AtomOwner p.separator gapOwner
  have rootBound := right.lower_le_upper
  have rootValue : f (2*root+1) = 2*access+1 := by simp only [f, owner_odd, atAccess]
  have leftNe : ∀ value ∈ (atoms left).map f, value ≠ 2*access+1 := by
    intro value member
    obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp member
    have bound := (atoms_mem_iff left atom).1 atomMember
    have strict := atom_owners_strict p.gaps minima
      (by omega : atom < 2*root+1) (by omega : 2*root+1 < 2*p.count+1)
    change f atom < f (2*root+1) at strict
    rw [rootValue] at strict
    exact ne_of_lt strict
  have rightNe : ∀ value ∈ (atoms right).map f, value ≠ 2*access+1 := by
    intro value member
    obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp member
    have bound := (atoms_mem_iff right atom).1 atomMember
    have strict := atom_owners_strict p.gaps minima
      (by omega : 2*root+1 < atom) (by omega : atom < 2*p.count+1)
    change f (2*root+1) < f atom at strict
    rw [rootValue] at strict
    exact ne_of_gt strict
  rw [old_root_children_iff_atoms comparator tree p gapOwner minima global record real value,
    ← atoms_eq_range (.node left right)]
  change value ∈ (atoms (.node left right)).map f ∧ value ≠ 2*access+1 ↔
    value ∈ (atoms left ++ atoms right).map f
  simp only [atoms, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, rootValue]
  constructor
  · rintro ⟨(member | equal) | member, different⟩
    · exact Or.inl member
    · exact False.elim (different equal)
    · exact Or.inr member
  · rintro (member | member)
    · exact ⟨Or.inl (Or.inl member), leftNe value member⟩
    · exact ⟨Or.inr member, rightNe value member⟩

theorem exists_node_of_nonempty {lo hi : ℕ} (tree : BST lo hi) (nonempty : lo < hi) :
    ∃ (root : ℕ) (left : BST lo root) (right : BST (root+1) hi), tree = .node left right := by
  cases tree with
  | empty => omega
  | node left right => exact ⟨_, left, right, rfl⟩

/-- A real Greedy surface update supplies a legal adjacent-root execution
on exactly the actual old heap children. Its proposed target shape is the
exact raised canonical tree, expressed through the same extracted gaps.
The separate expansion-edge bridge identifies every scheduled edge with
its concrete target heap edge. -/
theorem actual_access_has_legal_schedule {n access : ℕ}
    (height : ℕ → ℤ) (time : ℤ) (comparator oldTree newTree : BST 0 n)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : GreedyMerge.Surface.Owners height comparator.depth oldOwner n)
    (newOwners : GreedyMerge.Surface.Owners
      (GreedyMerge.Surface.RaiseSurface height n access time) comparator.depth newOwner n)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (fresh : ∀ key, key < n → height key < time)
    (oldCanonical : GreedyMerge.Surface.Canonical height
      (fun key => comparator.depth (oldOwner key)) oldTree)
    (newCanonical : GreedyMerge.Surface.Canonical
      (GreedyMerge.Surface.RaiseSurface height n access time)
      (fun key => comparator.depth (newOwner key)) newTree)
    (p : Decomposition oldTree access)
    (record : External n) (real : record.val = 2*access+1) :
    ∃ (gapOwner owner : ℕ → ℕ) (root : ℕ) (left : BST 0 root) (right : BST (root+1) p.count),
      let f := AtomOwner p.separator gapOwner
      let rank := fun atom => comparator.externalDepth (f atom)
      let events := (schedule owner left ++ schedule owner right).map
        (fun event => (f event.1,f event.2))
      (∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
        (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i)) ∧
      GreedyMerge.IntervalRootOracle.Canonical rank (.node left right) ∧
      newTree = p.expand (.node left right) ∧ p.separator root = access ∧
      LocalOwners rank owner 0 p.count ∧ Projection rank owner (.node left right) ∧
      (∀ value, HasChild (Snapshot.ofTree comparator) oldTree (Nat.le_refl n) 0 record value ↔
        value ∈ (atoms left ++ atoms right).map f) ∧
      Run comparator.externalDepth events ((atoms left ++ atoms right).map f)
        [f (treeOwner owner left), f (treeOwner owner right)] ∧
      events.length = 2*p.count-2 := by
  obtain ⟨gapOwner, skeleton, minima, canonical, expansion⟩ :=
    GreedyMerge.AccessExpansion.canonical_after_raise_is_expansion height time comparator oldTree newTree
      oldOwner newOwner oldOwners newOwners global fresh oldCanonical newCanonical p
  obtain ⟨owner, localOwners, projection⟩ :=
    actual_projection_exists comparator p gapOwner minima skeleton canonical
  obtain ⟨root, left, right, shape⟩ := exists_node_of_nonempty skeleton p.positive
  rw [shape] at canonical expansion projection
  have atAccess := skeleton_root_is_access comparator p gapOwner minima left right canonical global
  refine ⟨gapOwner, owner, root, left, right, minima, canonical, expansion, atAccess,
    localOwners, projection, ?_, ?_, ?_⟩
  · intro value
    exact old_children_iff_two_sides comparator oldTree p gapOwner minima left right
      atAccess global record real value
  · exact run_map (two_sided_run _ owner left right projection localOwners)
  · have rootBound := right.lower_le_upper
    simp only [List.length_map, List.length_append, schedule_length]
    omega

end GreedyMerge.AccessConsolidation

#print axioms GreedyMerge.AccessConsolidation.actual_projection_exists
#print axioms GreedyMerge.AccessConsolidation.skeleton_root_is_access
#print axioms GreedyMerge.AccessConsolidation.actual_access_has_legal_schedule
