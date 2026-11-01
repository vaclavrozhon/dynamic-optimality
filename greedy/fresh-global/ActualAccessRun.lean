import CanonicalAccessReturn

/-! Actual Greedy access factory. Starting with the literal canonical
old heap's concrete block state, it constructs and executes the checked
fringe schedule and returns to the literal new canonical heap. Entries
capture the actual state-derived labels before each loser update. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessFrontier
open GreedyMerge.ExpandedFringe GreedyMerge.AccessSurvivors GreedyMerge.MappedConsolidation
open GreedyMerge.PathPlateau GreedyMerge.AccessConsolidation GreedyMerge.Primitives GreedyMerge.OrderedBlocks
open GreedyMerge.PlateauBridge GreedyMerge.ExpansionRotations GreedyMerge.IntervalRootOracle

/-- The actual geometric data produced by one surface access. This is an
output witness of the factory below; it is never an assumed aggregate cost
certificate. The accounting side can inspect the same literal phase lists. -/
structure AccessScheduleData {n access : ℕ} (comparator oldTree newTree : BST 0 n)
    (p : Decomposition oldTree access) where
  gapOwner : ℕ → ℕ
  owner : ℕ → ℕ
  root : ℕ
  left : BST 0 root
  right : BST (root+1) p.count
  minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
    (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i)
  canonical : GreedyMerge.IntervalRootOracle.Canonical
    (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) (.node left right)
  atAccess : p.separator root=access
  expansion : newTree=p.expand (.node left right)
  localOwners : LocalOwners (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom))
    owner 0 p.count
  projection : Projection (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom))
    owner (.node left right)

def AccessScheduleData.events {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p) :
    List (External n × External n) :=
  physicalEvents n (mapEvents (AtomOwner p.separator data.gapOwner)
    (schedule data.owner data.left++schedule data.owner data.right))

/-- The two root sides form a strictly ordered atom list after the
access atom itself is omitted. -/
theorem two_sided_atoms_pairwise {count root : ℕ} (left : BST 0 root) (right : BST (root+1) count) :
    (atoms left++atoms right).Pairwise (fun a b => a<b) := by
  have full := atoms_pairwise (.node left right)
  change (atoms left++[2*root+1]++atoms right).Pairwise (fun a b => a<b) at full
  have cross := (List.pairwise_append.mp full).2.2
  exact List.pairwise_append.mpr ⟨atoms_pairwise left,atoms_pairwise right,
    fun a ha b hb => cross a (List.mem_append_left _ ha) b hb⟩

theorem two_sided_atom_bound {count root atom : ℕ} (left : BST 0 root) (right : BST (root+1) count)
    (member : atom∈atoms left++atoms right) : atom ≤ 2*count := by
  have boundary := right.lower_le_upper
  rcases List.mem_append.mp member with leftMem | rightMem
  · have bound := (atoms_mem_iff left atom).mp leftMem
    omega
  · exact ((atoms_mem_iff right atom).mp rightMem).2

/-- A complete real access returns an actually executed state with exact
new canonical parents and labels. Projection, schedule, finite record
lifting, prefix order, inherited edges, and root survivors are all derived
inside this theorem from the surface access and the concrete old state. -/
theorem actual_access_returns_canonical {n access : ℕ}
    (height : ℕ → ℤ) (raiseTime : ℤ) (comparator oldTree newTree : BST 0 n)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : GreedyMerge.Surface.Owners height comparator.depth oldOwner n)
    (newOwners : GreedyMerge.Surface.Owners
      (GreedyMerge.Surface.RaiseSurface height n access raiseTime) comparator.depth newOwner n)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (fresh : ∀ key, key<n → height key<raiseTime)
    (oldCanonical : GreedyMerge.Surface.Canonical height
      (fun key => comparator.depth (oldOwner key)) oldTree)
    (newCanonical : GreedyMerge.Surface.Canonical
      (GreedyMerge.Surface.RaiseSurface height n access raiseTime)
      (fun key => comparator.depth (newOwner key)) newTree)
    (p : Decomposition oldTree access) (source : External n) (real : source.val=2*access+1)
    (states : States n) (K : ℤ) (clock : ℕ)
    (sound : SoundFor (canonicalParent (Snapshot.ofTree comparator) oldTree) states)
    (complete : CompleteFor (canonicalParent (Snapshot.ofTree comparator) oldTree) states)
    (ordered : Ordered states) (persistent : Persistent states)
    (histories : Histories states) (beforeClock : BeforeTime clock states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[]) :
    ∃ data : AccessScheduleData comparator oldTree newTree p,
      let events := data.events
      let reader := fun (_ : ℕ) (current : States n) => StateLabels.label comparator.externalDepth K current
      let sourceSide := fun event : External n × External n => decide (event.2.val<source.val)
      let after := runLinks source sourceSide reader clock states events
      SoundFor (canonicalParent (Snapshot.ofTree comparator) newTree) after ∧
      CompleteFor (canonicalParent (Snapshot.ofTree comparator) newTree) after ∧
      Ordered after ∧ Persistent after ∧
      Histories after ∧ BeforeTime (clock+events.length) after ∧
      StateLabels.label comparator.externalDepth K after =
        GreedyForest.Phase.runLabels comparator.externalDepth (StateLabels.label comparator.externalDepth K states)
          (events.map eventKeys) ∧
      events.length=2*p.count-2 := by
  obtain ⟨gapOwner,owner,root,left,right,minima,canonical,expansion,atAccess,
    localOwners,projection,oldChildren,natRun,eventCount⟩ :=
    actual_access_has_legal_schedule height raiseTime comparator oldTree newTree oldOwner newOwner
      oldOwners newOwners global fresh oldCanonical newCanonical p source real
  let f := AtomOwner p.separator gapOwner
  let natEvents := mapEvents f (schedule owner left++schedule owner right)
  let roots := (atoms left++atoms right).map f
  let finalRoots := [f (treeOwner owner left),f (treeOwner owner right)]
  let events := physicalEvents n natEvents
  let sourceSide := fun event : External n × External n => decide (event.2.val<source.val)
  let reader := fun (_ : ℕ) (current : States n) => StateLabels.label comparator.externalDepth K current
  have zero : (Snapshot.ofTree comparator).rank source=0 := by
    change comparator.externalDepth source.val=0
    rw [real]
    exact comparator_zero_of_global comparator global
  have actualChildren : ∀ child, HasChild (Snapshot.ofTree comparator) oldTree (Nat.le_refl n) 0 source child ↔
      child ∈ roots := oldChildren
  have keysEq : events.map eventKeys=natEvents :=
    physicalEvents_actual_keys (Snapshot.ofTree comparator) oldTree source comparator.externalDepth
      natEvents roots finalRoots natRun actualChildren
  have run : Run comparator.externalDepth (events.map eventKeys) roots finalRoots := by
    rw [keysEq]
    exact natRun
  have rootsOrder : roots.Pairwise (fun a b => a<b) := by
    rw [List.pairwise_map]
    apply (two_sided_atoms_pairwise left right).imp_of_mem
    intro a b ha hb less
    exact (atom_owner_lt_iff comparator p gapOwner minima
      (two_sided_atom_bound left right ha) (two_sided_atom_bound left right hb)).mpr less
  have unique : roots.Nodup := rootsOrder.imp (fun h => Nat.ne_of_lt h)
  have abstractRun := two_sided_run _ owner left right projection localOwners
  have eventMember : ∀ event∈events, eventKeys event∈natEvents := by
    intro event member
    rw [←keysEq]
    exact List.mem_map.mpr ⟨event,member,rfl⟩
  have arrivalOrders : ∀ event∈events,
      (arrivals (targetSide event) event.1.val (events.map eventKeys)).Pairwise
        (arrivalOrder (targetSide event)) := by
    intro event member
    obtain ⟨atomEvent,atomMember,mapped⟩ := List.mem_map.mp (eventMember event member)
    have rootMember := (abstractRun.event_members atomEvent atomMember).1
    have parentEq : f atomEvent.1=event.1.val := congrArg Prod.fst mapped
    rw [keysEq,←parentEq]
    exact mapped_two_sided_arrivals comparator p gapOwner owner minima left right projection localOwners
      (targetSide event) atomEvent.1 (two_sided_atom_bound left right rootMember)
  have eventEdges : ∀ event∈events, HasPair (Snapshot.ofTree comparator)
      (p.expand (.node left right)) (Nat.le_refl n) 0 event.1.val event.2.val := by
    intro event member
    exact scheduled_edge_in_new_tree comparator oldTree (p.expand (.node left right)) p gapOwner owner
      minima left right projection localOwners rfl event.1.val event.2.val (eventMember event member)
  have finalChildren : ∀ child, HasPair (Snapshot.ofTree comparator)
      (p.expand (.node left right)) (Nat.le_refl n) 0 source.val child ↔ child∈finalRoots := by
    intro child
    simpa only [finalRoots,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using
      expanded_root_children comparator p gapOwner owner minima left right projection atAccess source real zero child
  have parents := runParents_eq_canonical (Snapshot.ofTree comparator) oldTree p (.node left right)
    source real zero global.1 comparator.externalDepth events roots finalRoots unique run actualChildren eventEdges finalChildren
  have prefixOrders := runLinks_ordered_prefixes (Snapshot.ofTree comparator) oldTree source sourceSide states
    sound ordered persistent emptySource comparator.externalDepth events roots finalRoots run actualChildren reader clock arrivalOrders
  have rootParent : ∀ record : External n, record.val∈roots →
      canonicalParent (Snapshot.ofTree comparator) oldTree record=some source := by
    intro record member
    apply (hasPair_iff_canonicalParent (Snapshot.ofTree comparator) oldTree source record).mp
    exact (hasChild_iff_hasPair _ _ _ _ _ _).mp ((actualChildren _).mpr member)
  have notRoot : ∀ key∈roots, key≠source.val := by
    intro key member
    exact hasChild_ne_owner (Snapshot.ofTree comparator) oldTree source key ((actualChildren key).mpr member)
  have execution := runLinks_sound_complete_labels (canonicalParent (Snapshot.ofTree comparator) oldTree)
    comparator.externalDepth K source sourceSide reader clock states events roots finalRoots run unique rootParent notRoot
    sound complete persistent emptySource (by intro event member; rfl) prefixOrders
  let data : AccessScheduleData comparator oldTree newTree p :=
    ⟨gapOwner,owner,root,left,right,minima,canonical,atAccess,expansion,localOwners,projection⟩
  have neverWins : ∀ event∈events, event.1≠source := by
    intro event member same
    have initialMember := (run.event_members _ (List.mem_map.mpr ⟨event,member,rfl⟩)).1
    exact notRoot _ initialMember (congrArg Fin.val same)
  have historyRun := runLinks_histories source sourceSide reader clock states events persistent histories
    beforeClock emptySource neverWins
  refine ⟨data,?_,?_,?_,?_,historyRun.1,historyRun.2,execution.2.2,?_⟩
  · simpa only [parents,←expansion,data,AccessScheduleData.events,events,natEvents,f,sourceSide,reader] using execution.1
  · simpa only [parents,←expansion,data,AccessScheduleData.events,events,natEvents,f,sourceSide,reader] using execution.2.1
  · exact prefixOrders events [] (by simp)
  · exact runLinks_persistent source sourceSide reader clock states events persistent
  · simpa only [data,AccessScheduleData.events,events,physicalEvents,natEvents,mapEvents,List.length_map] using eventCount

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.actual_access_returns_canonical
