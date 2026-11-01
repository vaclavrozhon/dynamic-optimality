import AccessInventory
import ActualEntryCensus
import ActualLifetimeWitnesses

/-!
The accounting source partition is read from the literal converted access
state and the same geometric schedule returned by the access factory.
Coverage, base floors, and stored bucket consistency are consequences of
Ready, not independently supplied event-to-source projections.
-/
namespace GreedyMerge.AccessSourceAccounting

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.PathPlateau GreedyMerge.PlateauBridge GreedyMerge.AccessFrontier
open GreedyMerge.AccessSurvivors GreedyMerge.ExpandedFringe GreedyMerge.AccessConsolidation
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.ActualBlockPartition
open GreedyForest.Phase

/-- Ordinary canonical state soundness/completeness and spatial validity
identify the exact records in either stored root side. -/
theorem ready_side_keys {n : ℕ} (comparator tree : BST 0 n) (states : States n)
    (ready : Ready comparator tree states) (source : External n) (side : Bool) (key : ℕ) :
    key ∈ (entries (states source side)).map Entry.key ↔
      HasChild (Snapshot.ofTree comparator) tree (Nat.le_refl n) 0 source key ∧
      (if side then key<source.val else source.val<key) := by
  constructor
  · rintro member
    obtain ⟨entry,entryMem,rfl⟩ := List.mem_map.mp member
    obtain ⟨record,recordKey,parent⟩ := ready.sound source side entry entryMem
    have child := (hasChild_iff_hasPair _ _ _ _ _ _).mpr
      ((hasPair_iff_canonicalParent (Snapshot.ofTree comparator) tree source record).mpr parent)
    refine ⟨by simpa only [recordKey] using child,?_⟩
    exact (ready.valid source side).2.1 entry entryMem
  · rintro ⟨child,sideTest⟩
    obtain ⟨edge,edgeMem,edgeOwner,edgeKey⟩ := child
    have parent : canonicalParent (Snapshot.ofTree comparator) tree edge.child=some source := by
      simpa only [edgeOwner] using ComparatorHeap.parent_of_fullEdge (Snapshot.ofTree comparator)
        tree edge edgeMem
    obtain ⟨actualSide,entry,entryMem,entryKey⟩ :=
      ready.complete edge.child source parent (by simp)
    have position := (ready.valid source actualSide).2.1 entry entryMem
    have sameSide : actualSide=side := by
      have sameKey : entry.key=key := entryKey.trans edgeKey
      cases actualSide <;> cases side <;> simp_all [onSide] <;> omega
    exact List.mem_map.mpr ⟨entry,by simpa only [sameSide] using entryMem,entryKey.trans edgeKey⟩

theorem atom_left_of_source {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val=2*access+1) (key : ℕ)
    (member : key∈(atoms data.left).map (AtomOwner p.separator data.gapOwner)) : key<source.val := by
  obtain ⟨atom,atomMem,rfl⟩ := List.mem_map.mp member
  have bound := (atoms_mem_iff data.left atom).mp atomMem
  have rootBound := data.right.lower_le_upper
  have less := (GreedyMerge.MappedConsolidation.atom_owner_lt_iff comparator p data.gapOwner
    data.minima (by omega : atom≤2*p.count) (by omega : 2*data.root+1≤2*p.count)).mpr
      (by omega : atom<2*data.root+1)
  simpa only [owner_odd,data.atAccess,←real] using less

theorem atom_right_of_source {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val=2*access+1) (key : ℕ)
    (member : key∈(atoms data.right).map (AtomOwner p.separator data.gapOwner)) : source.val<key := by
  obtain ⟨atom,atomMem,rfl⟩ := List.mem_map.mp member
  have bound := (atoms_mem_iff data.right atom).mp atomMem
  have rootBound := data.right.lower_le_upper
  have less := (GreedyMerge.MappedConsolidation.atom_owner_lt_iff comparator p data.gapOwner
    data.minima (by omega : 2*data.root+1≤2*p.count) (by omega : atom≤2*p.count)).mpr
      (by omega : 2*data.root+1<atom)
  simpa only [owner_odd,data.atAccess,←real] using less

/-- Both source sides come from the exact old canonical child relation of
the same access, including its actual map from atoms to physical records. -/
theorem actual_source_coverage {n access : ℕ} (comparator oldTree newTree : BST 0 n)
    (p : Decomposition oldTree access) (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val=2*access+1)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (states : States n) (ready : Ready comparator oldTree states) :
    (∀ key, key∈(entries (states source true)).map Entry.key ↔
      key∈(atoms data.left).map (AtomOwner p.separator data.gapOwner)) ∧
    (∀ key, key∈(entries (states source false)).map Entry.key ↔
      key∈(atoms data.right).map (AtomOwner p.separator data.gapOwner)) := by
  have children := old_children_iff_two_sides comparator oldTree p data.gapOwner data.minima
    data.left data.right data.atAccess global source real
  constructor
  · intro key
    rw [ready_side_keys comparator oldTree states ready source true key,children]
    simp only [if_true,List.map_append,List.mem_append]
    constructor
    · rintro ⟨left | right,less⟩
      · exact left
      · have greater := atom_right_of_source data source real key right
        omega
    · intro left
      exact ⟨Or.inl left,atom_left_of_source data source real key left⟩
  · intro key
    rw [ready_side_keys comparator oldTree states ready source false key,children]
    simp only [Bool.false_eq_true,if_false,List.map_append,List.mem_append]
    constructor
    · rintro ⟨left | right,greater⟩
      · have less := atom_left_of_source data source real key left
        omega
      · exact right
    · intro right
      exact ⟨Or.inr right,atom_right_of_source data source real key right⟩

/-- The numerical input of a source partition is forced by the actual
stored block bases. Its labels are the global state lookup. -/
theorem source_partition_of_ready {n access lo hi : ℕ}
    (comparator oldTree : BST 0 n) (p : Decomposition oldTree access) (gapOwner : ℕ→ℕ)
    (minima : ∀ i, i≤p.count → GreedyMerge.IntervalRootOracle.UniqueMin comparator.externalDepth
      (2*GreedyMerge.ExpansionRotations.GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (tree : BST lo hi) (upper : hi≤p.count) (source : External n) (side : Bool)
    (states : States n) (ready : Ready comparator oldTree states) (K : ℤ)
    (emptyGrower : growerEntries (states source side).grower=[])
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (coverage : ∀ key, key∈(entries (states source side)).map Entry.key ↔
      key∈(atoms tree).map (AtomOwner p.separator gapOwner)) :
    ∃ s : SourcePartition (comparator.externalDepth ∘ AtomOwner p.separator gapOwner)
        (StateLabels.label comparator.externalDepth K states ∘ AtomOwner p.separator gapOwner) lo hi,
      (∀ v, 2*lo≤v → v≤2*hi → ∀ b∈(states source side).shrinking,
        s.block v=b.id ↔ AtomOwner p.separator gapOwner v∈blockKeys b) ∧
      (∀ b∈(states source side).shrinking, s.base b.id=b.base) := by
  apply GreedyMerge.SourceSideStates.source_partition_of_side comparator p gapOwner minima tree upper
    (StateLabels.label comparator.externalDepth K states) side (states source side)
    (ready.valid source side) emptyGrower ids coverage
  · intro b hb e he
    exact StateLabels.label_of_frozen (Snapshot.ofTree comparator) oldTree comparator.externalDepth K states
      ready.valid ready.sound source side b hb e he
  · intro b hb e he
    exact (ready.bases source side b hb).2 e he


/-- A source ID is looked up in the literal stored frozen blocks. The
fallback is irrelevant on the covered atom domain. -/
noncomputable def storedBlock (state : SideState) (key : ℕ) : ℕ := by
  classical
  exact if present : ∃ b∈state.shrinking, key∈blockKeys b then present.choose.id else 0

theorem frozen_key_of_empty (state : SideState) (empty : growerEntries state.grower=[])
    (key : ℕ) (member : key∈(entries state).map Entry.key) :
    ∃ b∈state.shrinking, key∈blockKeys b := by
  obtain ⟨entry,entryMem,keyEq⟩ := List.mem_map.mp member
  have frozen : entry∈frozenEntries state.shrinking := by
    simpa only [entries,empty,List.append_nil] using entryMem
  obtain ⟨b,hb,he⟩ := List.mem_flatMap.mp frozen
  exact ⟨b,hb,List.mem_map.mpr ⟨entry,he,keyEq⟩⟩

/-- The view's interval coordinates and labels are attached to the same
actual frozen records; no separate per-event source map is retained. -/
structure SideView {lo hi : ℕ} (rank : ℕ→ℕ) (initial : ℕ→ℤ) (record : ℕ→ℕ)
    (tree : BST lo hi) (state : SideState) where
  partition : SourcePartition (rank ∘ record) (initial ∘ record) lo hi
  matching : ∀ v, 2*lo≤v → v≤2*hi → ∀ b∈state.shrinking,
    partition.block v=b.id ↔ record v∈blockKeys b
  bases : ∀ b∈state.shrinking, partition.base b.id=b.base
  covered : ∀ v∈atoms tree, ∃ b∈state.shrinking, record v∈blockKeys b

theorem SideView.block_eq_stored {lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (v : ℕ) (member : v∈atoms tree) : view.partition.block v=storedBlock state (record v) := by
  have present := view.covered v member
  have bounds := (atoms_mem_iff tree v).mp member
  simp only [storedBlock,dif_pos present]
  exact (view.matching v bounds.1 bounds.2 present.choose present.choose_spec.1).mpr present.choose_spec.2

theorem side_view_of_ready {n access lo hi : ℕ}
    (comparator oldTree : BST 0 n) (p : Decomposition oldTree access) (gapOwner : ℕ→ℕ)
    (minima : ∀ i, i≤p.count → GreedyMerge.IntervalRootOracle.UniqueMin comparator.externalDepth
      (2*GreedyMerge.ExpansionRotations.GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (tree : BST lo hi) (upper : hi≤p.count) (source : External n) (side : Bool)
    (states : States n) (ready : Ready comparator oldTree states) (K : ℤ)
    (emptyGrower : growerEntries (states source side).grower=[])
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (coverage : ∀ key, key∈(entries (states source side)).map Entry.key ↔
      key∈(atoms tree).map (AtomOwner p.separator gapOwner)) :
    Nonempty (SideView comparator.externalDepth (StateLabels.label comparator.externalDepth K states)
      (AtomOwner p.separator gapOwner) tree (states source side)) := by
  obtain ⟨partition,matching,bases⟩ := source_partition_of_ready comparator oldTree p gapOwner minima
    tree upper source side states ready K emptyGrower ids coverage
  refine ⟨⟨partition,matching,bases,?_⟩⟩
  intro atom atomMem
  apply frozen_key_of_empty _ emptyGrower
  exact (coverage _).mpr (List.mem_map.mpr ⟨atom,atomMem,rfl⟩)

/-- The two accounting views are constructed from the same actual
converted state and access schedule. Only distinct live instance names
remain an allocator invariant. -/
theorem actual_converted_sources {n access : ℕ} (comparator oldTree newTree : BST 0 n)
    (p : Decomposition oldTree access) (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val=2*access+1)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (states : States n) (ready : Ready comparator oldTree states) (K : ℤ)
    (families ids : Bool→ℕ)
    (distinct : ∀ side, ((convertRoot comparator.externalDepth source families ids states source side).shrinking.map
      Frozen.id).Nodup) :
    let prepared := convertRoot comparator.externalDepth source families ids states
    Nonempty (SideView comparator.externalDepth (StateLabels.label comparator.externalDepth K prepared)
      (AtomOwner p.separator data.gapOwner) data.left (prepared source true)) ∧
    Nonempty (SideView comparator.externalDepth (StateLabels.label comparator.externalDepth K prepared)
      (AtomOwner p.separator data.gapOwner) data.right (prepared source false)) := by
  let prepared := convertRoot comparator.externalDepth source families ids states
  have ready' := convertRoot_ready comparator oldTree source families ids states ready
  have coverage := actual_source_coverage comparator oldTree newTree p data source real global prepared ready'
  have bound := data.right.lower_le_upper
  exact ⟨side_view_of_ready comparator oldTree p data.gapOwner data.minima data.left (by omega)
      source true prepared ready' K (convertRoot_empty _ _ _ _ _ true) (distinct true) coverage.1,
    side_view_of_ready comparator oldTree p data.gapOwner data.minima data.right (le_refl _)
      source false prepared ready' K (convertRoot_empty _ _ _ _ _ false) (distinct false) coverage.2⟩

/-- The single source view supplies both positive and boundary event
geometry. Both filters use exactly its actual stored instance IDs. -/
theorem SideView.positive_geometry {lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ→ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) (block : ℕ) :
    Nonempty (GreedyForest.Execution.HarmfulPhaseGeometry
      (blockPositive (rank ∘ record) (initial ∘ record) (schedule owner tree) view.partition.block block).card) :=
  block_positive_geometry _ owner tree projection localOwners _ view.partition block

theorem SideView.boundary_geometry {lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ→ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) (block H : ℕ)
    (bound : ∀ atom, 2*lo≤atom → atom≤2*hi → rank (record atom)≤H) :
    Nonempty (GreedyForest.Execution.BoundaryPhaseGeometry (contractedGap H)
      (blockBoundaryNondrops (rank ∘ record) (initial ∘ record) (schedule owner tree)
        view.partition.block block).card) :=
  block_boundary_geometry _ owner tree projection localOwners _ view.partition block H bound


/-- Fresh allocation discharges source-ID uniqueness, so the access
factory needs no independent source partition or membership census. -/
theorem actual_allocated_sources {n access : ℕ} (comparator oldTree newTree : BST 0 n)
    (p : Decomposition oldTree access) (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val=2*access+1)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (states : States n) (ready : Ready comparator oldTree states) (K : ℤ) (start : ℕ)
    (inventory : GreedyMerge.HeapAllocation.HeapInventory states start) :
    let prepared := convertRoot comparator.externalDepth source (rootNames source start) (rootNames source start) states
    Nonempty (SideView comparator.externalDepth (StateLabels.label comparator.externalDepth K prepared)
      (AtomOwner p.separator data.gapOwner) data.left (prepared source true)) ∧
    Nonempty (SideView comparator.externalDepth (StateLabels.label comparator.externalDepth K prepared)
      (AtomOwner p.separator data.gapOwner) data.right (prepared source false)) := by
  apply actual_converted_sources comparator oldTree newTree p data source real global states ready K
    (rootNames source start) (rootNames source start)
  intro side
  apply inventory_shrinking_nodup
  exact convertRoot_inventory comparator.externalDepth source start states inventory

/-- Endpoint snapshots in the local schedule are its initial source
labels, and the source IDs are looked up in the actual frozen records. -/
theorem SideView.kind_from_stored {lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ→ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (event : Fin (schedule owner tree).length) :
    EntryCensus.actualKind (rank ∘ record) (initial ∘ record) (schedule owner tree) view.partition.block event =
      EntryCensus.classify (storedBlock state (record ((schedule owner tree).get event).1))
        (storedBlock state (record ((schedule owner tree).get event).2))
        (initial (record ((schedule owner tree).get event).1))
        (initial (record ((schedule owner tree).get event).2)) := by
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have endpoints := run.event_members _ (List.get_mem _ event)
  have labels := actual_event_source_labels run (atoms_nodup tree) (initial ∘ record) event
  simp only [EntryCensus.actualKind,labels.1,labels.2,Function.comp_apply,
    view.block_eq_stored _ endpoints.1,view.block_eq_stored _ endpoints.2]

/-- Every harmful cell is the literal loser's source-label increase.
This equality uses the exact same indexed event and stored ID as kind. -/
theorem SideView.positive_iff_stored {lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ→ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (event : Fin (schedule owner tree).length) (block : ℕ) :
    event∈blockPositive (rank ∘ record) (initial ∘ record) (schedule owner tree) view.partition.block block ↔
      storedBlock state (record ((schedule owner tree).get event).2)=block ∧
      initial (record ((schedule owner tree).get event).2) <
        (contractedGap (rank (record ((schedule owner tree).get event).2)-
          rank (record ((schedule owner tree).get event).1)) : ℤ) := by
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have endpoints := run.event_members _ (List.get_mem _ event)
  have labels := actual_event_source_labels run (atoms_nodup tree) (initial ∘ record) event
  simp only [blockPositive,Finset.mem_filter,Finset.mem_univ,true_and,labelsAt_succ,
    linkLabels,Function.update_self,labels.2,Function.comp_apply,view.block_eq_stored _ endpoints.2]

/-- The boundary nondrop filter reads the same two concrete instance
IDs and the same loser-update cell; it has no independent classification. -/
theorem SideView.boundary_iff_stored {lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ→ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (event : Fin (schedule owner tree).length) (block : ℕ) :
    event∈blockBoundaryNondrops (rank ∘ record) (initial ∘ record) (schedule owner tree) view.partition.block block ↔
      storedBlock state (record ((schedule owner tree).get event).2)=block ∧
      storedBlock state (record ((schedule owner tree).get event).1)≠block ∧
      initial (record ((schedule owner tree).get event).2) ≤
        (contractedGap (rank (record ((schedule owner tree).get event).2)-
          rank (record ((schedule owner tree).get event).1)) : ℤ) := by
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have endpoints := run.event_members _ (List.get_mem _ event)
  have labels := actual_event_source_labels run (atoms_nodup tree) (initial ∘ record) event
  simp only [blockBoundaryNondrops,Finset.mem_filter,Finset.mem_univ,true_and,labelsAt_succ,
    linkLabels,Function.update_self,labels.2,Function.comp_apply,
    view.block_eq_stored _ endpoints.1,view.block_eq_stored _ endpoints.2]

end GreedyMerge.AccessSourceAccounting

#print axioms GreedyMerge.AccessSourceAccounting.actual_source_coverage
#print axioms GreedyMerge.AccessSourceAccounting.source_partition_of_ready

#print axioms GreedyMerge.AccessSourceAccounting.actual_converted_sources

#print axioms GreedyMerge.AccessSourceAccounting.actual_allocated_sources
#print axioms GreedyMerge.AccessSourceAccounting.SideView.kind_from_stored
#print axioms GreedyMerge.AccessSourceAccounting.SideView.positive_iff_stored
#print axioms GreedyMerge.AccessSourceAccounting.SideView.boundary_iff_stored
