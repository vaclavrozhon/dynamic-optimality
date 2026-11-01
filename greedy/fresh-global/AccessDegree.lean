import AccessReady
import SourceSideStates

/-! Exact cost of the actual access in terms of its represented source
root degree.  No numerical degree certificate is an input: the identity
follows from canonical parent coverage, spatial order, and the extracted
search-path decomposition. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.AccessFrontier GreedyMerge.AccessSurvivors GreedyMerge.ExpandedFringe
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessConsolidation
open GreedyMerge.MappedConsolidation GreedyMerge.ExpansionRotations
open GreedyMerge.PathPlateau GreedyMerge.PlateauBridge GreedyMerge.SourceSideStates

def sourceKeys {n : ℕ} (states : States n) (source : External n) : List ℕ :=
  (entries (states source true)).map Entry.key ++ (entries (states source false)).map Entry.key

def sourceDegree {n : ℕ} (states : States n) (source : External n) : ℕ :=
  (entries (states source true)).length + (entries (states source false)).length

theorem sourceKeys_length {n : ℕ} (states : States n) (source : External n) :
    (sourceKeys states source).length = sourceDegree states source := by
  simp [sourceKeys,sourceDegree]

theorem sourceKeys_nodup {n : ℕ} (states : States n) (source : External n)
    (ordered : Ordered states) : (sourceKeys states source).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨StateLabels.entries_key_nodup _ _ _ (ordered source true),
    StateLabels.entries_key_nodup _ _ _ (ordered source false),?_⟩
  intro key leftMem other rightMem same
  obtain ⟨left,hl,leftKey⟩ := List.mem_map.mp leftMem
  obtain ⟨right,hr,rightKey⟩ := List.mem_map.mp rightMem
  have less := (ordered source true).2.1 left hl
  have greater := (ordered source false).2.1 right hr
  simp only [onSide,if_true,Bool.false_eq_true,if_false] at less greater
  omega

theorem sourceKeys_iff_child {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (states : States n) (source : External n)
    (sound : SoundFor (canonicalParent snapshot tree) states)
    (complete : CompleteFor (canonicalParent snapshot tree) states) (key : ℕ) :
    key ∈ sourceKeys states source ↔ HasChild snapshot tree (Nat.le_refl n) 0 source key := by
  constructor
  · intro member
    rcases List.mem_append.mp member with left | right
    · obtain ⟨entry,member,equal⟩ := List.mem_map.mp left
      obtain ⟨record,recordKey,parent⟩ := sound source true entry member
      rw [←equal,←recordKey]
      exact (hasChild_iff_hasPair ..).mpr (canonical_parent_pair snapshot tree source record parent)
    · obtain ⟨entry,member,equal⟩ := List.mem_map.mp right
      obtain ⟨record,recordKey,parent⟩ := sound source false entry member
      rw [←equal,←recordKey]
      exact (hasChild_iff_hasPair ..).mpr (canonical_parent_pair snapshot tree source record parent)
  · intro child
    have bound := hasChild_record_bound snapshot tree source key child
    let record : External n := ⟨key,by omega⟩
    have parent : canonicalParent snapshot tree record=some source :=
      (hasPair_iff_canonicalParent snapshot tree source record).mp ((hasChild_iff_hasPair ..).mp child)
    obtain ⟨side,entry,member,equal⟩ := complete record source parent
    cases side
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨entry,member,equal⟩)
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨entry,member,equal⟩)

/-- Parent coverage identifies the actual represented degree with any
duplicate-free enumeration of the literal canonical root children. -/
theorem sourceDegree_eq_children {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (states : States n) (source : External n) (roots : List ℕ)
    (sound : SoundFor (canonicalParent snapshot tree) states)
    (complete : CompleteFor (canonicalParent snapshot tree) states)
    (ordered : Ordered states) (unique : roots.Nodup)
    (children : ∀ key, HasChild snapshot tree (Nat.le_refl n) 0 source key ↔ key∈roots) :
    sourceDegree states source=roots.length := by
  have same : (sourceKeys states source).toFinset=roots.toFinset := by
    ext key
    simpa only [List.mem_toFinset] using (sourceKeys_iff_child snapshot tree states source sound complete key).trans (children key)
  calc
    sourceDegree states source = (sourceKeys states source).toFinset.card := by
      rw [List.toFinset_card_of_nodup (sourceKeys_nodup states source ordered),sourceKeys_length]
    _ = roots.toFinset.card := congrArg Finset.card same
    _ = roots.length := List.toFinset_card_of_nodup unique

theorem two_sided_atoms_length {count root : ℕ} (left : BST 0 root) (right : BST (root+1) count) :
    (atoms left++atoms right).length=2*count := by
  have bound := right.lower_le_upper
  simp only [List.length_append,atoms_eq_range',List.length_range']
  omega

/-- Every real touched node contributes exactly two old heap children,
including the exposed real separators and gap minima. -/
theorem AccessScheduleData.old_degree {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (source : External n) (real : source.val=2*access+1)
    (states : States n) (ready : Ready comparator oldTree states) :
    sourceDegree states source=2*p.count := by
  let f := AtomOwner p.separator data.gapOwner
  let roots := (atoms data.left++atoms data.right).map f
  have rootsOrder : roots.Pairwise (fun a b => a<b) := by
    rw [List.pairwise_map]
    apply (two_sided_atoms_pairwise data.left data.right).imp_of_mem
    intro a b ha hb less
    exact (atom_owner_lt_iff comparator p data.gapOwner data.minima
      (two_sided_atom_bound data.left data.right ha) (two_sided_atom_bound data.left data.right hb)).mpr less
  have complete : CompleteFor (canonicalParent (Snapshot.ofTree comparator) oldTree) states := by
    intro record owner parent
    exact ready.complete record owner parent (by simp)
  calc
    sourceDegree states source = roots.length := sourceDegree_eq_children _ _ states source roots
      ready.sound complete ready.valid (rootsOrder.imp Nat.ne_of_lt)
      (old_children_iff_two_sides comparator oldTree p data.gapOwner data.minima data.left data.right
        data.atAccess global source real)
    _ = 2*p.count := by simpa only [roots,List.length_map] using two_sided_atoms_length data.left data.right

/-- The degree identity makes the geometric access cost literal: the
actual touch count is half the old represented root degree. -/
theorem AccessScheduleData.touch_count {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (source : External n) (real : source.val=2*access+1)
    (states : States n) (ready : Ready comparator oldTree states) :
    (GreedyMerge.SearchGaps.PathKeys access oldTree).card=sourceDegree states source/2 := by
  rw [data.old_degree global source real states ready,decomposition_path_card p]
  omega

theorem AccessScheduleData.event_count {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p) :
    data.events.length=2*p.count-2 := by
  have bound := data.right.lower_le_upper
  simp only [AccessScheduleData.events,physicalEvents,mapEvents,List.length_map,List.length_append,schedule_length]
  omega

/-- Exactly two source children survive, one on each side; every other
source entry is the loser of exactly one executed adjacent-root link. -/
theorem AccessScheduleData.links_eq_degree {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (source : External n) (real : source.val=2*access+1)
    (states : States n) (ready : Ready comparator oldTree states) :
    data.events.length+2=sourceDegree states source := by
  rw [data.old_degree global source real states ready,data.event_count]
  have positive := p.positive
  omega

theorem sourceDegree_convertRoot {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (families ids : Bool → ℕ) (states : States n) :
    sourceDegree (convertRoot rank source families ids states) source=sourceDegree states source := by
  simp only [sourceDegree,convertRoot_entries]

theorem AccessScheduleData.links_and_births_le_degree {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (source : External n) (real : source.val=2*access+1)
    (states : States n) (ready : Ready comparator oldTree states) :
    data.events.length+rootConversionBirths source states ≤ sourceDegree states source := by
  have links := data.links_eq_degree global source real states ready
  have births := rootConversionBirths_le_two source states
  omega

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.sourceDegree_eq_children
#print axioms GreedyMerge.ActualLinks.AccessScheduleData.old_degree
#print axioms GreedyMerge.ActualLinks.AccessScheduleData.touch_count
#print axioms GreedyMerge.ActualLinks.AccessScheduleData.links_and_births_le_degree
