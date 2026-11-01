import AccessSourceAccounting
import CanonicalRunLabels
import Greedy.RestorationJournal

/-!
# The literal access schedule and its intermediate source labels

All hypotheses of the prefix-label theorem are extracted from an actual
access schedule. Internal entries are defined by membership in one
literal frozen source instance, and weak label order is proved for them.
-/

namespace Greedy.AccessTrace

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.PathPlateau GreedyMerge.PlateauBridge GreedyMerge.AccessFrontier
open GreedyMerge.AccessSurvivors GreedyMerge.ExpandedFringe GreedyMerge.AccessConsolidation
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.MappedConsolidation
open GreedyMerge.AccessSourceAccounting GreedyForest.Phase

noncomputable def roots {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p) : List ℕ :=
  (atoms data.left ++ atoms data.right).map (AtomOwner p.separator data.gapOwner)

noncomputable def survivors {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p) : List ℕ :=
  [AtomOwner p.separator data.gapOwner (treeOwner data.owner data.left),
    AtomOwner p.separator data.gapOwner (treeOwner data.owner data.right)]

structure Geometry {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) : Prop where
  run : GreedyMerge.Fringe.Schedule.Run comparator.externalDepth (data.events.map eventKeys) (roots data) (survivors data)
  unique : (roots data).Nodup
  children : ∀ child, HasChild (Snapshot.ofTree comparator) oldTree (Nat.le_refl n) 0 source child ↔ child ∈ roots data
  arrivals : ∀ event ∈ data.events,
    (arrivals (targetSide event) event.1.val (data.events.map eventKeys)).Pairwise (arrivalOrder (targetSide event))

theorem geometry {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val = 2*access+1)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access) : Geometry data source := by
  let f := AtomOwner p.separator data.gapOwner
  let events := mapEvents f (schedule data.owner data.left ++ schedule data.owner data.right)
  have abstractRun := two_sided_run _ data.owner data.left data.right data.projection data.localOwners
  have mapped : GreedyMerge.Fringe.Schedule.Run comparator.externalDepth events (roots data) (survivors data) :=
    run_map abstractRun
  have children := old_children_iff_two_sides comparator oldTree p data.gapOwner data.minima
    data.left data.right data.atAccess global source real
  have keys : data.events.map eventKeys = events :=
    physicalEvents_actual_keys (Snapshot.ofTree comparator) oldTree source comparator.externalDepth
      events (roots data) (survivors data) mapped children
  have order : (roots data).Pairwise (fun a b => a < b) := by
    rw [roots, List.pairwise_map]
    apply (two_sided_atoms_pairwise data.left data.right).imp_of_mem
    intro a b ha hb less
    exact (atom_owner_lt_iff comparator p data.gapOwner data.minima
      (two_sided_atom_bound data.left data.right ha) (two_sided_atom_bound data.left data.right hb)).mpr less
  refine ⟨by rwa [keys], order.imp Nat.ne_of_lt, children, ?_⟩
  intro event member
  have mappedMember : eventKeys event ∈ events := keys ▸ List.mem_map.mpr ⟨event, member, rfl⟩
  obtain ⟨atomEvent, atomMember, equal⟩ := List.mem_map.mp mappedMember
  have rootMember := (abstractRun.event_members atomEvent atomMember).1
  have parentEq : f atomEvent.1 = event.1.val := congrArg Prod.fst equal
  rw [keys, ← parentEq]
  exact mapped_two_sided_arrivals comparator p data.gapOwner data.owner data.minima data.left data.right
    data.projection data.localOwners (targetSide event) atomEvent.1
    (two_sided_atom_bound data.left data.right rootMember)

noncomputable def current {n : ℕ} (comparator : BST 0 n) (K : ℤ)
    (source : External n) (clock : ℕ) (states : States n) (events : List (External n × External n)) (index : ℕ) : States n :=
  runLinks source (fun event => decide (event.2.val < source.val))
    (fun _ current => GreedyMerge.StateLabels.label comparator.externalDepth K current)
    clock states (events.take index)

theorem prefix_labels {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : Geometry data source) (K : ℤ) (clock : ℕ)
    (states : States n) (ready : Ready comparator oldTree states)
    (empty : ∀ side, growerEntries (states source side).grower = [])
    (index : ℕ) (inside : index ≤ data.events.length) :
    GreedyMerge.StateLabels.label comparator.externalDepth K (current comparator K source clock states data.events index) =
      labelsAt comparator.externalDepth (GreedyMerge.StateLabels.label comparator.externalDepth K states)
        (data.events.map eventKeys) index := by
  apply runLinks_labelsAt (Snapshot.ofTree comparator) oldTree comparator.externalDepth K source
    (fun event => decide (event.2.val < source.val)) _ clock states data.events (roots data) (survivors data)
    geometry.run geometry.unique geometry.children ready.sound _ ready.valid ready.persistent empty
    (by intros; rfl) geometry.arrivals index inside
  intro record owner parent
  exact ready.complete record owner parent (by simp)

/-- Equality of source instances is read from frozen records themselves,
so the classification includes both equal-label and unequal-label links. -/
def SameBlock {n : ℕ} (states : States n) (source : External n) (event : External n × External n) : Prop :=
  ∃ side block, block ∈ (states source side).shrinking ∧
    ∃ winner ∈ block.members, ∃ loser ∈ block.members, winner.key = event.1.val ∧ loser.key = event.2.val

noncomputable def kind {n : ℕ} (states : States n) (source : External n) (event : External n × External n) : EntryJournal.Kind := by
  classical
  exact if SameBlock states source event then .internal else .boundary

@[simp] theorem kind_not_ordinary {n : ℕ} (states : States n) (source : External n) (event : External n × External n) :
    kind states source event ≠ .ordinary := by unfold kind; split_ifs <;> simp

theorem internal_order {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : Geometry data source) (K : ℤ) (clock : ℕ)
    (states : States n) (ready : Ready comparator oldTree states)
    (empty : ∀ side, growerEntries (states source side).grower = [])
    (index : Fin data.events.length) (internal : kind states source (data.events.get index) = .internal) :
    let label := GreedyMerge.StateLabels.label comparator.externalDepth K (current comparator K source clock states data.events index)
    label (data.events.get index).1.val ≤ label (data.events.get index).2.val := by
  classical
  have same : SameBlock states source (data.events.get index) := by
    simpa only [kind, ite_eq_left_iff, reduceCtorEq, imp_false, not_not] using internal
  obtain ⟨side, block, member, winner, winMem, loser, loseMem, winKey, loseKey⟩ := same
  have w := GreedyMerge.StateLabels.label_of_frozen (Snapshot.ofTree comparator) oldTree comparator.externalDepth K
    states ready.valid ready.sound source side block member winner winMem
  have l := GreedyMerge.StateLabels.label_of_frozen (Snapshot.ofTree comparator) oldTree comparator.externalDepth K
    states ready.valid ready.sound source side block member loser loseMem
  rw [winKey] at w
  rw [loseKey] at l
  have sourceLabels := actual_event_source_labels geometry.run geometry.unique
    (GreedyMerge.StateLabels.label comparator.externalDepth K states)
    ⟨index.val, by simpa using index.isLt⟩
  simp only [List.get_eq_getElem, List.getElem_map, eventKeys] at sourceLabels
  have rankOrder := run_event_rank_lt geometry.run (eventKeys (data.events.get index))
    (List.mem_map.mpr ⟨_, List.get_mem _ index, rfl⟩)
  dsimp only
  rw [prefix_labels data source geometry K clock states ready empty index.val (Nat.le_of_lt index.isLt)]
  simp only [List.get_eq_getElem] at w l ⊢
  rw [sourceLabels.1, sourceLabels.2, w, l]
  exact_mod_cast contractedGap_mono (Nat.sub_le_sub_right (Nat.le_of_lt rankOrder) block.base)

end Greedy.AccessTrace
