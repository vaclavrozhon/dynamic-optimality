import ActualHarmfulEvents
import DepartureGeometry

/-!
The nondropping boundary events are actual indexed schedule links. Their
two cut trees are constructed from the retained-record tree and the two
endpoints of the source interval; the exceptional edges are derived.
-/
namespace GreedyForest.Phase

open Splay.Tree Splay.Tree.BST
open Splay.Analysis
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open HistoricalCuts ActiveTree

noncomputable def actualBoundaryNondrops (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (first finish : ℕ) : Finset (Fin events.length) := by
  classical
  exact Finset.univ.filter (fun i => first ≤ (events.get i).2 ∧
    (events.get i).2 < finish ∧
    ¬(first ≤ (events.get i).1 ∧ (events.get i).1 < finish) ∧
    labelsAt rank initial events i (events.get i).2 ≤
      labelsAt rank initial events (i.val+1) (events.get i).2)

theorem actual_boundary_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) (initial : ℕ → ℤ)
    (first finish base H : ℕ)
    (hb : ∀ v, first ≤ v → v < finish → initial v = baseLabel rank base v)
    (hfloor : ∀ v, first ≤ v → v < finish → base ≤ rank v)
    (hrank : ∀ v, 2*lo ≤ v → v ≤ 2*hi → rank v ≤ H) :
    Nonempty (Execution.BoundaryPhaseGeometry (contractedGap H)
      (actualBoundaryNondrops rank initial (schedule owner tree) first finish).card) := by
  classical
  let events := schedule owner tree
  let boundary := actualBoundaryNondrops rank initial events first finish
  let safe := boundary.filter (fun i => Retained owner (events.get i).2 ∧
    base ≤ rank (events.get i).1)
  let harmful := boundary.filter (fun i => Retained owner (events.get i).2 ∧
    rank (events.get i).1 < base)
  let inactive := boundary.filter (fun i => ¬Retained owner (events.get i).2)
  let a := (active owner tree).tree
  let below := Sparse.belowEntries rank first finish base base a
  let leftEdges := strictCrossingEdges (baseLabel rank base) first a
  let rightEdges := strictCrossingEdges (baseLabel rank base) finish a
  let leftTree := cutView (baseLabel rank base) first a
  let rightTree := cutView (baseLabel rank base) finish a
  have hrun := schedule_run rank owner tree hp hloc
  have hn := atoms_nodup tree
  have hperm := schedule_perm_edges rank owner tree hp hloc
  have eventInjective : Function.Injective events.get := (run_events_nodup hrun hn).injective_get
  have loserInjective := actual_loser_injective hrun hn
  have boundarySpec : ∀ i ∈ boundary,
      first ≤ (events.get i).2 ∧ (events.get i).2 < finish ∧
      ¬(first ≤ (events.get i).1 ∧ (events.get i).1 < finish) ∧
      labelsAt rank initial events i (events.get i).2 ≤
        labelsAt rank initial events (i.val+1) (events.get i).2 := by
    intro i hi; exact (Finset.mem_filter.mp hi).2
  have eventMem : ∀ i : Fin events.length,
      events.get i ∈ GreedyMerge.Fringe.edges owner tree := by
    intro i; exact hperm.mem_iff.mp (List.get_mem events i)
  have activeMem : ∀ i : Fin events.length, Retained owner (events.get i).2 →
      events.get i ∈ a.edges := by
    intro i hi
    rw [active_edges rank owner tree hp hloc]
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (eventMem i),hi⟩
  have hsplit : boundary ⊆ safe ∪ harmful ∪ inactive := by
    intro i hi
    by_cases hr : Retained owner (events.get i).2
    · by_cases hf : base ≤ rank (events.get i).1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,hr,hf⟩))
      · have hlt : rank (events.get i).1 < base := by omega
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,hr,hlt⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,hr⟩)
  have hsafeSubset : safe.image events.get ⊆ leftEdges ∪ rightEdges := by
    intro edge he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hib,hret,hbase⟩ := Finset.mem_filter.mp hi
    have hs := boundarySpec i hib
    have hl := (actual_event_source_labels hrun hn initial i).2.trans (hb _ hs.1 hs.2.1)
    obtain ⟨current,next,hlink⟩ := actual_event_link hrun i
    have hupdate := hs.2.2.2
    rw [labelsAt_succ] at hupdate
    have hstrict := boundary_nondrop_strict_rise hlink (labelsAt rank initial events i)
      base hbase hl hupdate
    have hedge := activeMem i hret
    have hcross : KeyCrosses first (events.get i).1 (events.get i).2 ∨
        KeyCrosses finish (events.get i).1 (events.get i).2 := by
      unfold KeyCrosses
      omega
    rcases hcross with hleft | hright
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hedge,hleft,hstrict⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hedge,hright,hstrict⟩)
  have hsafe : safe.card ≤ leftEdges.card+rightEdges.card := by
    have hc := Finset.card_le_card hsafeSubset
    rw [Finset.card_image_of_injective _ eventInjective] at hc
    exact hc.trans (Finset.card_union_le _ _)
  have hharmSubset : harmful.image (fun i => (events.get i).2) ⊆ below := by
    intro child hc
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hib,hret,hbase⟩ := Finset.mem_filter.mp hi
    have hs := boundarySpec i hib
    exact Sparse.belowEntries_of_edge rank first finish base a
      (events.get i).1 (events.get i).2 (activeMem i hret) ⟨hs.1,hs.2.1⟩ hbase base
  have hharmful : harmful.card ≤ 1 := by
    have hc := Finset.card_le_card hharmSubset
    rw [Finset.card_image_of_injective _ loserInjective] at hc
    exact hc.trans (Sparse.belowEntries_card_le_one rank first finish base a
      (active_ordered rank owner tree hp hloc) (active_heap rank owner tree hp hloc)
      (by intro v hv hf hz; exact hfloor v hf hz) base)
  have hinactiveSubset : inactive.image (fun i => (events.get i).2) ⊆
      ({first,finish-1} : Finset ℕ) := by
    intro child hc
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hib,hret⟩ := Finset.mem_filter.mp hi
    have hs := boundarySpec i hib
    have hadj := inactive_edge_adjacent rank owner tree hloc
      (events.get i).1 (events.get i).2 (eventMem i) hret
    have heq : (events.get i).2 = first ∨ (events.get i).2 = finish-1 := by omega
    simpa using heq
  have hinactive : inactive.card ≤ 2 := by
    have hc := Finset.card_le_card hinactiveSubset
    rw [Finset.card_image_of_injective _ loserInjective] at hc
    have hpair := Finset.card_insert_le first ({finish-1} : Finset ℕ)
    simp only [Finset.card_singleton] at hpair
    exact hc.trans hpair
  have hcard : boundary.card ≤ leftEdges.card+rightEdges.card+3 := by
    have hc := Finset.card_le_card hsplit
    have hc1 := Finset.card_union_le safe harmful
    have hc2 := Finset.card_union_le (safe ∪ harmful) inactive
    omega
  have hleftCount : leftEdges.card ≤ (badCutCount leftTree).toNat := by
    have h := strictCrossingEdges_card_le_count (baseLabel rank base) first a
    change (leftEdges.card:ℤ) ≤ badCutCount leftTree at h
    omega
  have hrightCount : rightEdges.card ≤ (badCutCount rightTree).toNat := by
    have h := strictCrossingEdges_card_le_count (baseLabel rank base) finish a
    change (rightEdges.card:ℤ) ≤ badCutCount rightTree at h
    omega
  have hcapacity : boundary.card ≤
      (badCutCount leftTree).toNat+((badCutCount rightTree).toNat+5) := by omega
  have hlabels : ∀ cut, LabelBounded (contractedGap H) 1 (cutView (baseLabel rank base) cut a) := by
    intro cut
    apply bounded_cutView rank (baseLabel rank base) cut a (contractedGap H) 1
      (active_heap rank owner tree hp hloc) (baseLabel_rank_mono rank base)
    intro v hv
    have hvb := active_bounds owner tree v hv
    exact baseLabel_bounds rank base H v (hrank v hvb.1 hvb.2)
  let project : Fin boundary.card → Sum (Fin (badCutCount leftTree).toNat)
      (Sum (Fin (badCutCount rightTree).toNat) (Fin 5)) := fun i =>
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm)
      (finSumFinEquiv.symm (Fin.castLE hcapacity i))
  refine ⟨⟨leftTree,rightTree,
    ordered_cutView _ _ _ (active_ordered rank owner tree hp hloc),
    ordered_cutView _ _ _ (active_ordered rank owner tree hp hloc),
    hlabels first,hlabels finish,project,?_⟩⟩
  exact (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).injective.comp
    (finSumFinEquiv.symm.injective.comp (Fin.castLE_injective hcapacity))

theorem actual_boundary_nondrops_bound {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) (initial : ℕ → ℤ)
    (first finish base H : ℕ)
    (hb : ∀ v, first ≤ v → v < finish → initial v = baseLabel rank base v)
    (hfloor : ∀ v, first ≤ v → v < finish → base ≤ rank v)
    (hrank : ∀ v, 2*lo ≤ v → v ≤ 2*hi → rank v ≤ H) :
    (actualBoundaryNondrops rank initial (schedule owner tree) first finish).card ≤
      2*contractedGap H+3 := by
  obtain ⟨geometry⟩ := actual_boundary_geometry rank owner tree hp hloc initial
    first finish base H hb hfloor hrank
  apply geometry.bound
  simp only [contractedGap]
  omega

end GreedyForest.Phase

#print axioms GreedyForest.Phase.actual_boundary_geometry
#print axioms GreedyForest.Phase.actual_boundary_nondrops_bound
