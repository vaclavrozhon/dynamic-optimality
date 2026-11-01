import ActualPhaseEvents
import HarmfulDepartureGeometry

/-!
Positive elementary label cells of the actual canonical link schedule
are projected to its actual sparse below-floor entries and the two
endpoint records of the source interval. The phase interface is built,
not supplied as a hypothesis.
-/
namespace GreedyForest.Phase

open Splay.Tree Splay.Tree.BST
open Splay.Analysis
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open ActiveTree

theorem positive_link_below_base (rank : ℕ → ℕ) (labels : ℕ → ℤ)
    (event : ℕ × ℕ) (base : ℕ)
    (hl : labels event.2 = baseLabel rank base event.2)
    (hpositive : labels event.2 < linkLabels rank labels event event.2) :
    rank event.1 < base := by
  by_contra hnot
  have hfloor : base ≤ rank event.1 := by omega
  have hm := contractedGap_mono
    (show rank event.2-rank event.1 ≤ rank event.2-base by omega)
  rw [hl] at hpositive
  simp only [linkLabels,Function.update_self,baseLabel] at hpositive
  omega

noncomputable def actualPositiveDepartures (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (first finish : ℕ) : Finset (Fin events.length) := by
  classical
  exact Finset.univ.filter (fun i => first ≤ (events.get i).2 ∧
    (events.get i).2 < finish ∧
    labelsAt rank initial events i (events.get i).2 <
      labelsAt rank initial events (i.val+1) (events.get i).2)

theorem actual_loser_injective {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (hrun : Run rank events before after) (hn : before.Nodup) :
    Function.Injective (fun i : Fin events.length => (events.get i).2) := by
  have hevent := run_events_nodup hrun hn
  have hloser := List.inj_on_of_nodup_map (run_losers_nodup hrun hn)
  intro i j hij
  apply hevent.injective_get
  exact hloser (List.get_mem events i) (List.get_mem events j) hij

theorem positive_departures_subset {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) (initial : ℕ → ℤ)
    (first finish base : ℕ)
    (hb : ∀ v, first ≤ v → v < finish → initial v = baseLabel rank base v)
    (hfloor : ∀ v, first ≤ v → v < finish → base ≤ rank v) :
    (actualPositiveDepartures rank initial (schedule owner tree) first finish).image
      (fun i => ((schedule owner tree).get i).2) ⊆
      Sparse.belowEntries rank first finish base base (active owner tree).tree ∪
        {first,finish-1} := by
  classical
  let events := schedule owner tree
  have hrun := schedule_run rank owner tree hp hloc
  have hperm := schedule_perm_edges rank owner tree hp hloc
  intro child hchild
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hchild
  have hpos := (Finset.mem_filter.mp hi).2
  have hs := (actual_event_source_labels hrun (atoms_nodup tree) initial i).2
  have hl : labelsAt rank initial events i (events.get i).2 =
      baseLabel rank base (events.get i).2 := hs.trans (hb _ hpos.1 hpos.2.1)
  have hupdate := hpos.2.2
  rw [labelsAt_succ] at hupdate
  have hbelow := positive_link_below_base rank (labelsAt rank initial events i)
    (events.get i) base hl hupdate
  have hedge : events.get i ∈ GreedyMerge.Fringe.edges owner tree :=
    hperm.mem_iff.mp (List.get_mem events i)
  by_cases hr : Retained owner (events.get i).2
  · apply Finset.mem_union_left
    apply Sparse.belowEntries_of_edge rank first finish base _ (events.get i).1
      (events.get i).2 ?_ ⟨hpos.1,hpos.2.1⟩ hbelow base
    rw [active_edges rank owner tree hp hloc]
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hedge,hr⟩
  · apply Finset.mem_union_right
    have hadj := inactive_edge_adjacent rank owner tree hloc
      (events.get i).1 (events.get i).2 hedge hr
    have hout : ¬(first ≤ (events.get i).1 ∧ (events.get i).1 < finish) := by
      intro h; have := hfloor _ h.1 h.2; omega
    have hcl : first ≤ (events.get i).2 := hpos.1
    have hcu : (events.get i).2 < finish := hpos.2.1
    have heq : (events.get i).2 = first ∨ (events.get i).2 = finish-1 := by omega
    simpa using heq

/-- The finite trace's harmful geometry is obtained from the actual
positive cells, actual source interval, and actual retained-record tree.
No projection, phase count, or lifetime allowance is assumed. -/
theorem actual_positive_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) (initial : ℕ → ℤ)
    (first finish base : ℕ)
    (hb : ∀ v, first ≤ v → v < finish → initial v = baseLabel rank base v)
    (hfloor : ∀ v, first ≤ v → v < finish → base ≤ rank v) :
    Nonempty (Execution.HarmfulPhaseGeometry
      (actualPositiveDepartures rank initial (schedule owner tree) first finish).card) := by
  classical
  let events := schedule owner tree
  let positive := actualPositiveDepartures rank initial events first finish
  let a := (active owner tree).tree
  let below := Sparse.belowEntries rank first finish base base a
  have hsubset := positive_departures_subset rank owner tree hp hloc initial
    first finish base hb hfloor
  have hc := Finset.card_le_card hsubset
  have hinj := actual_loser_injective (schedule_run rank owner tree hp hloc) (atoms_nodup tree)
  rw [Finset.card_image_of_injective _ hinj] at hc
  have hc2 := Finset.card_union_le below ({first,finish-1} : Finset ℕ)
  have hc3 : ({first,finish-1} : Finset ℕ).card ≤ 2 := by
    have h := Finset.card_insert_le first ({finish-1} : Finset ℕ)
    simpa using h
  have hcapacity : positive.card ≤ below.card+2 := by
    change positive.card ≤ (below ∪ {first,finish-1}).card at hc
    omega
  let project : Fin positive.card → Sum (Fin below.card) (Fin 2) :=
    fun i => finSumFinEquiv.symm (Fin.castLE hcapacity i)
  refine ⟨Execution.HarmfulPhaseGeometry.sparse
    ⟨first,finish,base,base,rank,a,active_ordered rank owner tree hp hloc,
      active_heap rank owner tree hp hloc,?_,project,?_⟩⟩
  · intro v hv hf hz
    exact hfloor v hf hz
  · exact finSumFinEquiv.symm.injective.comp (Fin.castLE_injective hcapacity)

theorem actual_positive_departures_le_three {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) (initial : ℕ → ℤ)
    (first finish base : ℕ)
    (hb : ∀ v, first ≤ v → v < finish → initial v = baseLabel rank base v)
    (hfloor : ∀ v, first ≤ v → v < finish → base ≤ rank v) :
    (actualPositiveDepartures rank initial (schedule owner tree) first finish).card ≤ 3 := by
  obtain ⟨geometry⟩ := actual_positive_geometry rank owner tree hp hloc initial
    first finish base hb hfloor
  exact geometry.bound

end GreedyForest.Phase

#print axioms GreedyForest.Phase.actual_positive_geometry
#print axioms GreedyForest.Phase.actual_positive_departures_le_three
