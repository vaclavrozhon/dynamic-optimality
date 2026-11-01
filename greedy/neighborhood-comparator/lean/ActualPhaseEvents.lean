import ActualFringeCuts
import CutGeometry

/-!
The links counted here are positions of the literal `FringeSchedule`
execution. Their labels are obtained by folding the actual loser updates
over the preceding schedule prefix. Historical bad-cut counts are derived
from those events; no event-to-Cartesian-edge injection is supplied.
-/
namespace GreedyForest.Phase

open Splay.Tree Splay.Tree.BST
open Splay.Analysis
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open HistoricalCuts ActiveTree

theorem run_take_split {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (h : Run rank events before after)
    (i : ℕ) (hi : i ≤ events.length) :
    ∃ middle, Run rank (events.take i) before middle ∧
      Run rank (events.drop i) middle after := by
  induction h generalizing i with
  | nil roots =>
      have hi0 : i = 0 := by simpa using hi
      subst i
      exact ⟨roots, Run.nil _, Run.nil _⟩
  | @cons event events before middle after first rest ih =>
      cases i with
      | zero => exact ⟨before, Run.nil _, Run.cons first rest⟩
      | succ i =>
          have hi' : i ≤ events.length := by simpa using hi
          obtain ⟨current,hprefix,hsuffix⟩ := ih i hi'
          exact ⟨current, Run.cons first hprefix, hsuffix⟩

def labelsAt (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (time : ℕ) : ℕ → ℤ :=
  runLabels rank initial (events.take time)

/-- The indexed snapshots use the actual one-record loser update. -/
theorem labelsAt_succ (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (i : Fin events.length) :
    labelsAt rank initial events (i.val+1) =
      linkLabels rank (labelsAt rank initial events i) (events.get i) := by
  simp only [labelsAt,runLabels,List.take_succ_eq_append_getElem i.isLt,
    List.foldl_append,List.foldl_cons,List.foldl_nil,List.get_eq_getElem]

/-- Both endpoint labels at an actual indexed link are their frozen
source labels, derived from the prefix execution and permanent loser
removal. -/
theorem actual_event_source_labels {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (h : Run rank events before after)
    (hn : before.Nodup) (initial : ℕ → ℤ) (i : Fin events.length) :
    labelsAt rank initial events i (events.get i).1 = initial (events.get i).1 ∧
    labelsAt rank initial events i (events.get i).2 = initial (events.get i).2 := by
  obtain ⟨middle,hprefix,hsuffix⟩ := run_take_split h i (Nat.le_of_lt i.isLt)
  have hm : events.get i ∈ events.drop i := by
    rw [List.drop_eq_getElem_cons i.isLt]
    exact List.mem_cons_self
  have he := hsuffix.event_members (events.get i) hm
  exact ⟨run_survivor_labels hprefix hn initial _ he.1,
    run_survivor_labels hprefix hn initial _ he.2⟩

theorem actual_event_link {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (h : Run rank events before after)
    (i : Fin events.length) :
    ∃ current next, Link rank (events.get i) current next := by
  obtain ⟨middle,hprefix,hsuffix⟩ := run_take_split h i (Nat.le_of_lt i.isLt)
  rw [List.drop_eq_getElem_cons i.isLt] at hsuffix
  cases hsuffix with
  | cons first rest => exact ⟨_,_,first⟩

theorem baseLabel_rank_mono (rank : ℕ → ℕ) (base : ℕ) :
    ∀ a b, rank a ≤ rank b → baseLabel rank base a ≤ baseLabel rank base b := by
  intro a b hab
  unfold baseLabel
  exact_mod_cast contractedGap_mono (Nat.sub_le_sub_right hab base)

theorem baseLabel_bounds (rank : ℕ → ℕ) (base H key : ℕ)
    (hr : rank key ≤ H) :
    1 ≤ baseLabel rank base key ∧ baseLabel rank base key ≤ (contractedGap H : ℤ) := by
  constructor
  · simp only [baseLabel, contractedGap]
    omega
  · unfold baseLabel
    exact_mod_cast contractedGap_mono (show rank key-base ≤ H by omega)

noncomputable def actualBadCrossings (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (members : Finset ℕ) (join : ℕ → ℕ) (time : ℕ) :
    Finset (Fin events.length) := by
  classical
  exact Finset.univ.filter (fun i =>
    (events.get i).1 ∈ members ∧ (events.get i).2 ∈ members ∧
    labelsAt rank initial events i (events.get i).1 ≠
      labelsAt rank initial events i (events.get i).2 ∧
    TimeCrosses time (join (events.get i).1) (join (events.get i).2))

/-- The creator-cut phase allowance for the literal schedule, using
actual prefix labels and either orientation of original join order.
The spatial cut and the map from events to its crossing edges are
constructed in the proof rather than provided as trace witnesses. -/
theorem actual_bad_crossings_have_cut {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) (initial : ℕ → ℤ)
    (members : Finset ℕ) (base : ℕ) (join : ℕ → ℕ) (time : ℕ)
    (hb : ∀ v ∈ members, initial v = baseLabel rank base v)
    (horder :
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join b ≤ join a)) :
    ∃ cut, (actualBadCrossings rank initial (schedule owner tree) members join time).image
      (schedule owner tree).get ⊆ fringeStrictCuts owner (baseLabel rank base) cut tree := by
  classical
  let events := schedule owner tree
  let bad := actualBadCrossings rank initial events members join time
  have hrun := schedule_run rank owner tree hp hloc
  have hn := atoms_nodup tree
  have hperm := schedule_perm_edges rank owner tree hp hloc
  obtain ⟨cut,hcut⟩ := ordered_join_crossings_have_one_key_cut members join time horder
  have hsubset : bad.image events.get ⊆
      fringeStrictCuts owner (baseLabel rank base) cut tree := by
    intro edge he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    have hbad := (Finset.mem_filter.mp hi).2
    have hs := actual_event_source_labels hrun hn initial i
    obtain ⟨current,next,hlink⟩ := actual_event_link hrun i
    have hw : labelsAt rank initial events i (events.get i).1 =
        baseLabel rank base (events.get i).1 := hs.1.trans (hb _ hbad.1)
    have hl : labelsAt rank initial events i (events.get i).2 =
        baseLabel rank base (events.get i).2 := hs.2.trans (hb _ hbad.2.1)
    have hstrict := bad_entry_strict hlink (labelsAt rank initial events i) base
      hw hl hbad.2.2.1
    rw [hw,hl] at hstrict
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_,?_⟩
    · exact List.mem_toFinset.mpr (hperm.mem_iff.mp (List.get_mem events i))
    · exact (hcut _ hbad.1 _ hbad.2.1).mp hbad.2.2.2
    · omega
  exact ⟨cut,hsubset⟩

/-- Construct the exact local interface used by `FiniteExecution` from
the actual schedule, including its concrete active cut tree. -/
theorem actual_bad_crossing_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) (initial : ℕ → ℤ)
    (members : Finset ℕ) (base : ℕ) (join : ℕ → ℕ) (time H : ℕ)
    (hb : ∀ v ∈ members, initial v = baseLabel rank base v)
    (horder :
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join b ≤ join a))
    (hrank : ∀ v, 2*lo ≤ v → v ≤ 2*hi → rank v ≤ H) :
    Nonempty (Execution.CutPhaseGeometry (contractedGap H)
      (actualBadCrossings rank initial (schedule owner tree) members join time).card) := by
  classical
  let events := schedule owner tree
  let bad := actualBadCrossings rank initial events members join time
  obtain ⟨cut,hsubset⟩ := actual_bad_crossings_have_cut rank owner tree hp hloc
    initial members base join time hb horder
  have hevent := run_events_nodup (schedule_run rank owner tree hp hloc) (atoms_nodup tree)
  have hc := Finset.card_le_card hsubset
  have hinj : Function.Injective events.get := hevent.injective_get
  rw [Finset.card_image_of_injective _ hinj] at hc
  let a := (active owner tree).tree
  let ct := cutView (baseLabel rank base) cut a
  have hpath := fringe_strict_cut_path_bound rank owner tree hp hloc (baseLabel rank base) cut
  have hcapacity : bad.card ≤ (badCutCount ct).toNat + 2 := hc.trans hpath
  have hlabels : LabelBounded (contractedGap H) 1 ct := by
    apply bounded_cutView rank (baseLabel rank base) cut a (contractedGap H) 1
      (active_heap rank owner tree hp hloc) (baseLabel_rank_mono rank base)
    intro v hv
    have hvb := active_bounds owner tree v hv
    exact baseLabel_bounds rank base H v (hrank v hvb.1 hvb.2)
  let project : Fin bad.card → Sum (Fin (badCutCount ct).toNat) (Fin 2) :=
    fun i => finSumFinEquiv.symm (Fin.castLE hcapacity i)
  refine ⟨⟨ct, ordered_cutView _ _ _ (active_ordered rank owner tree hp hloc),
    hlabels, project, ?_⟩⟩
  exact finSumFinEquiv.symm.injective.comp (Fin.castLE_injective hcapacity)

theorem actual_bad_crossing_bound {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) (initial : ℕ → ℤ)
    (members : Finset ℕ) (base : ℕ) (join : ℕ → ℕ) (time H : ℕ)
    (hb : ∀ v ∈ members, initial v = baseLabel rank base v)
    (horder :
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join b ≤ join a))
    (hrank : ∀ v, 2*lo ≤ v → v ≤ 2*hi → rank v ≤ H) :
    (actualBadCrossings rank initial (schedule owner tree) members join time).card ≤
      contractedGap H + 1 := by
  obtain ⟨geometry⟩ := actual_bad_crossing_geometry rank owner tree hp hloc
    initial members base join time H hb horder hrank
  apply geometry.bound
  simp only [contractedGap]
  omega

end GreedyForest.Phase

#print axioms GreedyForest.Phase.actual_bad_crossing_bound
#print axioms GreedyForest.Phase.actual_bad_crossing_geometry
