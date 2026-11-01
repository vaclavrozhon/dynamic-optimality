import ActualBoundaryEvents
import WinnerGeometry

/-!
Actual good/bad classifications use current prefix labels and the fixed
source-block identities. Their local accounting cells, winner geometry,
and shrinking-source transitions are derived from the same link run.
-/
namespace GreedyForest.Phase

open Splay.Tree Splay.Tree.BST
open Splay.Analysis
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule

noncomputable def actualInternalGood (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (block : ℕ → ℕ) : Finset (Fin events.length) := by
  classical
  exact Finset.univ.filter (fun i => block (events.get i).1 = block (events.get i).2 ∧
    labelsAt rank initial events i (events.get i).1 =
      labelsAt rank initial events i (events.get i).2)

noncomputable def actualInternalBad (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (block : ℕ → ℕ) : Finset (Fin events.length) := by
  classical
  exact Finset.univ.filter (fun i => block (events.get i).1 = block (events.get i).2 ∧
    labelsAt rank initial events i (events.get i).1 ≠
      labelsAt rank initial events i (events.get i).2)

/-- A good event names its own actual decreasing label cell. -/
theorem actual_good_drop {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (hrun : Run rank events before after) (hn : before.Nodup)
    (initial : ℕ → ℤ) (block base : ℕ → ℕ)
    (hb : ∀ v ∈ before, initial v = baseLabel rank (base (block v)) v)
    (hf : ∀ v ∈ before, base (block v) ≤ rank v)
    (i : Fin events.length) (hi : i ∈ actualInternalGood rank initial events block) :
    labelsAt rank initial events (i.val+1) (events.get i).2 -
      labelsAt rank initial events i (events.get i).2 ≤ -1 := by
  classical
  have hg := (Finset.mem_filter.mp hi).2
  have hm := hrun.event_members (events.get i) (List.get_mem events i)
  have hs := actual_event_source_labels hrun hn initial i
  obtain ⟨current,next,hlink⟩ := actual_event_link hrun i
  have hw := hs.1.trans (hb _ hm.1)
  have hl := hs.2.trans (hb _ hm.2)
  rw [←hg.1] at hl
  rw [labelsAt_succ]
  exact good_link_drop hlink (labelsAt rank initial events i) (base (block (events.get i).1))
    (hf _ hm.1) hw hl hg.2

/-- The new entry ticket of a bad event has positive entry rank before
the loser update. This uses its actual two endpoint snapshots. -/
theorem actual_bad_entry_strict {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (hrun : Run rank events before after) (hn : before.Nodup)
    (initial : ℕ → ℤ) (block base : ℕ → ℕ)
    (hb : ∀ v ∈ before, initial v = baseLabel rank (base (block v)) v)
    (i : Fin events.length) (hi : i ∈ actualInternalBad rank initial events block) :
    labelsAt rank initial events i (events.get i).1 + 1 ≤
      labelsAt rank initial events i (events.get i).2 := by
  classical
  have hg := (Finset.mem_filter.mp hi).2
  have hm := hrun.event_members (events.get i) (List.get_mem events i)
  have hs := actual_event_source_labels hrun hn initial i
  obtain ⟨current,next,hlink⟩ := actual_event_link hrun i
  have hw := hs.1.trans (hb _ hm.1)
  have hl := hs.2.trans (hb _ hm.2)
  rw [←hg.1] at hl
  exact bad_entry_strict hlink (labelsAt rank initial events i) (base (block (events.get i).1))
    hw hl hg.2

/-- Distinct indexed events always name distinct elementary cells,
independently of any rank or geometry property. -/
theorem actual_event_cell_injective (events : List (ℕ × ℕ)) :
    Function.Injective (fun i : Fin events.length => ((events.get i).2,i)) := by
  intro i j hij
  exact congrArg Prod.snd hij

noncomputable def actualBadWins (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (block : ℕ → ℕ) (parent : ℕ) : Finset (Fin events.length) := by
  classical
  exact (actualInternalBad rank initial events block).filter (fun i => (events.get i).1 = parent)

/-- The actual bad wins of a record produce the winner geometry required
by the finite trace. The projection is constructed from schedule edges. -/
theorem actual_winner_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi)
    (hcanonical : GreedyMerge.Plateau.Cartesian (GreedyMerge.Plateau.Priority rank) tree)
    (hloc : LocalOwners rank owner lo hi) (hunique : UniqueIntervals rank (2*lo) (2*hi))
    (initial : ℕ → ℤ) (block : ℕ → ℕ) (parent : ℕ) :
    Nonempty (Execution.WinnerPhaseGeometry
      (actualBadWins rank initial (schedule owner tree) block parent).card) := by
  classical
  let events := schedule owner tree
  let wins := actualBadWins rank initial events block parent
  have hp := projection_of_cartesian rank owner tree hcanonical hloc hunique
  have hrun := schedule_run rank owner tree hp hloc
  have hperm := schedule_perm_edges rank owner tree hp hloc
  have hsubset : wins.image (fun i => (events.get i).2) ⊆ (outgoing owner parent tree).toFinset := by
    intro child hc
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hc
    have hparent := (Finset.mem_filter.mp hi).2
    have hedge := hperm.mem_iff.mp (List.get_mem events i)
    have hedge' : (parent,(events.get i).2) ∈ edges owner tree := by
      simpa only [←hparent] using hedge
    exact List.mem_toFinset.mpr ((mem_edges_iff_outgoing owner tree parent _).mp hedge')
  have hc := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ (actual_loser_injective hrun (atoms_nodup tree))] at hc
  have hcapacity : wins.card ≤ (outgoing owner parent tree).length :=
    hc.trans (List.toFinset_card_le _)
  refine ⟨⟨lo,hi,rank,owner,tree,parent,hcanonical,hloc,hunique,
    Fin.castLE hcapacity,Fin.castLE_injective hcapacity⟩⟩

theorem run_final_loser_absent {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (hrun : Run rank events before after) (hn : before.Nodup)
    (event : ℕ × ℕ) (he : event ∈ events) : event.2 ∉ after := by
  induction hrun with
  | nil roots => simp at he
  | @cons firstEvent events before middle after first rest ih =>
      rcases List.mem_cons.mp he with he | he
      · subst event
        intro hafter
        exact first.loser_absent hn (rest.sublist.subset hafter)
      · exact ih (hn.sublist first.sublist) he

noncomputable def actualSourceStep (members : Finset ℕ) (events : List (ℕ × ℕ))
    (after : List ℕ) (charged : Finset (Fin events.length)) : Execution.DepartureStep ℕ := by
  classical
  exact ⟨members ∩ after.toFinset, charged.image (fun i => (events.get i).2)⟩

/-- A complete actual consolidation supplies its source-set refinement,
charged-record deletion, and singleton collapse. The charged event subset
may be positive cells or nondropping boundary cells. -/
theorem actual_source_transition {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before : List ℕ} {survivor : ℕ} (hrun : Run rank events before [survivor])
    (hn : before.Nodup) (members : Finset ℕ) (charged : Finset (Fin events.length))
    (hsource : ∀ i ∈ charged, (events.get i).2 ∈ members) :
    Execution.DepartureTransitions members
      [actualSourceStep members events [survivor] charged] := by
  classical
  refine ⟨Finset.inter_subset_left,?_,?_,?_,trivial⟩
  · intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact hsource i hi
  · apply Finset.disjoint_left.mpr
    intro v hv hafter
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hmem := List.mem_toFinset.mp (Finset.mem_inter.mp hafter).2
    exact run_final_loser_absent hrun hn _ (List.get_mem events i) hmem
  · intro _
    have hc := Finset.card_le_card (Finset.inter_subset_right :
      members ∩ ([survivor] : List ℕ).toFinset ⊆ ([survivor] : List ℕ).toFinset)
    simpa [actualSourceStep] using hc

end GreedyForest.Phase

#print axioms GreedyForest.Phase.actual_good_drop
#print axioms GreedyForest.Phase.actual_bad_entry_strict
#print axioms GreedyForest.Phase.actual_winner_geometry
#print axioms GreedyForest.Phase.actual_source_transition
