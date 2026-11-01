import ConcreteLifetimeAssembly

/-!
The actual lifetime of one logical shrinking instance. Splitting retires
that instance; the two fresh instances receive separate histories. Erase
and rebase keep its entries as subsequences. Positive and boundary event
lifetimes follow from these concrete edits and actual complete source
consolidations, without a supplied lifetime capacity or deletion telescope.
-/
namespace GreedyMerge.HistoryProcess

open OrderedBlocks FrozenHistory GreedyForest GreedyForest.Execution

def instanceKeys : Option Frozen → Finset ℕ
  | none => ∅
  | some block => (block.members.map Primitives.Entry.key).toFinset

inductive InstanceEdit : Option Frozen → Option Frozen → Prop
  | erase (keys : List ℕ) (block : Frozen) : InstanceEdit (some block) (some (eraseKeys keys block))
  | rebase (base : ℕ) (block : Frozen) : InstanceEdit (some block) (some (OrderedBlocks.rebase base block))
  | retire (block : Frozen) : InstanceEdit (some block) none

inductive InstanceRun : Option Frozen → Option Frozen → Prop
  | nil (state : Option Frozen) : InstanceRun state state
  | cons {before middle after : Option Frozen} (edit : InstanceEdit before middle)
      (rest : InstanceRun middle after) : InstanceRun before after

theorem instanceKeys_erase (keys : List ℕ) (block : Frozen) (key : ℕ) :
    key ∈ instanceKeys (some (eraseKeys keys block)) ↔
      key ∈ instanceKeys (some block) ∧ key ∉ keys := by
  rw [eraseKeys_eq]
  simp only [instanceKeys,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨entry,⟨member,notDeleted⟩,equal⟩
    exact ⟨⟨entry,member,equal⟩,by simpa only [equal] using notDeleted⟩
  · rintro ⟨⟨entry,member,equal⟩,notDeleted⟩
    exact ⟨entry,⟨member,by simpa only [equal] using notDeleted⟩,equal⟩

theorem InstanceEdit.keys_subset {before after : Option Frozen}
    (edit : InstanceEdit before after) : instanceKeys after ⊆ instanceKeys before := by
  cases edit with
  | erase keys block =>
      intro key member
      exact ((instanceKeys_erase keys block key).mp member).1
  | rebase base block => exact Finset.Subset.refl _
  | retire block => exact Finset.empty_subset _

theorem InstanceRun.keys_subset {before after : Option Frozen}
    (run : InstanceRun before after) : instanceKeys after ⊆ instanceKeys before := by
  induction run with
  | nil state => exact Finset.Subset.refl _
  | cons edit rest ih => exact ih.trans edit.keys_subset

/-- A block phase names the actual complete adjacent-root schedule.
The post-phase instance consists of its actual loser deletions followed
by erase/rebase/retire edits. -/
structure InstanceConsolidation (before after : Option Frozen) where
  source : Frozen
  beforeSource : before = some source
  rank : ℕ → ℕ
  events : List (ℕ × ℕ)
  roots : List ℕ
  survivor : ℕ
  links : Fringe.Schedule.Run rank events roots [survivor]
  uniqueRoots : roots.Nodup
  record : ℕ → ℕ
  recordInjective : Set.InjOn record {key | key ∈ roots}
  sourceCovered : ∀ entry ∈ source.members, ∃ key ∈ roots, record key=entry.key
  afterEdits : InstanceRun (some (eraseKeys (events.map (fun event => record event.2)) source)) after

def InstanceConsolidation.departing {before after : Option Frozen}
    (phase : InstanceConsolidation before after) : List ℕ :=
  phase.events.map (fun event => phase.record event.2)

theorem InstanceConsolidation.keys_subset {before after : Option Frozen}
    (phase : InstanceConsolidation before after) : instanceKeys after ⊆ instanceKeys before := by
  rw [phase.beforeSource]
  exact phase.afterEdits.keys_subset.trans (InstanceEdit.erase _ phase.source).keys_subset

theorem InstanceConsolidation.departed_absent {before after : Option Frozen}
    (phase : InstanceConsolidation before after) (key : ℕ)
    (departed : key ∈ phase.departing) : key ∉ instanceKeys after := by
  intro present
  have unerased := (instanceKeys_erase phase.departing phase.source key).mp
    (phase.afterEdits.keys_subset present)
  exact unerased.2 departed

theorem InstanceConsolidation.small {before after : Option Frozen}
    (phase : InstanceConsolidation before after) : (instanceKeys after).card ≤ 1 := by
  have subset : instanceKeys after ⊆ {phase.record phase.survivor} := by
    intro key member
    have kept := phase.afterEdits.keys_subset member
    have pair := (instanceKeys_erase phase.departing phase.source key).mp kept
    obtain ⟨entry,entryMember,entryKey⟩ := List.mem_map.mp (List.mem_toFinset.mp pair.1)
    obtain ⟨atom,atomMember,atomKey⟩ := phase.sourceCovered entry entryMember
    have same := (mapped_departure_iff phase.links phase.uniqueRoots phase.record
      phase.recordInjective atom atomMember).mp
      (by simpa only [atomKey,entryKey,InstanceConsolidation.departing] using pair.2)
    exact Finset.mem_singleton.mpr (by simpa only [atomKey,entryKey] using same)
  simpa using Finset.card_le_card subset

theorem departureTransitions_of_consecutive {Event : Type*} {stages : ℕ}
    (state : ℕ → Finset ℕ) (selected : Fin stages → Finset Event) (record : Event → ℕ)
    (adjacent : ∀ p : Fin stages,
      state (p.val+1) ⊆ state p ∧ (selected p).image record ⊆ state p ∧
      Disjoint ((selected p).image record) (state (p.val+1)) ∧
      (0 < ((selected p).image record).card → (state (p.val+1)).card≤1)) :
    DepartureTransitions (state 0)
      (List.ofFn (fun p => DepartureStep.mk (state (p.val+1)) ((selected p).image record))) := by
  induction stages generalizing state with
  | zero => simp [DepartureTransitions]
  | succ stages ih =>
      rw [List.ofFn_succ]
      refine ⟨(adjacent 0).1,(adjacent 0).2.1,(adjacent 0).2.2.1,(adjacent 0).2.2.2,?_⟩
      have tail := ih (fun t => state (t+1)) (fun p => selected p.succ)
        (fun p => by simpa only [Fin.val_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using adjacent p.succ)
      simpa [Fin.val_succ,Nat.add_assoc] using tail

/-- The remaining inputs identify selected actual event records with
their source membership and actual departing loser list. Event injection
is the actual loser-injectivity fact proved from the adjacent-root run. -/
noncomputable def eventDepartureHistory_of_instances {Event : Type*} {stages : ℕ}
    (actual : ℕ → Option Frozen) (selected : Fin stages → Finset Event) (record : Event → ℕ)
    (edits : ∀ p : Fin stages, InstanceRun (actual p) (actual (p.val+1)))
    (injective : ∀ p, Set.InjOn record (selected p))
    (source : ∀ p, ∀ event∈selected p, record event∈instanceKeys (actual p))
    (charged : ∀ p, (selected p).Nonempty →
      ∃ phase : InstanceConsolidation (actual p) (actual (p.val+1)),
        ∀ event∈selected p, record event∈phase.departing) :
    EventDepartureHistory ℕ Event stages selected record where
  initial := instanceKeys (actual 0)
  after := fun p => instanceKeys (actual (p.val+1))
  injective := injective
  transitions := by
    classical
    apply departureTransitions_of_consecutive (fun t => instanceKeys (actual t)) selected record
    intro p
    refine ⟨(edits p).keys_subset,?_,?_,?_⟩
    · intro key member
      obtain ⟨event,eventMember,rfl⟩ := Finset.mem_image.mp member
      exact source p event eventMember
    · apply Finset.disjoint_left.mpr
      intro key member remaining
      obtain ⟨event,eventMember,rfl⟩ := Finset.mem_image.mp member
      obtain ⟨phase,departing⟩ := charged p ⟨event,eventMember⟩
      exact phase.departed_absent _ (departing event eventMember) remaining
    · intro positive
      have nonempty := Finset.card_pos.mp positive
      obtain ⟨key,member⟩ := nonempty
      obtain ⟨event,eventMember,_⟩ := Finset.mem_image.mp member
      obtain ⟨phase,_⟩ := charged p ⟨event,eventMember⟩
      exact phase.small

noncomputable def harmfulLifetime_of_instances {Event : Type*} {stages : ℕ}
    (actual : ℕ → Option Frozen) (selected : Fin stages → Finset Event) (record : Event → ℕ)
    (edits : ∀ p : Fin stages, InstanceRun (actual p) (actual (p.val+1)))
    (injective : ∀ p, Set.InjOn record (selected p))
    (source : ∀ p, ∀ event∈selected p, record event∈instanceKeys (actual p))
    (charged : ∀ p, (selected p).Nonempty →
      ∃ phase : InstanceConsolidation (actual p) (actual (p.val+1)),
        ∀ event∈selected p, record event∈phase.departing)
    (geometry : ∀ p, HarmfulPhaseGeometry (selected p).card) :
    HarmfulEventLifetime ℕ Event stages selected record :=
  { eventDepartureHistory_of_instances actual selected record edits injective source charged with
    geometry := geometry }

noncomputable def boundaryLifetime_of_instances {Event : Type*} {stages k : ℕ}
    (actual : ℕ → Option Frozen) (selected : Fin stages → Finset Event) (record : Event → ℕ)
    (edits : ∀ p : Fin stages, InstanceRun (actual p) (actual (p.val+1)))
    (injective : ∀ p, Set.InjOn record (selected p))
    (source : ∀ p, ∀ event∈selected p, record event∈instanceKeys (actual p))
    (charged : ∀ p, (selected p).Nonempty →
      ∃ phase : InstanceConsolidation (actual p) (actual (p.val+1)),
        ∀ event∈selected p, record event∈phase.departing)
    (geometry : ∀ p, BoundaryPhaseGeometry k (selected p).card) :
    BoundaryEventLifetime ℕ Event stages k selected record :=
  { eventDepartureHistory_of_instances actual selected record edits injective source charged with
    geometry := geometry }

end GreedyMerge.HistoryProcess

#print axioms GreedyMerge.HistoryProcess.InstanceConsolidation.small
#print axioms GreedyMerge.HistoryProcess.eventDepartureHistory_of_instances
#print axioms GreedyMerge.HistoryProcess.harmfulLifetime_of_instances
#print axioms GreedyMerge.HistoryProcess.boundaryLifetime_of_instances
