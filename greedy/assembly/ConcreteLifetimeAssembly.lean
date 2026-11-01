import SimultaneousSourceDeletion
import CompletedFamilyHistory
import FiniteExecution

/-!
Finite winner and creator-cut lifetimes assembled from actual immutable
block histories. Partition, no-merge, simultaneous source collapse and
retrospective completion are proved here. Local geometric phase witnesses
are supplied by ActualLinkClasses and ActualFamilyCuts; no aggregate
lifetime multiplicity or abstract transition certificate is an input.
-/
namespace GreedyMerge.HistoryProcess

open OrderedBlocks FrozenHistory GreedyForest GreedyForest.Execution

/-- A concrete complete source consolidation, followed by any actual
closed-family edits. Multiple source blocks may be erased by the phase. -/
structure SourceConsolidation (before after : List Frozen) (source : Frozen) where
  rank : ℕ → ℕ
  events : List (ℕ × ℕ)
  roots : List ℕ
  survivor : ℕ
  links : Fringe.Schedule.Run rank events roots [survivor]
  uniqueRoots : roots.Nodup
  record : ℕ → ℕ
  recordInjective : Set.InjOn record {key | key ∈ roots}
  sourceKeysUnique : (source.members.map Primitives.Entry.key).Nodup
  sourceCovered : ∀ entry ∈ source.members, ∃ key ∈ roots, record key=entry.key
  afterEdits : Run (eraseAll (events.map (fun event => record event.2)) before) after

theorem SourceConsolidation.collapse {before after : List Frozen} {source : Frozen}
    (phase : SourceConsolidation before after source) (valid : Valid before)
    (present : source ∈ before) :
    Collapses (joins source) (familyView source.family before) (familyView source.family after) :=
  actual_all_deletions_then_admin_collapse phase.links phase.uniqueRoots phase.record
    phase.recordInjective before after source valid present phase.sourceKeysUnique
    phase.sourceCovered phase.afterEdits

theorem SourceConsolidation.history {before after : List Frozen} {source : Frozen}
    (phase : SourceConsolidation before after source) : Run before after :=
  (eraseAll_history _ before).trans phase.afterEdits

/-- Finite indexing is derived from consecutive states, rather than
assuming the recursive transition interface consumed by accounting. -/
theorem familyTransitions_of_consecutive {stages join : ℕ}
    (state : ℕ → Family ℕ) (wins : Fin stages → ℕ)
    (adjacent : ∀ p : Fin stages,
      Partitioned (state p) ∧ Refines (state (p.val+1)) (state p) ∧
      (0 < wins p → ¬Isolated join (state p) ∧
        ∃ source ∈ state p, join ∈ source ∧ Collapses source (state p) (state (p.val+1)))) :
    FamilyTransitions join (state 0) (List.ofFn (fun p => (state (p.val+1),wins p))) := by
  induction stages generalizing state with
  | zero => simp [FamilyTransitions]
  | succ stages ih =>
      rw [List.ofFn_succ]
      refine ⟨(adjacent 0).1,(adjacent 0).2.1,(adjacent 0).2.2,?_⟩
      have tail := ih (fun t => state (t+1)) (fun p => wins p.succ)
        (fun p => by simpa only [Fin.val_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using adjacent p.succ)
      simpa [Fin.val_succ,Nat.add_assoc] using tail

theorem cutTransitions_of_consecutive {stages cut : ℕ}
    (state : ℕ → Family ℕ) (crossings : Fin stages → ℕ)
    (adjacent : ∀ p : Fin stages,
      UniqueStraddler (fun x => decide (cut≤x)) (state p) ∧
      Refines (state (p.val+1)) (state p) ∧
      (0 < crossings p → ∃ source ∈ state p,
        GreedyForest.Straddles (fun x => decide (cut≤x)) source ∧
        Collapses source (state p) (state (p.val+1)))) :
    CutTransitions cut (state 0) (List.ofFn (fun p => (state (p.val+1),crossings p))) := by
  induction stages generalizing state with
  | zero => simp [CutTransitions]
  | succ stages ih =>
      rw [List.ofFn_succ]
      refine ⟨(adjacent 0).1,(adjacent 0).2.1,(adjacent 0).2.2,?_⟩
      have tail := ih (fun t => state (t+1)) (fun p => crossings p.succ)
        (fun p => by simpa only [Fin.val_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using adjacent p.succ)
      simpa [Fin.val_succ,Nat.add_assoc] using tail

/-- Build the literal winner lifetime from the completed actual family
history. The positive-stage witness names two different actual source
tickets and the actual complete consolidation that deletes that source. -/
noncomputable def winnerLifetime_of_completed {stages : ℕ}
    (family conversion join : ℕ) (actual : ℕ → List Frozen)
    (initial : Valid (actual conversion))
    (steps : ∀ time, conversion≤time → Run (actual time) (actual (time+1)))
    (wins : Fin stages → ℕ)
    (witness : ∀ p : Fin stages, 0 < wins p →
      ∃ source ∈ completedBlocks conversion actual p,
        source.family=family ∧ join∈joins source ∧
        (∃ other∈joins source, join≠other) ∧
        Nonempty (SourceConsolidation (completedBlocks conversion actual p)
          (completedBlocks conversion actual (p.val+1)) source))
    (geometry : ∀ p, WinnerPhaseGeometry (wins p)) :
    WinnerLifetime stages join wins where
  initial := completedView family conversion actual 0
  after := fun p => completedView family conversion actual (p.val+1)
  transitions := by
    apply familyTransitions_of_consecutive
    intro p
    have valid := (completedBlocks_from_conversion conversion actual steps p).valid initial
    refine ⟨(completedView_geometry family conversion actual initial steps p 0).2.1,
      completedView_refines family conversion actual steps p,?_⟩
    intro positive
    obtain ⟨source,present,same,contains,⟨other,otherMember,different⟩,⟨phase⟩⟩ := witness p positive
    refine ⟨internal_pair_not_isolated family _ source present same join other contains otherMember different,
      joins source,mem_familyView.mpr ⟨source,present,same,rfl⟩,contains,?_⟩
    simpa only [same,completedView] using phase.collapse valid present
  geometry := geometry

/-- Build the literal creator-cut lifetime. The cut is the half-open
integer separator (the application uses t+1), witnessed by actual source
tickets on its two sides. -/
noncomputable def cutLifetime_of_completed {stages k : ℕ}
    (family conversion cut : ℕ) (actual : ℕ → List Frozen)
    (initial : Valid (actual conversion))
    (steps : ∀ time, conversion≤time → Run (actual time) (actual (time+1)))
    (crossings : Fin stages → ℕ)
    (witness : ∀ p : Fin stages, 0 < crossings p →
      ∃ source ∈ completedBlocks conversion actual p,
        source.family=family ∧
        (∃ earlier∈joins source, ∃ later∈joins source, earlier<cut ∧ cut≤later) ∧
        Nonempty (SourceConsolidation (completedBlocks conversion actual p)
          (completedBlocks conversion actual (p.val+1)) source))
    (geometry : ∀ p, CutPhaseGeometry k (crossings p)) :
    CutLifetime stages cut k crossings where
  initial := completedView family conversion actual 0
  after := fun p => completedView family conversion actual (p.val+1)
  transitions := by
    apply cutTransitions_of_consecutive
    intro p
    have valid := (completedBlocks_from_conversion conversion actual steps p).valid initial
    refine ⟨(completedView_geometry family conversion actual initial steps p cut).2.2,
      completedView_refines family conversion actual steps p,?_⟩
    intro positive
    obtain ⟨source,present,same,⟨earlier,earlierMember,later,laterMember,earlierLt,laterGe⟩,⟨phase⟩⟩ :=
      witness p positive
    refine ⟨joins source,mem_familyView.mpr ⟨source,present,same,rfl⟩,?_,?_⟩
    · refine ⟨earlier,earlierMember,later,laterMember,?_⟩
      simp [Nat.not_le.mpr earlierLt,laterGe]
    · simpa only [same,completedView] using phase.collapse valid present
  geometry := geometry

end GreedyMerge.HistoryProcess

#print axioms GreedyMerge.HistoryProcess.SourceConsolidation.collapse
#print axioms GreedyMerge.HistoryProcess.winnerLifetime_of_completed
#print axioms GreedyMerge.HistoryProcess.cutLifetime_of_completed
