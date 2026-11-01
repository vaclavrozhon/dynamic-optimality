import SourceFamilyCollapse
import FringeSchedule

/-!
The concrete deletion of every departing loser from a frozen source
block is exactly its restriction to the final surviving root. This also
allows the canonical atom-to-record map, assumed injective only on the
actual initial roots. The abstract source collapse is a consequence of
this literal equality, not an independent execution premise.
-/

namespace GreedyMerge.HistoryProcess

open OrderedBlocks FrozenHistory GreedyForest

def eraseKeys (keys : List ℕ) (block : Frozen) : Frozen :=
  keys.foldl (fun current key => eraseMember key current) block

theorem eraseKeys_eq (keys : List ℕ) (block : Frozen) :
    eraseKeys keys block =
      { block with members := block.members.filter (fun entry => decide (entry.key ∉ keys)) } := by
  induction keys generalizing block with
  | nil => simp [eraseKeys]
  | cons key rest ih =>
      change eraseKeys rest (eraseMember key block) = _
      rw [ih]
      simp only [eraseMember, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro entry member
      apply Bool.eq_iff_iff.mpr
      simp [and_comm]

theorem eraseKeys_history (keys : List ℕ) (block : Frozen) :
    Run [block] [eraseKeys keys block] := by
  induction keys generalizing block with
  | nil => exact .nil _
  | cons key rest ih =>
      exact .cons (Edit.erase [] [] block key) (ih (eraseMember key block))

theorem link_survivor_iff {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (step : Fringe.Schedule.Link rank event before after) (unique : before.Nodup)
    (key : ℕ) : key ∈ after ↔ key ∈ before ∧ key ≠ event.2 := by
  constructor
  · intro present
    exact ⟨step.sublist.subset present, fun equal => step.loser_absent unique (equal ▸ present)⟩
  · rintro ⟨present, different⟩
    cases step <;> simp only [List.mem_append, List.mem_cons] at present ⊢ <;> aesop

theorem run_survivor_iff {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (run : Fringe.Schedule.Run rank events before after)
    (unique : before.Nodup) (key : ℕ) :
    key ∈ after ↔ key ∈ before ∧ key ∉ events.map Prod.snd := by
  induction run with
  | nil roots => simp
  | cons first rest ih =>
      rw [ih (unique.sublist first.sublist), link_survivor_iff first unique]
      simp only [List.map_cons, List.mem_cons, not_or]
      tauto

/-- Every initial source record other than the final survivor occurs
literally as one departing loser, also after the atom-to-record map. -/
theorem mapped_departure_iff {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before : List ℕ} {survivor : ℕ}
    (run : Fringe.Schedule.Run rank events before [survivor])
    (unique : before.Nodup) (record : ℕ → ℕ)
    (injective : Set.InjOn record {key | key ∈ before})
    (key : ℕ) (present : key ∈ before) :
    record key ∉ events.map (fun event => record event.2) ↔ record key = record survivor := by
  have survivorMember : survivor ∈ before := run.sublist.subset (by simp)
  have beforeEq : record key = record survivor ↔ key = survivor :=
    ⟨fun equal => injective present survivorMember equal, congrArg record⟩
  rw [beforeEq]
  have same : record key ∈ events.map (fun event => record event.2) ↔
      key ∈ events.map Prod.snd := by
    constructor
    · intro member
      obtain ⟨event, eventMember, equal⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨event, eventMember,
        injective (run.event_members event eventMember).2 present equal⟩
    · intro member
      obtain ⟨event, eventMember, equal⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨event, eventMember, congrArg record equal⟩
  rw [same]
  simpa only [List.mem_singleton, present, true_and] using
    (run_survivor_iff run unique key).symm

theorem actual_deletions_eq_retainRoot {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before : List ℕ} {survivor : ℕ}
    (run : Fringe.Schedule.Run rank events before [survivor])
    (unique : before.Nodup) (record : ℕ → ℕ)
    (injective : Set.InjOn record {key | key ∈ before})
    (block : Frozen)
    (covered : ∀ entry ∈ block.members, ∃ key ∈ before, record key = entry.key) :
    eraseKeys (events.map (fun event => record event.2)) block =
      retainRoot (record survivor) block := by
  rw [eraseKeys_eq]
  unfold retainRoot
  congr 1
  apply List.filter_congr
  intro entry entryMember
  obtain ⟨key, present, equal⟩ := covered entry entryMember
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq, ← equal]
  exact mapped_departure_iff run unique record injective key present

/-- The collapse consumed by lifetime accounting is now derived from the
actual complete adjacent-root run and its actual source deletions. -/
theorem actual_deletions_collapse {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before : List ℕ} {survivor : ℕ}
    (run : Fringe.Schedule.Run rank events before [survivor])
    (unique : before.Nodup) (record : ℕ → ℕ)
    (injective : Set.InjOn record {key | key ∈ before})
    (pre post : List Frozen) (block : Frozen)
    (valid : Valid (pre ++ block :: post))
    (keysUnique : (block.members.map Primitives.Entry.key).Nodup)
    (covered : ∀ entry ∈ block.members, ∃ key ∈ before, record key = entry.key) :
    Collapses (joins block)
      (familyView block.family (pre ++ block :: post))
      (familyView block.family
        (pre ++ eraseKeys (events.map (fun event => record event.2)) block :: post)) := by
  rw [actual_deletions_eq_retainRoot run unique record injective block covered]
  exact retainRoot_collapses pre post block (record survivor) valid keysUnique

end GreedyMerge.HistoryProcess

#print axioms GreedyMerge.HistoryProcess.actual_deletions_eq_retainRoot
#print axioms GreedyMerge.HistoryProcess.actual_deletions_collapse
