import ChaCha.ProjectedRecords
import Mathlib.Data.Finset.Sum

/-!
# Injective chronological gap payments

A delayed record is the most recent fine change in its retained coarse cell.
Consequently two records triggering at the same time and cell have the same
source occurrence, even when their physical source keys were initially named
differently. This supplies the occurrence injection used by gap accounting.
-/

namespace ChaCha

open Primary Witnesses

/-- A later selected adjacent pair lies in the suffix following an earlier
selected occurrence of the same chronological word. -/
theorem later_pair_mem_suffix {α : Type*} {before₁ before₂ tail₁ tail₂ : List α}
    {y z p : α} (eqword : before₁ ++ y :: tail₁ = before₂ ++ z :: p :: tail₂)
    (later : before₁.length < before₂.length) : z ∈ tail₁ ∧ p ∈ tail₁ := by
  rcases List.append_eq_append_iff.mp eqword with ⟨middle, hbefore, htail⟩ | ⟨middle, hbefore, _⟩
  · cases middle with
    | nil => simp only [List.append_nil] at hbefore; rw [hbefore] at later; omega
    | cons a middle =>
      have ht : tail₁ = middle ++ z :: p :: tail₂ := (List.cons.inj htail).2
      simp [ht]
  · have hl := congrArg List.length hbefore
    simp only [List.length_append] at hl
    omega

/-- Every retained query in the source coarse cell remains in the new fine cell. -/
theorem Witnesses.DelayedEvent.same_cell_fine {history : List Key} {x y z : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (hz : z ∈ e.next :: e.later)
    (howner : q.owner.IsPrefix z) (hcell : q.coarse z = q.coarse y) :
    q.fine z = q.fine e.next := by
  rcases e.retained z hz howner with h | ⟨hn, _⟩
  · exact h
  · exact (hn hcell).elim

/-- A strictly later same-cell source pair would contradict an earlier record's
retained fine cell. -/
theorem Witnesses.DelayedEvent.not_later_source {history : List Key} {x y z : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (f : DelayedEvent history x q z)
    (hcell : q.coarse y = q.coarse z) : ¬ e.before.length < f.before.length := by
  intro hlt
  have heq := e.history_eq.symm.trans f.history_eq
  obtain ⟨hzm, hpm⟩ := later_pair_mem_suffix heq hlt
  have hzfine := e.same_cell_fine hzm f.owner_source hcell.symm
  have hpfine := e.same_cell_fine hpm f.owner_next (f.coarse_same.symm.trans hcell.symm)
  exact f.fine_change (hzfine.trans hpfine.symm)

/-- The source occurrence itself, not only its key, is unique for a retained
coarse-cell record at a fixed query. -/
theorem Witnesses.DelayedEvent.source_prefix_unique {history : List Key} {x y z : Key} {q : Gadget}
    (e : DelayedEvent history x q y) (f : DelayedEvent history x q z)
    (hcell : q.coarse y = q.coarse z) : e.before = f.before := by
  have h₁ := e.not_later_source f hcell
  have h₂ := f.not_later_source e hcell.symm
  have hlen : e.before.length = f.before.length := by omega
  exact List.append_inj_left (e.history_eq.symm.trans f.history_eq) hlen

/-- Uniqueness is preserved under projection of the source history. -/
theorem delayed_source_projection_unique {β : Type*} (project : Key → Option β)
    {history₁ history₂ : List Key} {x₁ x₂ y z : Key} {q : Gadget}
    (e : DelayedEvent history₁ x₁ q y) (f : DelayedEvent history₂ x₂ q z)
    (hhistory : history₁ = history₂) (htarget : x₁ = x₂)
    (hcell : q.coarse y = q.coarse z) :
    e.before.filterMap project = f.before.filterMap project := by
  subst history₂
  subst x₂
  exact congrArg (List.filterMap project) (e.source_prefix_unique f hcell)

/-- A finite family of chronological entry and delayed gap payments has the
actual event budget. Distinct projected entry targets and delayed source
occurrences suffice; delayed trigger times themselves need not be distinct. -/
theorem entry_delayed_payment_bound_by_cell {E D β : Type*} [DecidableEq E] [DecidableEq D]
    (entries : Finset E) (delays : Finset D) (H : Nat) (qs : Finset Gadget)
    (q : Gadget) (hq : q ∈ qs) (word : List Key) (leaves : OnLeaves H word)
    (project : Key → Option β)
    (entryTime : E → Fin word.length) (entrySource : E → Key)
    (entryRecord : ∀ i ∈ entries,
      EntryEvent (queryHistory [] word (entryTime i)) word[entryTime i] q (entrySource i))
    (entryOrdinal : E → Nat)
    (entryMatch : ∀ i ∈ entries,
      ((word.take (entryTime i).val).filterMap project).length = entryOrdinal i)
    (entryInjective : Set.InjOn entryOrdinal (entries : Set E))
    (delayedTime : D → Fin word.length) (delayedSource : D → Key)
    (delayedRecord : ∀ i ∈ delays,
      DelayedEvent (queryHistory [] word (delayedTime i)) word[delayedTime i] q (delayedSource i))
    (delayedOrdinal : D → Nat)
    (delayedMatch : ∀ i (hi : i ∈ delays),
      ((delayedRecord i hi).before.filterMap project).length = delayedOrdinal i)
    (delayedInjective : Set.InjOn
      (fun i => (q.coarse (delayedSource i), delayedOrdinal i)) (delays : Set D)) :
    entries.card + delays.card ≤ eventSum H qs [] word := by
  classical
  let assign : E ⊕ D → EventOccurrence word
    | .inl i => ⟨entryTime i, Sum.inl q⟩
    | .inr i => ⟨delayedTime i, Sum.inr (q, q.coarse (delayedSource i))⟩
  rw [← Finset.card_disjSum]
  apply payment_card_le_eventSum (entries.disjSum delays) H qs [] word assign
  · intro i hi
    cases i with
    | inl i =>
      have him : i ∈ entries := Finset.inl_mem_disjSum.mp hi
      exact entry_record_mem_eventsAt (entryTime i) hq (entryRecord i him)
    | inr i =>
      have him : i ∈ delays := Finset.inr_mem_disjSum.mp hi
      apply delayed_record_mem_eventsAt (delayedTime i) hq (delayedRecord i him)
      intro x hx
      simp only [queryHistory, List.nil_append, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact leaves x (List.mem_of_mem_take hx)
      · exact leaves _ (List.getElem_mem _)
  · intro i hi j hj heq
    have htime := congrArg (fun a : EventOccurrence word => a.1) heq
    have htag := congrArg (fun a : EventOccurrence word => a.2) heq
    cases i with
    | inl i =>
      have him : i ∈ entries := Finset.inl_mem_disjSum.mp hi
      cases j with
      | inl j =>
        have hjm : j ∈ entries := Finset.inl_mem_disjSum.mp hj
        have hij : entryTime i = entryTime j := htime
        congr 1
        apply entryInjective him hjm
        rw [← entryMatch i him, ← entryMatch j hjm, hij]
      | inr j => cases htag
    | inr i =>
      have him : i ∈ delays := Finset.inr_mem_disjSum.mp hi
      cases j with
      | inl j => cases htag
      | inr j =>
        have hjm : j ∈ delays := Finset.inr_mem_disjSum.mp hj
        have hij : delayedTime i = delayedTime j := htime
        have hcell : q.coarse (delayedSource i) = q.coarse (delayedSource j) := by
          exact congrArg Prod.snd (Sum.inr.inj htag)
        have hproject := delayed_source_projection_unique project
          (delayedRecord i him) (delayedRecord j hjm)
          (congrArg (queryHistory [] word) hij)
          (congrArg (fun t : Fin word.length => word[t]) hij) hcell
        congr 1
        apply delayedInjective him hjm
        apply Prod.ext hcell
        change delayedOrdinal i = delayedOrdinal j
        rw [← delayedMatch i him, ← delayedMatch j hjm, hproject]

/-- Version using globally injective delayed source ordinals. -/
theorem entry_delayed_payment_bound {E D β : Type*} [DecidableEq E] [DecidableEq D]
    (entries : Finset E) (delays : Finset D) (H : Nat) (qs : Finset Gadget)
    (q : Gadget) (hq : q ∈ qs) (word : List Key) (leaves : OnLeaves H word)
    (project : Key → Option β)
    (entryTime : E → Fin word.length) (entrySource : E → Key)
    (entryRecord : ∀ i ∈ entries,
      EntryEvent (queryHistory [] word (entryTime i)) word[entryTime i] q (entrySource i))
    (entryOrdinal : E → Nat)
    (entryMatch : ∀ i ∈ entries,
      ((word.take (entryTime i).val).filterMap project).length = entryOrdinal i)
    (entryInjective : Set.InjOn entryOrdinal (entries : Set E))
    (delayedTime : D → Fin word.length) (delayedSource : D → Key)
    (delayedRecord : ∀ i ∈ delays,
      DelayedEvent (queryHistory [] word (delayedTime i)) word[delayedTime i] q (delayedSource i))
    (delayedOrdinal : D → Nat)
    (delayedMatch : ∀ i (hi : i ∈ delays),
      ((delayedRecord i hi).before.filterMap project).length = delayedOrdinal i)
    (delayedInjective : Set.InjOn delayedOrdinal (delays : Set D)) :
    entries.card + delays.card ≤ eventSum H qs [] word := by
  apply entry_delayed_payment_bound_by_cell entries delays H qs q hq word leaves project
    entryTime entrySource entryRecord entryOrdinal entryMatch entryInjective
    delayedTime delayedSource delayedRecord delayedOrdinal delayedMatch
  intro i hi j hj hij
  exact delayedInjective hi hj (congrArg Prod.snd hij)

end ChaCha
