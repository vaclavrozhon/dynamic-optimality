import VirtualPrefixInsertion
import VirtualGrowingSlot
import Splay.Interface.OperationCounts

namespace Splay.Research.CappedPrefixInsertion
open Splay.Interface Splay.Research.VirtualNumericInsertion Splay.Research.VirtualPrefixInsertion

theorem realize {n R : ℕ} {params : Parameters} (before : State n)
    (id : BlockId) (source : Block n) (element : Element n) (target : ℕ)
    (valid : before.Valid params) (found : before.blocks[id]? = some source)
    (growing : source.mode = .growing) (fresh : element ∉ before.allElements)
    (different : source.creator ≠ element) (two : 2 ≤ R)
    (oldBound : ∀ x, before.value x ≤ R) (cap : R ≤ params.valueBound)
    (positive : 1 ≤ target) (bounded : target ≤ R) :
    ∃ operations,
      Trace params before operations (insertState (setValue before element target) id element) ∧
      totalActivity operations = 0 ∧ totalBlockGrowth operations = 0 ∧
      totalInserts operations = 1 ∧ totalIncreases operations ≤ R := by
  let c := min (before.value source.creator) (R-1)
  let delta := before.value source.creator-c
  let lowered := setValue before source.creator c
  have creatorPositive := (valid.2.1 source.creator).1
  have cPositive : 1 ≤ c := by dsimp [c]; omega
  have cLe : c ≤ before.value source.creator := min_le_left _ _
  have deltaLe : delta ≤ 1 := by have := oldBound source.creator; dsimp [delta, c]; omega
  have lowTrace := decreases_trace before source.creator delta valid (by dsimp [delta]; omega)
  have arithmetic : before.value source.creator-delta = c := by dsimp [delta]; omega
  rw [arithmetic] at lowTrace
  have lowValid : lowered.Valid params := VirtualGrowingSlot.trace_valid_after lowTrace
  have room : lowered.value source.creator+1 ≤ params.valueBound := by
    simp only [lowered, setValue, Function.update_self]
    dsimp [c]
    omega
  have inserted := VirtualPrefixInsertion.realize lowered id source element target lowValid found growing fresh
    different positive (bounded.trans cap) room
  let afterInsert := insertState (setValue lowered element target) id element
  have afterValid : afterInsert.Valid params := VirtualGrowingSlot.trace_valid_after inserted
  have creatorAfter : afterInsert.value source.creator = c := by
    simp [afterInsert, insertState, setValue, lowered, different]
  have restore := increases_trace afterInsert source.creator delta afterValid (by
    rw [creatorAfter]
    have := (oldBound source.creator).trans cap
    dsimp [delta]
    omega)
  have arithmetic' : afterInsert.value source.creator+delta = before.value source.creator := by
    rw [creatorAfter]
    dsimp [delta]
    omega
  rw [arithmetic'] at restore
  have endpoint : setValue afterInsert source.creator (before.value source.creator) =
      insertState (setValue before element target) id element := by
    cases before with
    | mk blocks values =>
      dsimp [afterInsert, lowered, insertState, setValue]
      congr 1
      funext queried
      by_cases creator : queried = source.creator
      · subst queried
        simp [different]
      · by_cases entrant : queried = element
        · subst queried
          simp [creator]
        · simp [creator, entrant]
  rw [endpoint] at restore
  have topBound : peak lowered source.creator element target ≤ R := by
    unfold peak
    apply max_le (max_le bounded ?_) ?_
    · simp only [lowered, setValue, Function.update_self]
      dsimp [c]
      omega
    · simpa [lowered, setValue, Ne.symm different] using oldBound element
  have entrantPositive : 1 ≤ lowered.value element := (lowValid.2.1 element).1
  have upBound : totalIncreases (VirtualPrefixInsertion.events lowered id source.creator element target) + delta ≤ R := by
    rw [VirtualPrefixInsertion.increases_eq]
    omega
  refine ⟨_, trace_append (trace_append lowTrace inserted) restore, ?_, ?_, ?_, ?_⟩
  · simp [totalActivity_append, VirtualPrefixInsertion.events, totalActivity, Operation.activity]
  · simp [totalBlockGrowth_append, VirtualPrefixInsertion.events,
      totalBlockGrowth, Operation.blockGrowth]
  · simp [totalInserts_append, VirtualPrefixInsertion.events,
      totalInserts, Operation.insertCount]
  · simpa [totalIncreases_append, totalIncreases, Operation.increaseCount] using upBound

end Splay.Research.CappedPrefixInsertion

#print axioms Splay.Research.CappedPrefixInsertion.realize
