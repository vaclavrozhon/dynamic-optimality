import Splay.Lazy.RankUpdateTrace

namespace Splay.Lazy

namespace Block.AbsorbsRankUpdate

/--
Absorbing a block's common raw-gap shift into its stored interval gap leaves
every member's transient contracted point gap unchanged.
-/
theorem transientContractedGap_eq {n : ℕ}
    {before after : HeapView n} {block : Block n} {shift : ℤ}
    (absorbs : block.AbsorbsRankUpdate before after shift)
    {element : Element n} (member : element ∈ block.elements) :
    Analysis.transientContractedGap
        (after.rawGap element) (block.intervalGap + shift) =
      Analysis.transientContractedGap
        (before.rawGap element) block.intervalGap := by
  cases hMode : block.mode with
  | growing =>
      have growing :
          shift = 0 ∧
            ∀ item ∈ block.elements,
              after.rawGap item = before.rawGap item := by
        simpa only [Block.AbsorbsRankUpdate, hMode] using absorbs
      rw [growing.1, growing.2 element member]
      simp
  | shrinking =>
      have shrinking :
          (block.elements = [] ∧ shift = 0) ∨
            (block.elements ≠ [] ∧
              ∀ item ∈ block.elements,
                after.rawGap item =
                  before.rawGap item + shift) := by
        simpa only [Block.AbsorbsRankUpdate, hMode] using absorbs
      rcases shrinking with empty | nonempty
      · rw [empty.1] at member
        simp at member
      · rw [nonempty.2 element member]
        exact Analysis.transientContractedGap_add_shift
          (before.rawGap element) block.intervalGap shift

end Block.AbsorbsRankUpdate

namespace State

/--
The checkpoint invariant preserved while real ranks are being updated.

It contains every component of `Stable` except heap order.  The parent
structure is already fixed during an absorbed rank update, but its old ranks
may deliberately cease to order that structure until the target ranks are
installed.
-/
def RankPrepared {n : ℕ} (state : State n)
    (params : Interface.Parameters) : Prop :=
  state.Valid params ∧
    state.Complete ∧
    state.OneGrowingPerSide ∧
    state.GrowingTopmost ∧
    state.ValuesRealizeGaps

namespace RankPrepared

theorem valid {n : ℕ} {state : State n}
    {params : Interface.Parameters}
    (prepared : state.RankPrepared params) :
    state.Valid params :=
  prepared.1

theorem complete {n : ℕ} {state : State n}
    {params : Interface.Parameters}
    (prepared : state.RankPrepared params) :
    state.Complete :=
  prepared.2.1

theorem oneGrowingPerSide {n : ℕ} {state : State n}
    {params : Interface.Parameters}
    (prepared : state.RankPrepared params) :
    state.OneGrowingPerSide :=
  prepared.2.2.1

theorem growingTopmost {n : ℕ} {state : State n}
    {params : Interface.Parameters}
    (prepared : state.RankPrepared params) :
    state.GrowingTopmost :=
  prepared.2.2.2.1

theorem valuesRealizeGaps {n : ℕ} {state : State n}
    {params : Interface.Parameters}
    (prepared : state.RankPrepared params) :
    state.ValuesRealizeGaps :=
  prepared.2.2.2.2

/-- Restoring heap order turns a rank-prepared checkpoint into a stable one. -/
theorem stable {n : ℕ} {state : State n}
    {params : Interface.Parameters}
    (prepared : state.RankPrepared params)
    (ordered : state.view.HeapOrdered) :
    state.Stable params :=
  ⟨prepared.valid, prepared.complete, ordered,
    prepared.oneGrowingPerSide, prepared.growingTopmost,
    prepared.valuesRealizeGaps⟩

end RankPrepared

/-- Forgetting heap order from a stable state yields `RankPrepared`. -/
theorem Stable.rankPrepared {n : ℕ} {state : State n}
    {params : Interface.Parameters}
    (stable : state.Stable params) :
    state.RankPrepared params :=
  ⟨stable.1, stable.2.1, stable.2.2.2.1,
    stable.2.2.2.2.1, stable.2.2.2.2.2⟩

/-- An absorbed rank update preserves completeness of the block partition. -/
theorem absorbRankUpdate_complete {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ}
    (complete : state.Complete)
    (same : state.view.SameStructure afterView) :
    (state.absorbRankUpdate afterView shift).Complete := by
  intro element
  rw [absorbRankUpdate_allElements]
  rw [complete element]
  change state.view.parent element ≠ none ↔
    afterView.parent element ≠ none
  rw [same.parent_apply]

/--
Changing only interval gaps preserves the unique growing block on every
owner-side pair.
-/
theorem absorbRankUpdate_oneGrowingPerSide {n : ℕ}
    (state : State n) (afterView : HeapView n)
    (shift : Block n → ℤ)
    (oneGrowing : state.OneGrowingPerSide) :
    (state.absorbRankUpdate afterView shift).OneGrowingPerSide := by
  intro owner childSide
  obtain ⟨beforeId, beforeProperty, beforeUnique⟩ :=
    oneGrowing owner childSide
  let afterId :
      Fin (state.absorbRankUpdate afterView shift).blocks.length :=
    ⟨beforeId.val, by
      change beforeId.val <
        (state.blocks.map fun block =>
          block.shiftedInterval (shift block)).length
      rw [List.length_map]
      exact beforeId.isLt⟩
  refine ⟨afterId, ?_, ?_⟩
  · simpa [afterId, absorbRankUpdate,
      Block.shiftedInterval] using beforeProperty
  · intro candidate candidateProperty
    let beforeCandidate : Fin state.blocks.length :=
      ⟨candidate.val, by
        have candidateBound := candidate.isLt
        simpa [absorbRankUpdate] using candidateBound⟩
    have beforeCandidateProperty :
        let block := state.blocks.get beforeCandidate
        block.mode = .growing ∧
          block.owner = owner ∧ block.side = childSide := by
      simpa [beforeCandidate, absorbRankUpdate,
        Block.shiftedInterval] using candidateProperty
    have beforeEq :
        beforeCandidate = beforeId :=
      beforeUnique beforeCandidate beforeCandidateProperty
    apply Fin.ext
    simpa [beforeCandidate, afterId] using
      congrArg Fin.val beforeEq

/--
The top-most placement of every growing interval is preserved because
`SameStructure` fixes all top-down child lists.
-/
theorem absorbRankUpdate_growingTopmost {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ}
    (topmost : state.GrowingTopmost)
    (same : state.view.SameStructure afterView) :
    (state.absorbRankUpdate afterView shift).GrowingTopmost := by
  intro afterId
  dsimp only
  intro growing
  let beforeId : Fin state.blocks.length :=
    ⟨afterId.val, by
      have afterBound := afterId.isLt
      simpa [absorbRankUpdate] using afterBound⟩
  have beforeGrowing :
      (state.blocks.get beforeId).mode = .growing := by
    simpa [beforeId, absorbRankUpdate,
      Block.shiftedInterval] using growing
  obtain ⟨suffix, beforeTopmost⟩ :=
    topmost beforeId beforeGrowing
  refine ⟨suffix, ?_⟩
  simpa [beforeId, absorbRankUpdate,
    Block.shiftedInterval, same.topDown_eq] using beforeTopmost

/--
Interface values still realize contracted point gaps after every compatible
block absorbs its common raw-gap shift.
-/
theorem absorbRankUpdate_valuesRealizeGaps {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ}
    (values : state.ValuesRealizeGaps)
    (compatible : state.RankUpdateCompatible afterView shift) :
    (state.absorbRankUpdate afterView shift).ValuesRealizeGaps := by
  constructor
  · change state.value afterView.root = 1
    rw [compatible.1.root_eq]
    exact values.1
  · intro afterBlock afterMember element elementMember
    simp only [absorbRankUpdate] at afterMember
    obtain ⟨beforeBlock, beforeMember, rfl⟩ :=
      List.mem_map.mp afterMember
    change state.value element =
      Analysis.transientContractedGap
        (afterView.rawGap element)
        (beforeBlock.intervalGap + shift beforeBlock)
    rw [values.2 beforeBlock beforeMember element elementMember]
    exact
      ((compatible.2 beforeBlock beforeMember).transientContractedGap_eq
        elementMember).symm

/-- A compatible absorbed rank update preserves all of `RankPrepared`. -/
theorem RankPrepared.absorbRankUpdate {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ} {params : Interface.Parameters}
    (prepared : state.RankPrepared params)
    (compatible : state.RankUpdateCompatible afterView shift) :
    (state.absorbRankUpdate afterView shift).RankPrepared params :=
  ⟨state.absorbRankUpdate_valid prepared.valid compatible,
    state.absorbRankUpdate_complete prepared.complete compatible.1,
    state.absorbRankUpdate_oneGrowingPerSide
      afterView shift prepared.oneGrowingPerSide,
    state.absorbRankUpdate_growingTopmost
      prepared.growingTopmost compatible.1,
    state.absorbRankUpdate_valuesRealizeGaps
      prepared.valuesRealizeGaps compatible⟩

/--
A compatible absorbed update whose target view is heap ordered reaches a
fully stable checkpoint.
-/
theorem RankPrepared.absorbRankUpdate_stable {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ} {params : Interface.Parameters}
    (prepared : state.RankPrepared params)
    (compatible : state.RankUpdateCompatible afterView shift)
    (ordered : afterView.HeapOrdered) :
    (state.absorbRankUpdate afterView shift).Stable params :=
  (prepared.absorbRankUpdate compatible).stable ordered

/-- The absorbed update is exactly one interface-invisible rich event. -/
theorem RankPrepared.absorbRankUpdate_trace {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ} {params : Interface.Parameters}
    (prepared : state.RankPrepared params)
    (compatible : state.RankUpdateCompatible afterView shift) :
    Trace params state [.silent]
      (state.absorbRankUpdate afterView shift) :=
  state.absorbRankUpdate_trace prepared.valid compatible

/--
Combined checkpoint bridge: one silent event installs the compatible ranks
and its endpoint is stable whenever the target view is heap ordered.
-/
theorem RankPrepared.absorbRankUpdate_trace_stable {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ} {params : Interface.Parameters}
    (prepared : state.RankPrepared params)
    (compatible : state.RankUpdateCompatible afterView shift)
    (ordered : afterView.HeapOrdered) :
    Trace params state [.silent]
        (state.absorbRankUpdate afterView shift) ∧
      (state.absorbRankUpdate afterView shift).Stable params :=
  ⟨prepared.absorbRankUpdate_trace compatible,
    prepared.absorbRankUpdate_stable compatible ordered⟩

end State

end Splay.Lazy
