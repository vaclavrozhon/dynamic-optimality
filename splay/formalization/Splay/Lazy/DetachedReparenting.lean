import Splay.Lazy.DeletionNormalization
import Splay.Lazy.OrderedChildren

namespace Splay.Lazy

/-- Views agreeing on assigned vertices induce identical attached-child
orders. Their structural depth functions need not be identical. -/
theorem HeapView.attachedTopDown_eq_of_agreement {n : ℕ} {before after : HeapView n}
    {assigned : List (Element n)}
    (agreement : ∀ element ∈ assigned,
      after.parent element = before.parent element ∧ after.side element = before.side element)
    (owner : Element n) (side : Side) :
    after.attachedTopDown assigned owner side = before.attachedTopDown assigned owner side := by
  have membership : ∀ element,
      element ∈ after.attachedTopDown assigned owner side ↔
        element ∈ before.attachedTopDown assigned owner side := by
    intro element
    simp only [HeapView.mem_attachedTopDown_iff, HeapView.mem_topDown_iff]
    constructor
    · rintro ⟨⟨parent, side⟩, member⟩
      rw [(agreement element member).1] at parent
      rw [(agreement element member).2] at side
      exact ⟨⟨parent, side⟩, member⟩
    · rintro ⟨⟨parent, side⟩, member⟩
      rw [← (agreement element member).1] at parent
      rw [← (agreement element member).2] at side
      exact ⟨⟨parent, side⟩, member⟩
  cases side with
  | left =>
      exact List.Pairwise.eq_of_mem_iff ((after.topDown_ordered owner).1.filter _)
        ((before.topDown_ordered owner).1.filter _) membership
  | right =>
      exact List.Pairwise.eq_of_mem_iff ((after.topDown_ordered owner).2.filter _)
        ((before.topDown_ordered owner).2.filter _) membership

namespace State

/-- Replace the heap view while retaining all interface data literally. -/
def replaceView {n : ℕ} (state : State n) (view : HeapView n) : State n :=
  { state with view := view }

/-- Changing parents only for detached elements leaves all current intervals
valid, with unchanged gaps and interface projection. -/
theorem replaceView_valid {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (view : HeapView n)
    (ranks : view.rank = state.view.rank)
    (agreement : ∀ element ∈ state.allElements,
      view.parent element = state.view.parent element ∧ view.side element = state.view.side element) :
    (state.replaceView view).Valid params := by
  refine ⟨valid.toInterface, ?_⟩
  intro block member
  have original := valid.2 block member
  have rawEq : ∀ element ∈ block.elements, view.rawGap element = state.view.rawGap element := by
    intro element inside
    have assigned := State.mem_allElements_iff.mpr ⟨block, member, inside⟩
    simp only [HeapView.rawGap, ranks, (agreement element assigned).1]
  refine ⟨?_, original.2.1, ?_⟩
  · change IsSegment block.elements (view.attachedTopDown state.allElements block.owner block.side)
    rw [HeapView.attachedTopDown_eq_of_agreement agreement]
    exact original.1
  · change block.GapValid view
    have oldGap := original.2.2
    cases mode : block.mode with
    | growing =>
        simp only [Block.GapValid, mode] at oldGap ⊢
        exact ⟨oldGap.1, fun element inside => by rw [rawEq element inside]; exact oldGap.2 element inside⟩
    | shrinking =>
        simp only [Block.GapValid, mode] at oldGap ⊢
        rcases oldGap with empty | ⟨nonempty, ⟨minimizer, inside, attains⟩, lower⟩
        · exact Or.inl empty
        · refine Or.inr ⟨nonempty, ⟨minimizer, inside, ?_⟩, ?_⟩
          · rw [rawEq minimizer (List.mem_toFinset.mp inside)]
            exact attains
          · intro element inside
            rw [rawEq element (List.mem_toFinset.mp inside)]
            exact lower element inside

/-- Detached reparenting is a checked silent step, rather than a rebase of
existing blocks. -/
theorem replaceView_step {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (view : HeapView n)
    (ranks : view.rank = state.view.rank)
    (agreement : ∀ element ∈ state.allElements,
      view.parent element = state.view.parent element ∧ view.side element = state.view.side element) :
    Step params state .silent (state.replaceView view) :=
  ⟨valid, replaceView_valid valid view ranks agreement, rfl⟩

/-- Every assigned point gap remains synchronized after detached reparenting. -/
theorem replaceView_valuesRealizeGaps {n : ℕ} {state : State n}
    (values : state.ValuesRealizeGaps) (view : HeapView n)
    (ranks : view.rank = state.view.rank) (root : view.root = state.view.root)
    (agreement : ∀ element ∈ state.allElements,
      view.parent element = state.view.parent element ∧ view.side element = state.view.side element) :
    (state.replaceView view).ValuesRealizeGaps := by
  constructor
  · change state.value view.root = 1
    rw [root]
    exact values.1
  · intro block member element inside
    have assigned := State.mem_allElements_iff.mpr ⟨block, member, inside⟩
    change state.value element = Analysis.transientContractedGap (view.rawGap element) block.intervalGap
    simp only [HeapView.rawGap, ranks, (agreement element assigned).1]
    exact values.2 block member element inside

/-- A change of the independent depth witness preserves the full stable
checkpoint when ranks, root, parents and sides agree. -/
theorem replaceView_stable {n : ℕ} {params : Interface.Parameters} {state : State n}
    (stable : state.Stable params) (view : HeapView n)
    (ranks : view.rank = state.view.rank) (root : view.root = state.view.root)
    (parents : view.parent = state.view.parent) (sides : view.side = state.view.side) :
    (state.replaceView view).Stable params := by
  have agreement : ∀ element ∈ state.allElements,
      view.parent element = state.view.parent element ∧ view.side element = state.view.side element := by
    intro element _
    exact ⟨congrFun parents element, congrFun sides element⟩
  have topDown : ∀ owner side, view.topDown owner side = state.view.topDown owner side := by
    intro owner side
    have membership : ∀ element, element ∈ view.topDown owner side ↔ element ∈ state.view.topDown owner side := by
      intro element
      simp only [HeapView.mem_topDown_iff, parents, sides]
    cases side with
    | left =>
        exact List.Pairwise.eq_of_mem_iff (view.topDown_ordered owner).1
          (state.view.topDown_ordered owner).1 membership
    | right =>
        exact List.Pairwise.eq_of_mem_iff (view.topDown_ordered owner).2
          (state.view.topDown_ordered owner).2 membership
  refine ⟨replaceView_valid stable.1 view ranks agreement, ?_, ?_, stable.2.2.2.1, ?_,
    replaceView_valuesRealizeGaps stable.2.2.2.2.2 view ranks root agreement⟩
  · intro element
    change element ∈ state.allElements ↔ view.parent element ≠ none
    rw [parents]
    exact stable.2.1 element
  · intro element owner parent
    change view.rank owner < view.rank element
    rw [ranks]
    change view.parent element = some owner at parent
    rw [parents] at parent
    exact stable.2.2.1 parent
  · intro id
    dsimp only
    intro growing
    obtain ⟨suffix, equation⟩ := stable.2.2.2.2.1 id growing
    exact ⟨suffix, (topDown _ _).trans equation⟩

end State
end Splay.Lazy
