import Splay.Lazy.UniformRankUpdate
import Splay.Lazy.StableRankUpdate

namespace Splay.Lazy

namespace HeapView

/-- Lower any chosen root children to priority one, retaining the complete
parent structure and its independent depth witness. -/
noncomputable def lowerRootChildren {n : ℕ} (view : HeapView n)
    (selected : Finset (Element n)) : HeapView n :=
  { view with rank := fun element => if element ∈ selected then 1 else view.rank element }

theorem lowerRootChildren_sameStructure {n : ℕ} (view : HeapView n)
    (selected : Finset (Element n)) : view.SameStructure (view.lowerRootChildren selected) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lowerRootChildren_ordered {n : ℕ} {view : HeapView n}
    (ordered : view.HeapOrdered) (zero : view.rank view.root = 0)
    (selected : Finset (Element n))
    (parents : ∀ element ∈ selected, view.parent element = some view.root) :
    (view.lowerRootChildren selected).HeapOrdered := by
  have rootOutside : view.root ∉ selected := by
    intro member
    have impossible := parents _ member
    rw [view.root_parent] at impossible
    contradiction
  intro element owner parent
  change view.parent element = some owner at parent
  change (if owner ∈ selected then 1 else view.rank owner) <
    (if element ∈ selected then 1 else view.rank element)
  by_cases elementSelected : element ∈ selected
  · have ownerRoot : owner = view.root := Option.some.inj (parent.symm.trans (parents _ elementSelected))
    simp [elementSelected, ownerRoot, rootOutside, zero]
  · by_cases ownerSelected : owner ∈ selected
    · have positive := ordered (parents _ ownerSelected)
      have strict := ordered parent
      simp only [elementSelected, ownerSelected, ↓reduceIte]
      rw [zero] at positive
      omega
    · simpa [elementSelected, ownerSelected] using ordered parent

end HeapView

namespace State

/-- A finite rank-change set is prepared when its elements are isolated in
shrinking singleton blocks and all its own growing intervals are empty. -/
structure IsolatedRanks {n : ℕ} (state : State n) (selected : Finset (Element n)) : Prop where
  growingEmpty : ∀ block ∈ state.blocks, block.mode = .growing →
    block.owner ∈ selected → block.elements = []
  singleton : ∀ element ∈ selected, ∀ block ∈ state.blocks, element ∈ block.elements →
    block.mode = .shrinking ∧ block.elements = [element]

/-- The offset is computed from a block's actual first element. Empty and
growing intervals retain their mandatory zero offset. -/
noncomputable def isolatedRankBlockShift {n : ℕ} (state : State n)
    (afterView : HeapView n) (block : Block n) : ℤ :=
  if block.mode = .growing then 0 else
    match block.elements with
    | [] => 0
    | element :: _ => afterView.rawGap element - state.view.rawGap element

namespace IsolatedRanks

variable {n : ℕ} {state : State n} {selected : Finset (Element n)}
  (prepared : state.IsolatedRanks selected)
  {params : Interface.Parameters} (valid : state.Valid params)
  {afterView : HeapView n} (same : state.view.SameStructure afterView)
  (ordinary : ∀ element ∉ selected, afterView.rank element = state.view.rank element)

include prepared valid same ordinary in
theorem growing_rawGap {block : Block n} (member : block ∈ state.blocks)
    (growing : block.mode = .growing) :
    ∀ element ∈ block.elements, afterView.rawGap element = state.view.rawGap element := by
  intro element inside
  have ownerOrdinary : block.owner ∉ selected := by
    intro marked
    rw [prepared.growingEmpty block member growing marked] at inside
    simp at inside
  have elementOrdinary : element ∉ selected := by
    intro marked
    have shrinking := (prepared.singleton element marked block member inside).1
    rw [growing] at shrinking
    contradiction
  simp only [HeapView.rawGap, same.parent_apply, (valid.2 block member).parent_eq inside,
    ordinary element elementOrdinary, ordinary block.owner ownerOrdinary]

include prepared valid same ordinary in
theorem block_rawGap {block : Block n} (member : block ∈ state.blocks)
    (shrinking : block.mode = .shrinking) (nonempty : block.elements ≠ []) :
    ∀ element ∈ block.elements, afterView.rawGap element = state.view.rawGap element +
      state.isolatedRankBlockShift afterView block := by
  cases elements : block.elements with
  | nil => exact (nonempty elements).elim
  | cons first rest =>
      have firstMember : first ∈ block.elements := by simp [elements]
      intro element inside
      have inside : element ∈ block.elements := by simpa [elements] using inside
      have parentFirst := (valid.2 block member).parent_eq firstMember
      have parentElement := (valid.2 block member).parent_eq inside
      by_cases firstSelected : first ∈ selected
      · have singleton := (prepared.singleton first firstSelected block member firstMember).2
        have equal : element = first := by simpa [singleton] using inside
        subst element
        simp only [isolatedRankBlockShift, shrinking, reduceCtorEq, ↓reduceIte, elements]
        omega
      · have elementOrdinary : element ∉ selected := by
          intro marked
          have singleton := (prepared.singleton element marked block member inside).2
          have equal : first = element := by simpa [singleton] using firstMember
          exact firstSelected (equal ▸ marked)
        simp only [isolatedRankBlockShift, shrinking, reduceCtorEq, ↓reduceIte, elements,
          HeapView.rawGap, same.parent_apply, parentFirst, parentElement,
          ordinary first firstSelected, ordinary element elementOrdinary]
        omega

include prepared valid same ordinary in
/-- Uniformity of every block is derived from the actual finite isolation
preparation; no per-element gap obligations remain for the caller. -/
theorem compatible : state.RankUpdateCompatible afterView (state.isolatedRankBlockShift afterView) := by
  refine ⟨same, ?_⟩
  intro block member
  cases mode : block.mode with
  | growing =>
      simp only [Block.AbsorbsRankUpdate, mode]
      exact ⟨by simp [isolatedRankBlockShift, mode], prepared.growing_rawGap valid same ordinary member mode⟩
  | shrinking =>
      simp only [Block.AbsorbsRankUpdate, mode]
      by_cases empty : block.elements = []
      · exact Or.inl ⟨empty, by simp [isolatedRankBlockShift, mode, empty]⟩
      · exact Or.inr ⟨empty, prepared.block_rawGap valid same ordinary member mode empty⟩

include prepared same ordinary in
/-- A prepared finite rank change is one silent trace and preserves the
stable checkpoint whenever the target ranks order the unchanged heap. -/
theorem trace_stable (stable : state.Stable params) (ordered : afterView.HeapOrdered) :
    Trace params state [.silent]
        (state.absorbRankUpdate afterView (state.isolatedRankBlockShift afterView)) ∧
      (state.absorbRankUpdate afterView (state.isolatedRankBlockShift afterView)).Stable params :=
  stable.rankPrepared.absorbRankUpdate_trace_stable
    (prepared.compatible stable.1 same ordinary) ordered

include prepared in
/-- In particular, installing the manuscript's artificial boundary priority
requires no insert, pass, split or value increase after isolation. -/
theorem lowerRootChildren_trace_stable (stable : state.Stable params)
    (zero : state.view.rank state.view.root = 0)
    (parents : ∀ element ∈ selected, state.view.parent element = some state.view.root) :
    let afterView := state.view.lowerRootChildren selected
    Trace params state [.silent]
        (state.absorbRankUpdate afterView (state.isolatedRankBlockShift afterView)) ∧
      (state.absorbRankUpdate afterView (state.isolatedRankBlockShift afterView)).Stable params := by
  apply prepared.trace_stable (state.view.lowerRootChildren_sameStructure selected) _ stable
    (HeapView.lowerRootChildren_ordered stable.2.2.1 zero selected parents)
  intro element outside
  simp [HeapView.lowerRootChildren, outside]

end IsolatedRanks
end State
end Splay.Lazy
