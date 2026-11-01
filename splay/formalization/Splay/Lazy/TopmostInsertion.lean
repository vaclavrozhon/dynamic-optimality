import Splay.Lazy.DetachedReparenting
import Splay.Lazy.SafeInsertCost

namespace Splay.Lazy

/-- Assigning an unassigned first child adds just that child to the attached
order of its placement. -/
theorem HeapView.attachedTopDown_assign_first {n : ℕ} (view : HeapView n)
    {assigned afterAssigned : List (Element n)} {element owner : Element n} {side : Side}
    (unassigned : element ∉ assigned)
    (assignedIff : ∀ queried, queried ∈ afterAssigned ↔ queried = element ∨ queried ∈ assigned)
    {tail : List (Element n)} (first : view.topDown owner side = element :: tail) :
    view.attachedTopDown afterAssigned owner side =
      element :: view.attachedTopDown assigned owner side := by
  have tailFresh : element ∉ tail := (List.nodup_cons.mp (first ▸ view.topDown_nodup owner side)).1
  have assignedNow : element ∈ afterAssigned := (assignedIff element).mpr (Or.inl rfl)
  unfold HeapView.attachedTopDown
  rw [first]
  simp only [List.filter_cons, assignedNow, unassigned, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply List.filter_congr
  intro queried member
  have different : queried ≠ element := by intro equal; subst queried; exact tailFresh member
  simp [assignedIff, different]

/-- Other placements retain their entire attached order when this element is
assigned. -/
theorem HeapView.attachedTopDown_assign_other {n : ℕ} (view : HeapView n)
    {assigned afterAssigned : List (Element n)} {element owner : Element n} {side : Side}
    (assignedIff : ∀ queried, queried ∈ afterAssigned ↔ queried = element ∨ queried ∈ assigned)
    (outside : element ∉ view.topDown owner side) :
    view.attachedTopDown afterAssigned owner side =
      view.attachedTopDown assigned owner side := by
  unfold HeapView.attachedTopDown
  apply List.filter_congr
  intro queried member
  have different : queried ≠ element := by intro equal; subst queried; exact outside member
  simp [assignedIff, different]

namespace State

/-- An outermost insertion into any growing block has the exact safe-insert
trace; no atomization or conversion of its existing contents is needed. -/
theorem safeInsert_trace_of_first {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) {blockId : Interface.BlockId} {block : Block n}
    (found : state.blocks[blockId]? = some block) (growing : block.mode = .growing)
    (element : Element n) (unassigned : element ∉ state.allElements)
    (elementGap : 0 ≤ state.view.rawGap element)
    (first : ∃ suffix, state.view.topDown block.owner block.side =
      element :: block.elements ++ suffix) :
    Trace params state (state.safeInsertEvents blockId block element) (state.insert blockId element) := by
  obtain ⟨suffix, first⟩ := first
  have assignedIff := Canonical.mem_insert_allElements_iff state blockId block element
  have assignedIff' : ∀ queried, queried ∈ (state.insert blockId element).allElements ↔
      queried = element ∨ queried ∈ state.allElements := fun queried => assignedIff queried found
  have first' : state.view.topDown block.owner block.side = element :: (block.elements ++ suffix) := first
  have attached := state.view.attachedTopDown_assign_first unassigned assignedIff' first'
  have elementTop : element ∈ state.view.topDown block.owner block.side := by simp [first']
  have elementPlacement := state.view.mem_topDown_iff.mp elementTop
  apply state.safeInsert_trace blockId block element valid found growing unassigned elementGap
  · have allAssigned : ∀ queried ∈ block.elements, decide (queried ∈ state.allElements) = true := by
      intro queried member
      exact decide_eq_true (State.mem_allElements_iff.mpr ⟨block, List.mem_of_getElem? found, member⟩)
    change IsSegment (element :: block.elements) _
    rw [attached]
    refine ⟨[], suffix.filter (fun queried => decide (queried ∈ state.allElements)), ?_⟩
    simp only [HeapView.attachedTopDown, first', List.filter_cons, unassigned,
      decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_append,
      List.filter_eq_self.mpr allAssigned, List.nil_append, List.cons_append]
  · intro id different
    let other := state.blocks.get id
    have original := valid.2 other (List.get_mem _ id)
    refine ⟨?_, original.2⟩
    by_cases placement : other.owner = block.owner ∧ other.side = block.side
    · change IsSegment other.elements (state.view.attachedTopDown
        (state.insert blockId element).allElements other.owner other.side)
      rw [placement.1, placement.2, attached]
      have oldSegment := original.1
      rw [placement.1, placement.2] at oldSegment
      obtain ⟨front, back, decomposition⟩ := oldSegment
      exact ⟨element :: front, back, by simp [decomposition, List.cons_append]⟩
    · have outside : element ∉ state.view.topDown other.owner other.side := by
        intro member
        have otherPlacement := state.view.mem_topDown_iff.mp member
        apply placement
        exact ⟨Option.some.inj (otherPlacement.1.symm.trans elementPlacement.1),
          otherPlacement.2.symm.trans elementPlacement.2⟩
      rw [state.view.attachedTopDown_assign_other assignedIff' outside]
      exact original.1

end State
end Splay.Lazy
