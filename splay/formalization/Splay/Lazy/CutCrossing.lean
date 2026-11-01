import Splay.Accounting.CanonicalJunctionSegments

namespace Splay.Lazy

/-- Two contiguous intervals crossing the same numerical cut on the same
side order must overlap. Thus one owner-side slot needs at most one split
for each cut, regardless of its number of blocks. -/
theorem segments_crossing_cut_overlap {n : ℕ} {first second whole : List (Element n)}
    (firstSegment : IsSegment first whole) (secondSegment : IsSegment second whole)
    (side : Side)
    (ordered : whole.Pairwise (fun a b => match side with
      | .left => a.val < b.val
      | .right => b.val < a.val))
    (cut : ℕ)
    (firstCrosses : ∃ low ∈ first, ∃ high ∈ first, low.val < cut ∧ cut ≤ high.val)
    (secondCrosses : ∃ low ∈ second, ∃ high ∈ second, low.val < cut ∧ cut ≤ high.val) :
    ∃ element, element ∈ first ∧ element ∈ second := by
  obtain ⟨a, aIn, aHigh, aHighIn, aLow, aUpper⟩ := firstCrosses
  obtain ⟨b, bIn, bHigh, bHighIn, bLow, bUpper⟩ := secondCrosses
  by_cases equal : a = b
  · exact ⟨b, equal ▸ aIn, bIn⟩
  have valuesNe : a.val ≠ b.val := fun same => equal (Fin.ext same)
  have asymmetric : ∀ {x y : Element n},
      (match side with | .left => x.val < y.val | .right => y.val < x.val) →
      ¬ (match side with | .left => y.val < x.val | .right => x.val < y.val) := by
    intro x y forward reverse
    cases side <;> simp only at forward reverse <;> omega
  by_cases aBefore : a.val < b.val
  · refine ⟨b, ?_, bIn⟩
    cases side with
    | left =>
        exact firstSegment.mem_of_rel_between ordered asymmetric aIn aHighIn
          (secondSegment.mem bIn) aBefore (by omega)
    | right =>
        exact firstSegment.mem_of_rel_between ordered asymmetric aHighIn aIn
          (secondSegment.mem bIn) (by omega) aBefore
  · refine ⟨a, aIn, ?_⟩
    have bBefore : b.val < a.val := by omega
    cases side with
    | left =>
        exact secondSegment.mem_of_rel_between ordered asymmetric bIn bHighIn
          (firstSegment.mem aIn) bBefore (by omega)
    | right =>
        exact secondSegment.mem_of_rel_between ordered asymmetric bHighIn bIn
          (firstSegment.mem aIn) (by omega) bBefore

namespace Block

def CrossesCut {n : ℕ} (cut : ℕ) (block : Block n) : Prop :=
  ∃ low ∈ block.elements, ∃ high ∈ block.elements, low.val < cut ∧ cut ≤ high.val

end Block

namespace State.Valid

/-- Valid disjoint blocks make the interval crossing a fixed cut unique
within each owner and side. -/
theorem blockId_eq_of_crossesCut {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) {firstId secondId : Interface.BlockId} {first second : Block n}
    (firstFound : state.blocks[firstId]? = some first) (secondFound : state.blocks[secondId]? = some second)
    (ownerEq : first.owner = second.owner) (sideEq : first.side = second.side)
    (cut : ℕ) (firstCrosses : first.CrossesCut cut) (secondCrosses : second.CrossesCut cut) :
    firstId = secondId := by
  have firstSegment := (valid.2 first (List.mem_of_getElem? firstFound)).isSegment
  have secondSegment := (valid.2 second (List.mem_of_getElem? secondFound)).isSegment
  rw [← ownerEq, ← sideEq] at secondSegment
  have ordered : (state.view.attachedTopDown state.allElements first.owner first.side).Pairwise
      (fun a b => match first.side with | .left => a.val < b.val | .right => b.val < a.val) := by
    cases side : first.side with
    | left => exact ((state.view.topDown_ordered first.owner).1.filter _)
    | right => exact ((state.view.topDown_ordered first.owner).2.filter _)
  obtain ⟨element, inFirst, inSecond⟩ := segments_crossing_cut_overlap firstSegment secondSegment
    first.side ordered cut firstCrosses secondCrosses
  exact valid.blockId_eq_of_element_mem firstFound inFirst secondFound inSecond

end State.Valid
end Splay.Lazy
