import Splay.Lazy.CutCrossing

namespace Splay.Accounting

open Splay.Lazy

/-- A side interval has only two boundary cuts. Pairwise-disjoint candidate
intervals which meet it without being contained in it can therefore number
at most two. This does not require cross-side unbrokenness. -/
theorem crossing_segments_card_le_two {n : ℕ} {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (candidates : ι → List (Element n))
    {source whole : List (Element n)} (sourceNonempty : source ≠ [])
    (sourceSegment : IsSegment source whole) (side : Side)
    (ordered : whole.Pairwise (fun a b => match side with | .left => a.val < b.val | .right => b.val < a.val))
    (segments : ∀ index ∈ indices, IsSegment (candidates index) whole)
    (disjoint : ∀ first ∈ indices, ∀ second ∈ indices, first ≠ second → List.Disjoint (candidates first) (candidates second))
    (crossing : ∀ index ∈ indices,
      ∃ inside ∈ candidates index, inside ∈ source ∧ ∃ outside ∈ candidates index, outside ∉ source) :
    indices.card ≤ 2 := by
  classical
  have nonempty : source.toFinset.Nonempty := by simpa using sourceNonempty
  let lower := source.toFinset.min' nonempty
  let upper := source.toFinset.max' nonempty
  have lowerMember : lower ∈ source := List.mem_toFinset.mp (Finset.min'_mem _ _)
  have upperMember : upper ∈ source := List.mem_toFinset.mp (Finset.max'_mem _ _)
  have bounds : ∀ element ∈ source, lower.val ≤ element.val ∧ element.val ≤ upper.val := by
    intro element member
    exact ⟨Finset.min'_le _ _ (List.mem_toFinset.mpr member), Finset.le_max' _ _ (List.mem_toFinset.mpr member)⟩
  have outsideBounds : ∀ element ∈ whole, element ∉ source → element.val < lower.val ∨ upper.val < element.val := by
    intro element member outside
    by_contra neither
    have lo : lower.val ≤ element.val := by omega
    have hi : element.val ≤ upper.val := by omega
    have notLow : element ≠ lower := fun equal => outside (equal ▸ lowerMember)
    have notHigh : element ≠ upper := fun equal => outside (equal ▸ upperMember)
    have strictLo : lower.val < element.val := by
      have valuesNe : element.val ≠ lower.val := fun equal => notLow (Fin.ext equal)
      omega
    have strictHi : element.val < upper.val := by
      have valuesNe : element.val ≠ upper.val := fun equal => notHigh (Fin.ext equal)
      omega
    have asymmetric : ∀ {x y : Element n},
        (match side with | .left => x.val < y.val | .right => y.val < x.val) →
        ¬ (match side with | .left => y.val < x.val | .right => x.val < y.val) := by
      intro x y forward reverse
      cases side <;> simp only at forward reverse <;> omega
    apply outside
    cases side with
    | left => exact sourceSegment.mem_of_rel_between ordered asymmetric lowerMember upperMember member strictLo strictHi
    | right => exact sourceSegment.mem_of_rel_between ordered asymmetric upperMember lowerMember member strictHi strictLo
  let crosses := fun (cut : ℕ) (index : ι) =>
    ∃ low ∈ candidates index, ∃ high ∈ candidates index, low.val < cut ∧ cut ≤ high.val
  have uniqueCut : ∀ cut, (indices.filter (crosses cut)).card ≤ 1 := by
    intro cut
    apply Finset.card_le_one.mpr
    intro first firstMember second secondMember
    have first := Finset.mem_filter.mp firstMember
    have second := Finset.mem_filter.mp secondMember
    by_contra different
    obtain ⟨element, inFirst, inSecond⟩ := segments_crossing_cut_overlap (segments _ first.1) (segments _ second.1)
      side ordered cut first.2 second.2
    exact List.disjoint_left.mp (disjoint _ first.1 _ second.1 different) inFirst inSecond
  have cover : indices ⊆ indices.filter (crosses lower.val) ∪ indices.filter (crosses (upper.val + 1)) := by
    intro index member
    obtain ⟨inside, insideCandidate, insideSource, outside, outsideCandidate, outsideSource⟩ := crossing index member
    have insideBounds := bounds inside insideSource
    rcases outsideBounds outside ((segments index member).mem outsideCandidate) outsideSource with below | above
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨member,
        outside, outsideCandidate, inside, insideCandidate, below, insideBounds.1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨member,
        inside, insideCandidate, outside, outsideCandidate, by omega, by omega⟩)
  have count := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have lowCount := uniqueCut lower.val
  have highCount := uniqueCut (upper.val + 1)
  omega

end Splay.Accounting
