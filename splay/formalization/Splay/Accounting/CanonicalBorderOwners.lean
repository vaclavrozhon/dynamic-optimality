import Splay.Rank.CoveringMinima
import Splay.Accounting.CanonicalJunctionParentCells
import Splay.Lazy.CutCrossing

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical

/-- Every canonical parent edge is witnessed by an actual attachment
interval containing its child and minimized by its owner. -/
theorem edge_owner_interval {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upperBound : upper ≤ n) (depth : ℕ)
    {edge : Edge n} (member : edge ∈ treeEdges snapshot tree upperBound depth) :
    ∃ (low high : External n), IsIntervalMin snapshot.rank low high edge.owner ∧ low ≤ edge.child ∧ edge.child ≤ high := by
  induction tree generalizing depth with
  | empty => simp [treeEdges] at member
  | @node lower root upper left right ihLeft ihRight =>
      simp only [treeEdges, List.mem_append] at member
      rcases member with (localEdge | leftEdge) | rightEdge
      · let node : AtNode n := ⟨lower, root, upper, left, right, upperBound⟩
        obtain ⟨branch, _, equal⟩ := List.mem_map.mp localEdge
        subst edge
        exact ⟨node.wholeLower, node.wholeUpper, node.owner_isMin snapshot, node.branchMin_in_whole snapshot branch⟩
      · exact ihLeft _ _ leftEdge
      · exact ihRight _ _ rightEdge

theorem canonicalParent_owner_interval {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {child owner : External n} (parent : canonicalParent snapshot tree child = some owner) :
    ∃ (low high : External n), IsIntervalMin snapshot.rank low high owner ∧ low ≤ child ∧ child ≤ high := by
  obtain ⟨edge, member, ownerEq, childEq⟩ := JunctionBendReduction.exists_edge_of_canonicalParent snapshot tree parent
  simpa only [ownerEq, childEq] using edge_owner_interval snapshot tree (Nat.le_refl n) 0 member

/-- Two intervals with the same actual minimum can be united without
changing their minimum, since they overlap at that minimum. -/
theorem intervalMin_union_same {n : ℕ} (snapshot : Snapshot n)
    {firstLower firstUpper secondLower secondUpper owner : External n}
    (first : IsIntervalMin snapshot.rank firstLower firstUpper owner)
    (second : IsIntervalMin snapshot.rank secondLower secondUpper owner) :
    IsIntervalMin snapshot.rank (min firstLower secondLower) (max firstUpper secondUpper) owner := by
  refine ⟨(min_le_left _ _).trans first.1, first.2.1.trans (le_max_left _ _), ?_⟩
  intro element atLower atUpper
  by_cases inFirst : firstLower ≤ element ∧ element ≤ firstUpper
  · exact first.2.2 element inFirst.1 inFirst.2
  · have inSecond : secondLower ≤ element ∧ element ≤ secondUpper := by
      have lowerCases := min_le_iff.mp atLower
      have upperCases := le_max_iff.mp atUpper
      have firstLow := first.1
      have firstHigh := first.2.1
      have secondLow := second.1
      have secondHigh := second.2.1
      rcases lowerCases with low | low <;> rcases upperCases with high | high <;>
        simp only [Fin.le_def] at * <;> omega
    exact second.2.2 element inSecond.1 inSecond.2

/-- An owner of children straddling a border is one of the boundedly many
interval minima covering that border. The children may have different
attachment nodes along their shared owner path. -/
theorem canonicalOwner_mem_coveringMinima_of_between_children {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {first second owner border : External n}
    (firstParent : canonicalParent snapshot tree first = some owner)
    (secondParent : canonicalParent snapshot tree second = some owner)
    (between : first ≤ border ∧ border ≤ second) : owner ∈ snapshot.coveringMinima border := by
  obtain ⟨fl, fu, fm, flc, fuc⟩ := canonicalParent_owner_interval snapshot tree firstParent
  obtain ⟨sl, su, sm, slc, suc⟩ := canonicalParent_owner_interval snapshot tree secondParent
  have minimum := intervalMin_union_same snapshot fm sm
  have nonempty : min fl sl ≤ max fu su := minimum.1.trans minimum.2.1
  apply (snapshot.mem_coveringMinima border owner).mpr
  exact ⟨min fl sl, max fu su, nonempty,
    (min_le_left _ _).trans (flc.trans between.1), (between.2.trans suc).trans (le_max_right _ _),
    (snapshot.intervalMin_unique _ _ nonempty minimum).symm⟩

/-- The same covering-minimum bound applies when a growing interval's
owner and one child lie in different numerical rank-update sectors. -/
theorem canonicalOwner_mem_coveringMinima_of_between_parent_child {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    {child owner border : External n} (parent : canonicalParent snapshot tree child = some owner)
    (between : (owner ≤ border ∧ border ≤ child) ∨ (child ≤ border ∧ border ≤ owner)) :
    owner ∈ snapshot.coveringMinima border := by
  obtain ⟨low, high, minimum, childLow, childHigh⟩ := canonicalParent_owner_interval snapshot tree parent
  have contains : low ≤ border ∧ border ≤ high := by
    rcases between with forward | backward
    · exact ⟨minimum.1.trans forward.1, forward.2.trans childHigh⟩
    · exact ⟨childLow.trans backward.1, backward.2.trans minimum.2.1⟩
  have nonempty := minimum.1.trans minimum.2.1
  exact (snapshot.mem_coveringMinima border owner).mpr
    ⟨low, high, nonempty, contains.1, contains.2, (snapshot.intervalMin_unique _ _ nonempty minimum).symm⟩

/-- Either endpoint of the adjacent pair defining a numerical cut may be
chosen as its border witness; this lets the caller choose the lower rank. -/
theorem canonicalBlock_owner_mem_coveringMinima_of_crossesCut {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} (valid : state.Valid params) (snapshot : Snapshot n) (tree : BST 0 n)
    (viewEq : state.view = canonicalHeapView snapshot tree) {block : Block n} (member : block ∈ state.blocks)
    (cut : ℕ) (border : External n) (adjacent : border.val = cut ∨ border.val + 1 = cut)
    (crossing : block.CrossesCut cut) : block.owner ∈ snapshot.coveringMinima border := by
  obtain ⟨low, lowIn, high, highIn, lowBound, highBound⟩ := crossing
  have lowParent := (valid.2 block member).parent_eq lowIn
  have highParent := (valid.2 block member).parent_eq highIn
  rw [viewEq] at lowParent highParent
  apply canonicalOwner_mem_coveringMinima_of_between_children snapshot tree lowParent highParent
  simp only [Fin.le_def]
  omega

end Splay.Accounting
