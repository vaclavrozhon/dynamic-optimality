import Splay.Accounting.ComparisonRotationBendGeometry

namespace Splay.Accounting.ComparisonRotationJunctionBound

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.JunctionBendReduction
open Splay.Accounting.ComparisonRotationBendGeometry

/-!
# A unit junction bound for one comparison-tree rotation

A rotation changes the external-depth minimum of an interval only when the
interval straddles the rotated edge.  In that case the minimum switches
between the two rotated value positions.  Consequently, in any fixed splay
tree every junction must be the unique node separating those two keys.

This gives the uniform bound `junctionCount ≤ 1`; neither rotation depth nor
the relevant-neighbor rank bound is needed for this sharper, exact argument.
-/

private theorem isIntervalMin_node_left_iff
    {lower root upper intervalLower intervalUpper candidate : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper)
    (h : intervalUpper < 2 * root + 1) :
    IsIntervalMin (BST.externalDepth (.node left right))
        intervalLower intervalUpper candidate ↔
      IsIntervalMin (BST.externalDepth left)
        intervalLower intervalUpper candidate := by
  apply (Tree.isIntervalMin_congrOn
    (rank₁ := BST.externalDepth (.node left right))
    (rank₂ := fun p => (BST.externalDepth left p).succ) ?_).trans
  · exact Tree.isIntervalMin_succ_iff
  · intro p _ hp
    exact BST.externalDepth_node_of_lt_root left right (by omega)

private theorem isIntervalMin_node_right_iff
    {lower root upper intervalLower intervalUpper candidate : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper)
    (h : 2 * root + 1 < intervalLower) :
    IsIntervalMin (BST.externalDepth (.node left right))
        intervalLower intervalUpper candidate ↔
      IsIntervalMin (BST.externalDepth right)
        intervalLower intervalUpper candidate := by
  apply (Tree.isIntervalMin_congrOn
    (rank₁ := BST.externalDepth (.node left right))
    (rank₂ := fun p => (BST.externalDepth right p).succ) ?_).trans
  · exact Tree.isIntervalMin_succ_iff
  · intro p hp _
    exact BST.externalDepth_node_of_root_lt left right (by omega)

private theorem isIntervalMin_node_root
    {lower root upper intervalLower intervalUpper : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper)
    (hl : intervalLower ≤ 2 * root + 1)
    (hu : 2 * root + 1 ≤ intervalUpper) :
    IsIntervalMin (BST.externalDepth (.node left right))
      intervalLower intervalUpper (2 * root + 1) := by
  refine ⟨hl, hu, ?_⟩
  intro p _ _
  simp only [BST.externalDepth_root]
  exact Nat.zero_le _

private theorem intervalMin_unique_eq
    {lower upper intervalLower intervalUpper first second : ℕ}
    (tree : BST lower upper)
    (il : 2 * lower ≤ intervalLower) (ne : intervalLower ≤ intervalUpper)
    (iu : intervalUpper ≤ 2 * upper)
    (fm : IsIntervalMin tree.externalDepth intervalLower intervalUpper first)
    (sm : IsIntervalMin tree.externalDepth intervalLower intervalUpper second) :
    first = second := by
  obtain ⟨minimum, _, unique⟩ :=
    tree.existsUnique_intervalExternalDepthMin il ne iu
  exact (unique first fm).trans (unique second sm).symm

/--
For a right root rotation, every interval whose minimum changes switches
exactly from the demoted root to the promoted root.
-/
private theorem rightRotation_intervalMin_change
    {lower promoted demoted upper intervalLower intervalUpper
      beforeMin afterMin : ℕ}
    (a : BST lower promoted)
    (b : BST (promoted + 1) demoted)
    (c : BST (demoted + 1) upper)
    (insideLower : 2 * lower ≤ intervalLower)
    (nonempty : intervalLower ≤ intervalUpper)
    (insideUpper : intervalUpper ≤ 2 * upper)
    (beforeIsMin : IsIntervalMin
      (BST.externalDepth (.node (.node a b) c))
        intervalLower intervalUpper beforeMin)
    (afterIsMin : IsIntervalMin
      (BST.externalDepth (.node a (.node b c)))
        intervalLower intervalUpper afterMin)
    (changed : beforeMin ≠ afterMin) :
    beforeMin = 2 * demoted + 1 ∧
      afterMin = 2 * promoted + 1 := by
  have promoted_lt_demoted : promoted < demoted := by
    have := b.lower_le_upper
    omega
  by_cases leftOfDemoted : intervalUpper < 2 * demoted + 1
  · by_cases leftOfPromoted : intervalUpper < 2 * promoted + 1
    · have beforeOuter :=
        (isIntervalMin_node_left_iff (.node a b) c leftOfDemoted).1
          beforeIsMin
      have beforeA :=
        (isIntervalMin_node_left_iff a b leftOfPromoted).1 beforeOuter
      have afterA :=
        (isIntervalMin_node_left_iff a (.node b c) leftOfPromoted).1
          afterIsMin
      exact False.elim (changed
        (intervalMin_unique_eq a insideLower nonempty (by omega)
          beforeA afterA))
    · by_cases rightOfPromoted : 2 * promoted + 1 < intervalLower
      · have beforeOuter :=
          (isIntervalMin_node_left_iff (.node a b) c leftOfDemoted).1
            beforeIsMin
        have beforeB :=
          (isIntervalMin_node_right_iff a b rightOfPromoted).1 beforeOuter
        have afterOuter :=
          (isIntervalMin_node_right_iff a (.node b c) rightOfPromoted).1
            afterIsMin
        have afterB :=
          (isIntervalMin_node_left_iff b c leftOfDemoted).1 afterOuter
        exact False.elim (changed
          (intervalMin_unique_eq b (by omega) nonempty (by omega)
            beforeB afterB))
      · have promotedLower : intervalLower ≤ 2 * promoted + 1 := by omega
        have promotedUpper : 2 * promoted + 1 ≤ intervalUpper := by omega
        have promotedBefore :=
          (isIntervalMin_node_left_iff (.node a b) c leftOfDemoted).2
            (isIntervalMin_node_root a b promotedLower promotedUpper)
        have promotedAfter :=
          isIntervalMin_node_root a (.node b c)
            promotedLower promotedUpper
        have beforeEq := intervalMin_unique_eq (.node (.node a b) c)
          insideLower nonempty insideUpper beforeIsMin promotedBefore
        have afterEq := intervalMin_unique_eq (.node a (.node b c))
          insideLower nonempty insideUpper afterIsMin promotedAfter
        exact False.elim (changed (beforeEq.trans afterEq.symm))
  · by_cases rightOfDemoted : 2 * demoted + 1 < intervalLower
    · have beforeC :=
        (isIntervalMin_node_right_iff (.node a b) c rightOfDemoted).1
          beforeIsMin
      have afterOuter :=
        (isIntervalMin_node_right_iff a (.node b c) (by omega)).1 afterIsMin
      have afterC :=
        (isIntervalMin_node_right_iff b c rightOfDemoted).1 afterOuter
      exact False.elim (changed
        (intervalMin_unique_eq c (by omega) nonempty insideUpper
          beforeC afterC))
    · have demotedLower : intervalLower ≤ 2 * demoted + 1 := by omega
      have demotedUpper : 2 * demoted + 1 ≤ intervalUpper := by omega
      by_cases rightOfPromoted : 2 * promoted + 1 < intervalLower
      · have demotedBefore :=
          isIntervalMin_node_root (.node a b) c demotedLower demotedUpper
        have demotedAfter :=
          (isIntervalMin_node_right_iff a (.node b c) rightOfPromoted).2
            (isIntervalMin_node_root b c demotedLower demotedUpper)
        have beforeEq := intervalMin_unique_eq (.node (.node a b) c)
          insideLower nonempty insideUpper beforeIsMin demotedBefore
        have afterEq := intervalMin_unique_eq (.node a (.node b c))
          insideLower nonempty insideUpper afterIsMin demotedAfter
        exact False.elim (changed (beforeEq.trans afterEq.symm))
      · have promotedLower : intervalLower ≤ 2 * promoted + 1 := by omega
        have promotedUpper : 2 * promoted + 1 ≤ intervalUpper := by omega
        exact
          ⟨intervalMin_unique_eq (.node (.node a b) c)
              insideLower nonempty insideUpper beforeIsMin
              (isIntervalMin_node_root (.node a b) c
                demotedLower demotedUpper),
            intervalMin_unique_eq (.node a (.node b c))
              insideLower nonempty insideUpper afterIsMin
              (isIntervalMin_node_root a (.node b c)
                promotedLower promotedUpper)⟩

/--
All changed interval minima for a transition use one fixed ordered pair of
external value positions.
-/
private def HasMinChangePair
    {lower upper : ℕ} (before after : BST lower upper)
    (beforePosition afterPosition : ℕ) : Prop :=
  ∀ ⦃intervalLower intervalUpper beforeMin afterMin : ℕ⦄,
    2 * lower ≤ intervalLower →
    intervalLower ≤ intervalUpper →
    intervalUpper ≤ 2 * upper →
    IsIntervalMin before.externalDepth
      intervalLower intervalUpper beforeMin →
    IsIntervalMin after.externalDepth
      intervalLower intervalUpper afterMin →
    beforeMin ≠ afterMin →
    beforeMin = beforePosition ∧ afterMin = afterPosition

private theorem HasMinChangePair.leftContext
    {lower root upper beforePosition afterPosition : ℕ}
    {before after : BST lower root}
    (pair : HasMinChangePair before after beforePosition afterPosition)
    (right : BST (root + 1) upper) :
    HasMinChangePair (.node before right) (.node after right)
      beforePosition afterPosition := by
  intro intervalLower intervalUpper beforeMin afterMin
    insideLower nonempty insideUpper beforeIsMin afterIsMin changed
  by_cases leftOnly : intervalUpper < 2 * root + 1
  · exact pair insideLower nonempty (by omega)
      ((isIntervalMin_node_left_iff before right leftOnly).1 beforeIsMin)
      ((isIntervalMin_node_left_iff after right leftOnly).1 afterIsMin)
      changed
  · by_cases rightOnly : 2 * root + 1 < intervalLower
    · have beforeRight :=
        (isIntervalMin_node_right_iff before right rightOnly).1 beforeIsMin
      have afterRight :=
        (isIntervalMin_node_right_iff after right rightOnly).1 afterIsMin
      exact False.elim (changed
        (intervalMin_unique_eq right (by omega) nonempty insideUpper
          beforeRight afterRight))
    · have rootLower : intervalLower ≤ 2 * root + 1 := by omega
      have rootUpper : 2 * root + 1 ≤ intervalUpper := by omega
      have rootBefore :=
        isIntervalMin_node_root before right rootLower rootUpper
      have rootAfter :=
        isIntervalMin_node_root after right rootLower rootUpper
      have beforeEq :=
        intervalMin_unique_eq (.node before right)
          insideLower nonempty insideUpper beforeIsMin rootBefore
      have afterEq :=
        intervalMin_unique_eq (.node after right)
          insideLower nonempty insideUpper afterIsMin rootAfter
      exact False.elim (changed (beforeEq.trans afterEq.symm))

private theorem HasMinChangePair.rightContext
    {lower root upper beforePosition afterPosition : ℕ}
    (left : BST lower root)
    {before after : BST (root + 1) upper}
    (pair : HasMinChangePair before after beforePosition afterPosition) :
    HasMinChangePair (.node left before) (.node left after)
      beforePosition afterPosition := by
  intro intervalLower intervalUpper beforeMin afterMin
    insideLower nonempty insideUpper beforeIsMin afterIsMin changed
  by_cases leftOnly : intervalUpper < 2 * root + 1
  · have beforeLeft :=
      (isIntervalMin_node_left_iff left before leftOnly).1 beforeIsMin
    have afterLeft :=
      (isIntervalMin_node_left_iff left after leftOnly).1 afterIsMin
    exact False.elim (changed
      (intervalMin_unique_eq left insideLower nonempty (by omega)
        beforeLeft afterLeft))
  · by_cases rightOnly : 2 * root + 1 < intervalLower
    · exact pair (by omega) nonempty insideUpper
        ((isIntervalMin_node_right_iff left before rightOnly).1 beforeIsMin)
        ((isIntervalMin_node_right_iff left after rightOnly).1 afterIsMin)
        changed
    · have rootLower : intervalLower ≤ 2 * root + 1 := by omega
      have rootUpper : 2 * root + 1 ≤ intervalUpper := by omega
      have rootBefore :=
        isIntervalMin_node_root left before rootLower rootUpper
      have rootAfter :=
        isIntervalMin_node_root left after rootLower rootUpper
      have beforeEq :=
        intervalMin_unique_eq (.node left before)
          insideLower nonempty insideUpper beforeIsMin rootBefore
      have afterEq :=
        intervalMin_unique_eq (.node left after)
          insideLower nonempty insideUpper afterIsMin rootAfter
      exact False.elim (changed (beforeEq.trans afterEq.symm))

/--
The two positions affected by a contextual rotation are the value positions
of two strictly ordered keys.  The disjunction records rotation orientation.
-/
private theorem exists_orderedMinChangePair
    {depth lower upper : ℕ} {before after : BST lower upper}
    (step : RotationAt depth before after) :
    ∃ low high : ℕ, low < high ∧
      (HasMinChangePair before after
          (2 * high + 1) (2 * low + 1) ∨
       HasMinChangePair before after
          (2 * low + 1) (2 * high + 1)) := by
  induction step with
  | root rootStep =>
      cases rootStep with
      | @right promoted demoted upper a b c =>
          refine ⟨promoted, demoted, ?_, Or.inl ?_⟩
          · have := b.lower_le_upper
            omega
          · intro intervalLower intervalUpper beforeMin afterMin
              insideLower nonempty insideUpper beforeIsMin afterIsMin changed
            exact rightRotation_intervalMin_change
              a b c insideLower nonempty insideUpper
              beforeIsMin afterIsMin changed
      | @left promoted demoted upper a b c =>
          refine ⟨promoted, demoted, ?_, Or.inr ?_⟩
          · have := b.lower_le_upper
            omega
          · intro intervalLower intervalUpper beforeMin afterMin
              insideLower nonempty insideUpper beforeIsMin afterIsMin changed
            have reversed :=
              rightRotation_intervalMin_change
                a b c insideLower nonempty insideUpper
                afterIsMin beforeIsMin changed.symm
            exact ⟨reversed.2, reversed.1⟩
  | leftContext step right ih =>
      obtain ⟨low, high, lowHigh, forward | backward⟩ := ih
      · exact ⟨low, high, lowHigh, Or.inl (forward.leftContext right)⟩
      · exact ⟨low, high, lowHigh, Or.inr (backward.leftContext right)⟩
  | rightContext left step ih =>
      obtain ⟨low, high, lowHigh, forward | backward⟩ := ih
      · exact ⟨low, high, lowHigh, Or.inl (forward.rightContext left)⟩
      · exact ⟨low, high, lowHigh, Or.inr (backward.rightContext left)⟩

private theorem ofTree_intervalMin_isTreeMin
    {n : ℕ} (tree : BST 0 n)
    (lower upper : External n) (nonempty : lower ≤ upper) :
    IsIntervalMin tree.externalDepth lower.val upper.val
      ((Snapshot.ofTree tree).intervalMin lower upper nonempty).val := by
  have minimum :=
    (Snapshot.ofTree tree).intervalMin_isMin lower upper nonempty
  refine ⟨minimum.1, minimum.2.1, ?_⟩
  intro position positionLower positionUpper
  let external : External n :=
    ⟨position, lt_of_le_of_lt positionUpper upper.isLt⟩
  simpa only [Snapshot.ofTree] using
    minimum.2.2 external positionLower positionUpper

/-- A genuine comparison rotation changes interval minima only at a set
of at most two actual external positions. The full numerical rank function
may still change on whole sectors. -/
theorem RotationAt.exists_minimumChangeSupport
    {n depth : ℕ} {before after : BST 0 n}
    (step : RotationAt depth before after) :
    ∃ selected : Finset (External n), selected.card ≤ 2 ∧
      ∀ lower upper (nonempty : lower ≤ upper),
        (Snapshot.ofTree before).intervalMin lower upper nonempty ∉ selected →
        (Snapshot.ofTree after).intervalMin lower upper nonempty =
          (Snapshot.ofTree before).intervalMin lower upper nonempty := by
  classical
  obtain ⟨low, high, _ordered, pair⟩ := exists_orderedMinChangePair step
  let selected : Finset (External n) := Finset.univ.filter fun element =>
    element.val = 2 * low + 1 ∨ element.val = 2 * high + 1
  have selectedCard : selected.card ≤ 2 := by
    have injective : Set.InjOn (fun element : External n => element.val) selected :=
      fun _ _ _ _ equal => Fin.ext equal
    have imageCard := Finset.card_image_iff.mpr injective
    have imageSubset : selected.image (fun element => element.val) ⊆ {2 * low + 1, 2 * high + 1} := by
      intro value member
      obtain ⟨element, inside, rfl⟩ := Finset.mem_image.mp member
      simpa [selected] using inside
    have cardinal := Finset.card_le_card imageSubset
    have pairCard : ({2 * low + 1, 2 * high + 1} : Finset ℕ).card ≤ 2 := by
      simpa using Finset.card_insert_le (2 * low + 1) {2 * high + 1}
    rw [imageCard] at cardinal
    exact cardinal.trans pairCard
  refine ⟨selected, selectedCard, ?_⟩
  intro lower upper nonempty outside
  by_contra changed
  have distinct : ((Snapshot.ofTree before).intervalMin lower upper nonempty).val ≠
      ((Snapshot.ofTree after).intervalMin lower upper nonempty).val := by
    intro equal
    exact changed (Fin.ext equal).symm
  have beforeMin := ofTree_intervalMin_isTreeMin before lower upper nonempty
  have afterMin := ofTree_intervalMin_isTreeMin after lower upper nonempty
  have upperBound : upper.val ≤ 2 * n := by have bound := upper.isLt; omega
  have atSelected : ((Snapshot.ofTree before).intervalMin lower upper nonempty).val = 2 * low + 1 ∨
      ((Snapshot.ofTree before).intervalMin lower upper nonempty).val = 2 * high + 1 := by
    rcases pair with forward | backward
    · exact Or.inr (forward (by omega) nonempty upperBound beforeMin afterMin distinct).1
    · exact Or.inl (backward (by omega) nonempty upperBound beforeMin afterMin distinct).1
  exact outside (by simpa [selected] using atSelected)

private theorem between_of_distinct_branches
    {root low high : ℕ} (lowHigh : low < high)
    {highBranch lowBranch : TernaryBranch}
    (highContains : highBranch.Contains root (2 * high + 1))
    (lowContains : lowBranch.Contains root (2 * low + 1))
    (distinct : highBranch ≠ lowBranch) :
    low ≤ root ∧ root ≤ high := by
  cases highBranch <;> cases lowBranch <;>
    simp_all [TernaryBranch.left_contains_iff,
      TernaryBranch.middle_contains_iff,
      TernaryBranch.right_contains_iff] <;>
    omega

private def Separates
    {n : ℕ} (low high : ℕ) (node : AtNode n) : Prop :=
  node.lower ≤ low ∧ low ≤ node.root ∧
    node.root ≤ high ∧ high < node.upper

/--
Any actual junction in the fixed splay tree separates the two rotated keys.
-/
private theorem junction_separates
    {n : ℕ} {before after : BST 0 n}
    {low high : ℕ} (lowHigh : low < high)
    (pair :
      HasMinChangePair before after (2 * high + 1) (2 * low + 1) ∨
      HasMinChangePair before after (2 * low + 1) (2 * high + 1))
    (node : AtNode n)
    (junction :
      node.heavyBranch (Snapshot.ofTree before) ≠
        node.heavyBranch (Snapshot.ofTree after)) :
    Separates low high node := by
  have isJunction :
      (Snapshot.ofTree before).IsJunction
        (Snapshot.ofTree after)
        node.wholeLower node.wholeUpper node.whole_nonempty node.root := by
    exact junction
  have minimumNe :=
    Snapshot.IsJunction.intervalMin_ne isJunction
  have minimumValNe :
      ((Snapshot.ofTree before).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val ≠
        ((Snapshot.ofTree after).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val := by
    intro valuesEq
    exact minimumNe (Fin.ext valuesEq)
  have beforeTreeMin :=
    ofTree_intervalMin_isTreeMin before
      node.wholeLower node.wholeUpper node.whole_nonempty
  have afterTreeMin :=
    ofTree_intervalMin_isTreeMin after
      node.wholeLower node.wholeUpper node.whole_nonempty
  have beforeContains :=
    node.owner_in_heavyBranch (Snapshot.ofTree before)
  have afterContains :=
    node.owner_in_heavyBranch (Snapshot.ofTree after)
  rcases pair with forward | backward
  · have changed := forward
      (Nat.zero_le _)
      node.whole_nonempty
      (by
        change 2 * node.upper ≤ 2 * n
        exact Nat.mul_le_mul_left 2 node.upper_le_n)
      beforeTreeMin afterTreeMin minimumValNe
    have between :=
      between_of_distinct_branches lowHigh
        (by simpa [AtNode.owner, changed.1] using beforeContains)
        (by simpa [AtNode.owner, changed.2] using afterContains)
        junction
    exact ⟨by
      have beforeLower := beforeTreeMin.1
      have afterLower := afterTreeMin.1
      change 2 * node.lower ≤
        ((Snapshot.ofTree before).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val at beforeLower
      change 2 * node.lower ≤
        ((Snapshot.ofTree after).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val at afterLower
      omega,
      between.1, between.2, by
      have beforeUpper := beforeTreeMin.2.1
      have afterUpper := afterTreeMin.2.1
      change
        ((Snapshot.ofTree before).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val ≤
            2 * node.upper at beforeUpper
      change
        ((Snapshot.ofTree after).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val ≤
            2 * node.upper at afterUpper
      omega⟩
  · have changed := backward
      (Nat.zero_le _)
      node.whole_nonempty
      (by
        change 2 * node.upper ≤ 2 * n
        exact Nat.mul_le_mul_left 2 node.upper_le_n)
      beforeTreeMin afterTreeMin minimumValNe
    have between :=
      between_of_distinct_branches lowHigh
        (by simpa [AtNode.owner, changed.2] using afterContains)
        (by simpa [AtNode.owner, changed.1] using beforeContains)
        junction.symm
    exact ⟨by
      have beforeLower := beforeTreeMin.1
      have afterLower := afterTreeMin.1
      change 2 * node.lower ≤
        ((Snapshot.ofTree before).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val at beforeLower
      change 2 * node.lower ≤
        ((Snapshot.ofTree after).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val at afterLower
      omega,
      between.1, between.2, by
      have beforeUpper := beforeTreeMin.2.1
      have afterUpper := afterTreeMin.2.1
      change
        ((Snapshot.ofTree before).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val ≤
            2 * node.upper at beforeUpper
      change
        ((Snapshot.ofTree after).intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty).val ≤
            2 * node.upper at afterUpper
      omega⟩

private theorem junctionCountFrom_eq_zero_of_upper_le_high
    {n : ℕ} {before after : BST 0 n}
    {low high : ℕ} (lowHigh : low < high)
    (pair :
      HasMinChangePair before after (2 * high + 1) (2 * low + 1) ∨
      HasMinChangePair before after (2 * low + 1) (2 * high + 1))
    {lower upper : ℕ} (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (upper_le_high : upper ≤ high) :
    junctionCountFrom
      (Snapshot.ofTree before) (Snapshot.ofTree after)
      tree upper_le_n = 0 := by
  induction tree with
  | empty =>
      simp [junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      have left_le_n : root ≤ n := by
        have := right.lower_le_upper
        omega
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have branchEq :
          node.heavyBranch (Snapshot.ofTree before) =
            node.heavyBranch (Snapshot.ofTree after) := by
        by_contra branchNe
        have separated :=
          junction_separates lowHigh pair node branchNe
        dsimp [Separates, node] at separated
        exact (by
          have := separated.2.2.2
          omega)
      have leftZero := ihLeft left_le_n (by
        have := right.lower_le_upper
        omega)
      have rightZero := ihRight upper_le_n upper_le_high
      simp only [junctionCountFrom]
      change
        (if node.heavyBranch (Snapshot.ofTree before) =
              node.heavyBranch (Snapshot.ofTree after)
          then 0 else 1) +
            junctionCountFrom
              (Snapshot.ofTree before) (Snapshot.ofTree after)
              left left_le_n +
            junctionCountFrom
              (Snapshot.ofTree before) (Snapshot.ofTree after)
              right upper_le_n = 0
      simp [branchEq, leftZero, rightZero]

private theorem junctionCountFrom_eq_zero_of_low_lt_lower
    {n : ℕ} {before after : BST 0 n}
    {low high : ℕ} (lowHigh : low < high)
    (pair :
      HasMinChangePair before after (2 * high + 1) (2 * low + 1) ∨
      HasMinChangePair before after (2 * low + 1) (2 * high + 1))
    {lower upper : ℕ} (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (low_lt_lower : low < lower) :
    junctionCountFrom
      (Snapshot.ofTree before) (Snapshot.ofTree after)
      tree upper_le_n = 0 := by
  induction tree with
  | empty =>
      simp [junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      have left_le_n : root ≤ n := by
        have := right.lower_le_upper
        omega
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have branchEq :
          node.heavyBranch (Snapshot.ofTree before) =
            node.heavyBranch (Snapshot.ofTree after) := by
        by_contra branchNe
        have separated :=
          junction_separates lowHigh pair node branchNe
        dsimp [Separates, node] at separated
        exact (by
          have := separated.1
          omega)
      have leftZero := ihLeft left_le_n low_lt_lower
      have rightZero := ihRight upper_le_n (by
        have := left.lower_le_upper
        omega)
      simp only [junctionCountFrom]
      change
        (if node.heavyBranch (Snapshot.ofTree before) =
              node.heavyBranch (Snapshot.ofTree after)
          then 0 else 1) +
            junctionCountFrom
              (Snapshot.ofTree before) (Snapshot.ofTree after)
              left left_le_n +
            junctionCountFrom
              (Snapshot.ofTree before) (Snapshot.ofTree after)
              right upper_le_n = 0
      simp [branchEq, leftZero, rightZero]

private theorem junctionCountFrom_le_one_of_orderedMinChangePair
    {n : ℕ} {before after : BST 0 n}
    {low high : ℕ} (lowHigh : low < high)
    (pair :
      HasMinChangePair before after (2 * high + 1) (2 * low + 1) ∨
      HasMinChangePair before after (2 * low + 1) (2 * high + 1))
    {lower upper : ℕ} (tree : BST lower upper)
    (upper_le_n : upper ≤ n) :
    junctionCountFrom
      (Snapshot.ofTree before) (Snapshot.ofTree after)
      tree upper_le_n ≤ 1 := by
  induction tree with
  | empty =>
      simp [junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      have left_le_n : root ≤ n := by
        have := right.lower_le_upper
        omega
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      by_cases root_lt_low : root < low
      · have branchEq :
            node.heavyBranch (Snapshot.ofTree before) =
              node.heavyBranch (Snapshot.ofTree after) := by
          by_contra branchNe
          have separated :=
            junction_separates lowHigh pair node branchNe
          dsimp [Separates, node] at separated
          omega
        have leftZero :=
          junctionCountFrom_eq_zero_of_upper_le_high
            lowHigh pair left left_le_n (by omega)
        have rightBound := ihRight upper_le_n
        simp only [junctionCountFrom]
        change
          (if node.heavyBranch (Snapshot.ofTree before) =
                node.heavyBranch (Snapshot.ofTree after)
            then 0 else 1) +
              junctionCountFrom
                (Snapshot.ofTree before) (Snapshot.ofTree after)
                left left_le_n +
              junctionCountFrom
                (Snapshot.ofTree before) (Snapshot.ofTree after)
                right upper_le_n ≤ 1
        simp only [branchEq, if_true, zero_add, leftZero]
        exact rightBound
      · by_cases high_lt_root : high < root
        · have branchEq :
              node.heavyBranch (Snapshot.ofTree before) =
                node.heavyBranch (Snapshot.ofTree after) := by
            by_contra branchNe
            have separated :=
              junction_separates lowHigh pair node branchNe
            dsimp [Separates, node] at separated
            omega
          have leftBound := ihLeft left_le_n
          have rightZero :=
            junctionCountFrom_eq_zero_of_low_lt_lower
              lowHigh pair right upper_le_n (by omega)
          simp only [junctionCountFrom]
          change
            (if node.heavyBranch (Snapshot.ofTree before) =
                  node.heavyBranch (Snapshot.ofTree after)
              then 0 else 1) +
                junctionCountFrom
                  (Snapshot.ofTree before) (Snapshot.ofTree after)
                  left left_le_n +
                junctionCountFrom
                  (Snapshot.ofTree before) (Snapshot.ofTree after)
                  right upper_le_n ≤ 1
          simp only [branchEq, if_true, zero_add, rightZero, add_zero]
          exact leftBound
        · have leftZero :=
            junctionCountFrom_eq_zero_of_upper_le_high
              lowHigh pair left left_le_n (by omega)
          have rightZero :=
            junctionCountFrom_eq_zero_of_low_lt_lower
              lowHigh pair right upper_le_n (by omega)
          simp only [junctionCountFrom]
          change
            (if node.heavyBranch (Snapshot.ofTree before) =
                  node.heavyBranch (Snapshot.ofTree after)
              then 0 else 1) +
                junctionCountFrom
                  (Snapshot.ofTree before) (Snapshot.ofTree after)
                  left left_le_n +
                junctionCountFrom
                  (Snapshot.ofTree before) (Snapshot.ofTree after)
                  right upper_le_n ≤ 1
          rw [leftZero, rightZero]
          split <;> omega

/--
A single comparison-tree rotation creates at most one heavy-branch junction
in an arbitrary fixed splay tree.
-/
theorem RotationAt.junctionCount_le_one
    {n depth : ℕ} {before after splayTree : BST 0 n}
    (step : RotationAt depth before after) :
    junctionCount
      (Snapshot.ofTree before) (Snapshot.ofTree after) splayTree ≤ 1 := by
  obtain ⟨low, high, lowHigh, pair⟩ :=
    exists_orderedMinChangePair step
  exact junctionCountFrom_le_one_of_orderedMinChangePair
    lowHigh pair splayTree (Nat.le_refl n)

/--
The raw creation bound depends only on the genuine comparison-tree rotation;
no depth or neighboring-rank certificate is required.
-/
theorem RotationAt.created_le_three
    {n depth : ℕ} {before after splayTree : BST 0 n}
    (step : RotationAt depth before after) :
    ((bends (Snapshot.ofTree after) splayTree) \
      (bends (Snapshot.ofTree before) splayTree)).card ≤ 3 := by
  have created :=
    created_le_three_mul_junctionCount
      (Snapshot.ofTree before) (Snapshot.ofTree after) splayTree
  have junctions :=
    RotationAt.junctionCount_le_one (splayTree := splayTree) step
  omega

/-- The exact bend action induced by a raw comparison-tree rotation. -/
noncomputable def RotationAt.comparisonBendAction
    {n depth : ℕ} {before after : BST 0 n}
    (_step : RotationAt depth before after)
    (splayTree : BST 0 n) : BendAction :=
  BendAction.between .comparisonRotation 0 0
    (bends (Snapshot.ofTree before) splayTree)
    (bends (Snapshot.ofTree after) splayTree)

/-- A raw rotation action has its exact singleton finite-set history. -/
theorem RotationAt.comparisonBendAction_history
    {n depth : ℕ} {before after : BST 0 n}
    (step : RotationAt depth before after)
    (splayTree : BST 0 n) :
    FiniteBendHistory n
      (bends (Snapshot.ofTree before) splayTree)
      [RotationAt.comparisonBendAction step splayTree]
      (bends (Snapshot.ofTree after) splayTree) := by
  exact .cons .comparisonRotation 0 0 (.nil _)

/--
The raw rotation action is locally sound for every comparison allowance at
least three, independently of any retained structural-normal-form fields.
-/
theorem RotationAt.comparisonBendAction_locallySound_of_three_le
    {n depth : ℕ} {before after : BST 0 n}
    (step : RotationAt depth before after)
    (splayTree : BST 0 n)
    (constants : BendConstants)
    (allowance : 3 ≤ constants.comparisonRotation) :
    (RotationAt.comparisonBendAction step splayTree).LocallySound
      constants := by
  change
    0 = 0 ∧ 0 = 0 ∧
      ((bends (Snapshot.ofTree after) splayTree) \
        (bends (Snapshot.ofTree before) splayTree)).card ≤
          constants.comparisonRotation
  exact
    ⟨rfl, rfl,
      (RotationAt.created_le_three
        (splayTree := splayTree) step).trans allowance⟩

namespace BoundedComparisonRotation

/-- The residual junction premise is discharged uniformly with budget one. -/
theorem junctionBound_one
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound) :
    context.JunctionBound 1 :=
  RotationAt.junctionCount_le_one context.rotation

/-- One comparison rotation creates at most three bends. -/
theorem created_le_three
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound) :
    ((bends (Snapshot.ofTree afterComparison) splayTree) \
      (bends (Snapshot.ofTree beforeComparison) splayTree)).card ≤ 3 :=
  RotationAt.created_le_three context.rotation

/--
The comparison-rotation bend action is locally sound for every allowance at
least three.
-/
theorem bendAction_locallySound_of_three_le
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound)
    (constants : BendConstants)
    (allowance : 3 ≤ constants.comparisonRotation) :
    context.bendAction.LocallySound constants := by
  exact context.bendAction_locallySound_of_junctionBound
    constants (junctionBound_one context) (by simpa using allowance)

/-- Uniform finite-step packaging for a comparison rotation. -/
noncomputable def finiteBendStep_of_three_le
    {n depth maxRotationDepth neighborRankBound : ℕ}
    {splayTree beforeComparison afterComparison : BST 0 n}
    (context :
      BoundedComparisonRotation
        (depth := depth)
        splayTree beforeComparison afterComparison
        maxRotationDepth neighborRankBound)
    (constants : BendConstants)
    (allowance : 3 ≤ constants.comparisonRotation) :
    LocalFiniteBendStep constants n :=
  context.finiteBendStep_of_junctionBound
    constants (junctionBound_one context) (by simpa using allowance)

end BoundedComparisonRotation

/-- Uniform trace-level comparison-rotation creation bound. -/
theorem structuralTraceRotation_created_le_three
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : Splay.Assumptions.NormalForm.StructuralBounds}
    {trace : Splay.Assumptions.NormalForm.ComparisonTrace n accesses}
    (normal :
      Splay.Assumptions.NormalForm.IsStructurallyNormal bounds trace)
    (splayTree : BST 0 n) (step : Fin trace.rotationCount) :
    ((bends
        (Snapshot.ofTree (trace.state step.succ)) splayTree) \
      (bends
        (Snapshot.ofTree (trace.state step.castSucc)) splayTree)).card ≤
          3 := by
  exact
    BoundedComparisonRotation.created_le_three
      (ComparisonRotationBendGeometry.BoundedComparisonRotation.ofTrace
        normal splayTree step)

end Splay.Accounting.ComparisonRotationJunctionBound
