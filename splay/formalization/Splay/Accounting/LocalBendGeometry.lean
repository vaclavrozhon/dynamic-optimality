import Splay.Accounting.ZigZagBend
import Splay.Lazy.Canonical
import Splay.Rank.FromTree

namespace Splay.Accounting.LocalBendGeometry

open Splay.Rank
open Splay.Tree
open Splay.Lazy.Canonical

/--
The two consecutive heavy edges at an internal node turn in opposite
left/right directions.

`incoming = none` means that the node is the top of its heavy path.  A
middle heavy branch ends at the value stored at the node, so it cannot form
a bend with an internal child.
-/
def Turns (incoming : Option TernaryBranch)
    (outgoing : TernaryBranch) : Prop :=
  (incoming = some .left ∧ outgoing = .right) ∨
    (incoming = some .right ∧ outgoing = .left)

instance (incoming : Option TernaryBranch)
    (outgoing : TernaryBranch) : Decidable (Turns incoming outgoing) :=
  inferInstanceAs (Decidable
    ((incoming = some .left ∧ outgoing = .right) ∨
      (incoming = some .right ∧ outgoing = .left)))

/--
The incoming-heavy-edge information passed to a binary child.

Only the child selected by the parent's canonical heavy branch receives an
incoming heavy edge.  A middle branch, or the sibling of the selected child,
starts a new heavy path.
-/
def childIncoming (outgoing child : TernaryBranch) :
    Option TernaryBranch :=
  if outgoing = child then some child else none

/-- The possible bend contributed by one internal key. -/
def bendAt {n : ℕ} (key : Fin n)
    (incoming : Option TernaryBranch)
    (outgoing : TernaryBranch) : Finset (Fin n) :=
  if Turns incoming outgoing then {key} else ∅

/--
All genuine heavy-path bends in an indexed splay-tree subtree.

The comparison-rank snapshot selects the outgoing heavy branch.  The
`incoming` parameter records the orientation of the heavy edge entering the
subtree root, if there is one.  Recursion then passes an incoming edge only
to the selected binary heavy child.
-/
noncomputable def bendsFrom
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) : Finset (Fin n) :=
  match tree with
  | .empty _ => ∅
  | .node (root := root) left right =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      let outgoing := node.heavyBranch snapshot
      let key : Fin n := ⟨root, by
        have hRight := right.lower_le_upper
        omega⟩
      bendAt key incoming outgoing ∪
        (bendsFrom snapshot left (by
            have hRight := right.lower_le_upper
            omega)
          (childIncoming outgoing .left) ∪
         bendsFrom snapshot right upper_le_n
          (childIncoming outgoing .right))
termination_by tree.size
decreasing_by
  all_goals simp [BST.size] <;> omega

/-- The finite set of bends of a complete `n`-key tree. -/
noncomputable def bends {n : ℕ} (snapshot : Snapshot n)
    (tree : BST 0 n) : Finset (Fin n) :=
  bendsFrom snapshot tree (Nat.le_refl n) none

/--
The local finite-set fragment needed to assemble a global
`FiniteZigZagBendWitness`: one exact action, its two actual bend sets, the
singleton finite history, and local soundness.
-/
structure LocalFiniteBendStep
    (constants : BendConstants) (n : ℕ) where
  beforeBends : Finset (Fin n)
  afterBends : Finset (Fin n)
  action : BendAction
  history :
    FiniteBendHistory n beforeBends [action] afterBends
  locallySound :
    action.LocallySound constants

theorem card_sdiff_le_card_left
    {α : Type*} [DecidableEq α] (left right : Finset α) :
    (left \ right).card ≤ left.card :=
  Finset.card_le_card Finset.sdiff_subset

/--
Created elements of a union inject into the union of the elements created
by its two corresponding components.
-/
theorem card_sdiff_union_le_add
    {α : Type*} [DecidableEq α]
    (after₁ after₂ before₁ before₂ : Finset α) :
    ((after₁ ∪ after₂) \ (before₁ ∪ before₂)).card ≤
      (after₁ \ before₁).card + (after₂ \ before₂).card := by
  have subset :
      (after₁ ∪ after₂) \ (before₁ ∪ before₂) ⊆
        (after₁ \ before₁) ∪ (after₂ \ before₂) := by
    intro element member
    simp only [Finset.mem_sdiff, Finset.mem_union] at member ⊢
    tauto
  exact
    (Finset.card_le_card subset).trans
      (Finset.card_union_le (after₁ \ before₁) (after₂ \ before₂))

/-- Adding the same component on both sides cannot create new elements. -/
theorem card_sdiff_union_same_le
    {α : Type*} [DecidableEq α]
    (after before common : Finset α) :
    ((after ∪ common) \ (before ∪ common)).card ≤
      (after \ before).card := by
  have subset :
      (after ∪ common) \ (before ∪ common) ⊆
        after \ before := by
    intro element member
    simp only [Finset.mem_sdiff, Finset.mem_union] at member ⊢
    tauto
  exact Finset.card_le_card subset

/-- The same monotonicity when the common component is written first. -/
theorem card_sdiff_same_union_le
    {α : Type*} [DecidableEq α]
    (common after before : Finset α) :
    ((common ∪ after) \ (common ∪ before)).card ≤
      (after \ before).card := by
  have subset :
      (common ∪ after) \ (common ∪ before) ⊆
        after \ before := by
    intro element member
    simp only [Finset.mem_sdiff, Finset.mem_union] at member ⊢
    tauto
  exact Finset.card_le_card subset

private def unionSeven {α : Type*} [DecidableEq α]
    (first second third fourth fifth sixth seventh : Finset α) :
    Finset α :=
  first ∪ (second ∪ (third ∪
    (fourth ∪ (fifth ∪ (sixth ∪ seventh)))))

private theorem card_unionSeven_le
    {α : Type*} [DecidableEq α]
    (first second third fourth fifth sixth seventh : Finset α) :
    (unionSeven first second third fourth fifth sixth seventh).card ≤
      first.card + second.card + third.card + fourth.card +
        fifth.card + sixth.card + seventh.card := by
  unfold unionSeven
  have h₁ := Finset.card_union_le sixth seventh
  have h₂ := Finset.card_union_le fifth (sixth ∪ seventh)
  have h₃ :=
    Finset.card_union_le fourth
      (fifth ∪ (sixth ∪ seventh))
  have h₄ :=
    Finset.card_union_le third
      (fourth ∪ (fifth ∪ (sixth ∪ seventh)))
  have h₅ :=
    Finset.card_union_le second
      (third ∪ (fourth ∪ (fifth ∪ (sixth ∪ seventh))))
  have h₆ :=
    Finset.card_union_le first
      (second ∪
        (third ∪ (fourth ∪ (fifth ∪ (sixth ∪ seventh)))))
  omega

/--
Seven local components, each of which can create at most one identity,
jointly create at most seven identities.
-/
private theorem card_sdiff_unionSeven_le_seven
    {α : Type*} [DecidableEq α]
    (after₁ after₂ after₃ after₄ after₅ after₆ after₇ :
      Finset α)
    (before₁ before₂ before₃ before₄ before₅ before₆ before₇ :
      Finset α)
    (h₁ : (after₁ \ before₁).card ≤ 1)
    (h₂ : (after₂ \ before₂).card ≤ 1)
    (h₃ : (after₃ \ before₃).card ≤ 1)
    (h₄ : (after₄ \ before₄).card ≤ 1)
    (h₅ : (after₅ \ before₅).card ≤ 1)
    (h₆ : (after₆ \ before₆).card ≤ 1)
    (h₇ : (after₇ \ before₇).card ≤ 1) :
    ((unionSeven after₁ after₂ after₃ after₄ after₅ after₆ after₇) \
      (unionSeven before₁ before₂ before₃ before₄ before₅ before₆
        before₇)).card ≤ 7 := by
  have subset :
      (unionSeven after₁ after₂ after₃ after₄ after₅ after₆ after₇) \
          (unionSeven before₁ before₂ before₃ before₄ before₅ before₆
            before₇) ⊆
        unionSeven
          (after₁ \ before₁) (after₂ \ before₂)
          (after₃ \ before₃) (after₄ \ before₄)
          (after₅ \ before₅) (after₆ \ before₆)
          (after₇ \ before₇) := by
    intro element member
    simp only [Finset.mem_sdiff, Finset.mem_union, unionSeven] at member ⊢
    tauto
  have cardSubset := Finset.card_le_card subset
  have cardUnion :=
    card_unionSeven_le
      (after₁ \ before₁) (after₂ \ before₂)
      (after₃ \ before₃) (after₄ \ before₄)
      (after₅ \ before₅) (after₆ \ before₆)
      (after₇ \ before₇)
  omega

@[simp]
theorem bendAt_card_le_one {n : ℕ} (key : Fin n)
    (incoming : Option TernaryBranch)
    (outgoing : TernaryBranch) :
    (bendAt key incoming outgoing).card ≤ 1 := by
  unfold bendAt
  split <;> simp

/--
Changing only whether the root is entered by a heavy edge can change at most
the root bend.  All descendant incoming-heavy-edge data is selected solely
by the subtree's own outgoing heavy branches.
-/
theorem bendsFrom_sdiff_le_one
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (afterIncoming beforeIncoming : Option TernaryBranch) :
    ((bendsFrom snapshot tree upper_le_n afterIncoming) \
      (bendsFrom snapshot tree upper_le_n beforeIncoming)).card ≤ 1 := by
  cases tree with
  | empty boundary =>
      simp [bendsFrom]
  | @node lower root upper left right =>
      simp only [bendsFrom]
      apply le_trans
        (card_sdiff_union_same_le
          (bendAt ⟨root, by
              have hRight := right.lower_le_upper
              omega⟩ afterIncoming
            (({
              lower := lower
              root := root
              upper := upper
              left := left
              right := right
              upper_le_n := upper_le_n
            } : AtNode n).heavyBranch snapshot))
          (bendAt ⟨root, by
              have hRight := right.lower_le_upper
              omega⟩ beforeIncoming
            (({
              lower := lower
              root := root
              upper := upper
              left := left
              right := right
              upper_le_n := upper_le_n
            } : AtNode n).heavyBranch snapshot))
          _)
      exact
        (card_sdiff_le_card_left _ _).trans
          (bendAt_card_le_one _ _ _)

/-- Every recorded bend key lies in the indexed subtree that generated it. -/
theorem mem_bendsFrom_bounds
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) {key : Fin n}
    (member : key ∈ bendsFrom snapshot tree upper_le_n incoming) :
    lower ≤ key.val ∧ key.val < upper := by
  induction tree generalizing incoming with
  | empty boundary =>
      simp [bendsFrom] at member
  | @node lower root upper left right ihLeft ihRight =>
      simp only [bendsFrom, Finset.mem_union] at member
      rcases member with atRoot | inChildren
      · have key_eq : key.val = root := by
          unfold bendAt at atRoot
          split at atRoot
          · simpa using congrArg Fin.val (Finset.mem_singleton.mp atRoot)
          · simp at atRoot
        have hLeft := left.lower_le_upper
        have hRight := right.lower_le_upper
        omega
      · rcases inChildren with inLeft | inRight
        · have bounds :=
            ihLeft (by
              have hRight := right.lower_le_upper
              omega) _ inLeft
          have hRight := right.lower_le_upper
          omega
        · have bounds := ihRight upper_le_n _ inRight
          have hLeft := left.lower_le_upper
          omega

/--
If a comparison tree has `key` at its root, the value position of `key` is
the canonical minimum-rank external node of the complete inorder interval.

This is the bridge from `ComparisonTrace.serves` to the owner hypothesis used
by the local zig-zag witnesses below.
-/
theorem globalIntervalMin_eq_valuePos_of_hasRoot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val) :
    let lower : External n := ⟨0, by omega⟩
    let upper : External n := ⟨2 * n, by omega⟩
    (Snapshot.ofTree comparison).intervalMin lower upper (by
      change (0 : ℕ) ≤ 2 * n
      omega) = valuePos key := by
  let lower : External n := ⟨0, by omega⟩
  let upper : External n := ⟨2 * n, by omega⟩
  have rankZero :
      (Snapshot.ofTree comparison).rank (valuePos key) = 0 := by
    obtain ⟨left, right, comparison_eq⟩ := root
    subst comparison
    simp [Snapshot.ofTree, valuePos]
  have valueMin :
      IsIntervalMin (Snapshot.ofTree comparison).rank
        lower upper (valuePos key) := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 ≤ 2 * key.val + 1
      omega
    · change 2 * key.val + 1 ≤ 2 * n
      have := key.isLt
      omega
    · intro node _ _
      rw [rankZero]
      exact Nat.zero_le _
  exact
    ((Snapshot.ofTree comparison).intervalMin_unique
      lower upper (by
        simp only [lower, upper, Fin.mk_le_mk]
        omega) valueMin).symm

/--
A left-right zig-zag changes bend status only at its three internal rotation
keys and at the roots of the four hanging subtrees.  Consequently it creates
at most seven bends, independently of the ranks and independently of whether
the local rotation root is entered by a heavy edge.
-/
theorem zigZagLeftRight_created_le_seven
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    ((bendsFrom snapshot
        (.node (.node a b) (.node c d)) upper_le_n incoming) \
      (bendsFrom snapshot
        (.node (.node a (.node b c)) d) upper_le_n incoming)).card ≤ 7 := by
  have first_lt_n : first < n := by
    have ha := a.lower_le_upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have second_lt_n : second < n := by
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have third_lt_n : third < n := by
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have first_le_n : first ≤ n := Nat.le_of_lt first_lt_n
  have second_le_n : second ≤ n := Nat.le_of_lt second_lt_n
  have third_le_n : third ≤ n := Nat.le_of_lt third_lt_n
  let firstKey : Fin n := ⟨first, first_lt_n⟩
  let secondKey : Fin n := ⟨second, second_lt_n⟩
  let thirdKey : Fin n := ⟨third, third_lt_n⟩
  let beforeGrand : AtNode n := {
    lower := lower
    root := third
    upper := upper
    left := .node a (.node b c)
    right := d
    upper_le_n := upper_le_n
  }
  let beforeParent : AtNode n := {
    lower := lower
    root := first
    upper := third
    left := a
    right := .node b c
    upper_le_n := third_le_n
  }
  let beforePromoted : AtNode n := {
    lower := first + 1
    root := second
    upper := third
    left := b
    right := c
    upper_le_n := third_le_n
  }
  let afterPromoted : AtNode n := {
    lower := lower
    root := second
    upper := upper
    left := .node a b
    right := .node c d
    upper_le_n := upper_le_n
  }
  let afterParent : AtNode n := {
    lower := lower
    root := first
    upper := second
    left := a
    right := b
    upper_le_n := second_le_n
  }
  let afterGrand : AtNode n := {
    lower := second + 1
    root := third
    upper := upper
    left := c
    right := d
    upper_le_n := upper_le_n
  }
  let beforeGrandBranch := beforeGrand.heavyBranch snapshot
  let beforeParentBranch := beforeParent.heavyBranch snapshot
  let beforePromotedBranch := beforePromoted.heavyBranch snapshot
  let afterPromotedBranch := afterPromoted.heavyBranch snapshot
  let afterParentBranch := afterParent.heavyBranch snapshot
  let afterGrandBranch := afterGrand.heavyBranch snapshot
  let beforeAtFirst :=
    bendAt firstKey
      (childIncoming beforeGrandBranch .left) beforeParentBranch
  let beforeAtSecond :=
    bendAt secondKey
      (childIncoming beforeParentBranch .right) beforePromotedBranch
  let beforeAtThird :=
    bendAt thirdKey incoming beforeGrandBranch
  let beforeA :=
    bendsFrom snapshot a first_le_n
      (childIncoming beforeParentBranch .left)
  let beforeB :=
    bendsFrom snapshot b second_le_n
      (childIncoming beforePromotedBranch .left)
  let beforeC :=
    bendsFrom snapshot c third_le_n
      (childIncoming beforePromotedBranch .right)
  let beforeD :=
    bendsFrom snapshot d upper_le_n
      (childIncoming beforeGrandBranch .right)
  let afterAtFirst :=
    bendAt firstKey
      (childIncoming afterPromotedBranch .left) afterParentBranch
  let afterAtSecond :=
    bendAt secondKey incoming afterPromotedBranch
  let afterAtThird :=
    bendAt thirdKey
      (childIncoming afterPromotedBranch .right) afterGrandBranch
  let afterA :=
    bendsFrom snapshot a first_le_n
      (childIncoming afterParentBranch .left)
  let afterB :=
    bendsFrom snapshot b second_le_n
      (childIncoming afterParentBranch .right)
  let afterC :=
    bendsFrom snapshot c third_le_n
      (childIncoming afterGrandBranch .left)
  let afterD :=
    bendsFrom snapshot d upper_le_n
      (childIncoming afterGrandBranch .right)
  have beforeDecomposition :
      bendsFrom snapshot
          (.node (.node a (.node b c)) d) upper_le_n incoming =
        unionSeven beforeAtFirst beforeAtSecond beforeAtThird
          beforeA beforeB beforeC beforeD := by
    simp only [bendsFrom]
    simp only [beforeAtFirst, beforeAtSecond, beforeAtThird,
      beforeA, beforeB, beforeC, beforeD,
      beforeGrandBranch, beforeParentBranch, beforePromotedBranch,
      beforeGrand, beforeParent, beforePromoted,
      firstKey, secondKey, thirdKey, unionSeven]
    ac_rfl
  have afterDecomposition :
      bendsFrom snapshot
          (.node (.node a b) (.node c d)) upper_le_n incoming =
        unionSeven afterAtFirst afterAtSecond afterAtThird
          afterA afterB afterC afterD := by
    simp only [bendsFrom]
    simp only [afterAtFirst, afterAtSecond, afterAtThird,
      afterA, afterB, afterC, afterD,
      afterPromotedBranch, afterParentBranch, afterGrandBranch,
      afterPromoted, afterParent, afterGrand,
      firstKey, secondKey, thirdKey, unionSeven]
    ac_rfl
  rw [afterDecomposition, beforeDecomposition]
  apply card_sdiff_unionSeven_le_seven
  · exact
      (card_sdiff_le_card_left _ _).trans
        (bendAt_card_le_one _ _ _)
  · exact
      (card_sdiff_le_card_left _ _).trans
        (bendAt_card_le_one _ _ _)
  · exact
      (card_sdiff_le_card_left _ _).trans
        (bendAt_card_le_one _ _ _)
  · exact bendsFrom_sdiff_le_one snapshot a first_le_n _ _
  · exact bendsFrom_sdiff_le_one snapshot b second_le_n _ _
  · exact bendsFrom_sdiff_le_one snapshot c third_le_n _ _
  · exact bendsFrom_sdiff_le_one snapshot d upper_le_n _ _

/--
The mirror-image right-left zig-zag has the same seven-site creation bound.
-/
theorem zigZagRightLeft_created_le_seven
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    ((bendsFrom snapshot
        (.node (.node a b) (.node c d)) upper_le_n incoming) \
      (bendsFrom snapshot
        (.node a (.node (.node b c) d)) upper_le_n incoming)).card ≤ 7 := by
  have first_lt_n : first < n := by
    have ha := a.lower_le_upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have second_lt_n : second < n := by
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have third_lt_n : third < n := by
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have first_le_n : first ≤ n := Nat.le_of_lt first_lt_n
  have second_le_n : second ≤ n := Nat.le_of_lt second_lt_n
  have third_le_n : third ≤ n := Nat.le_of_lt third_lt_n
  let firstKey : Fin n := ⟨first, first_lt_n⟩
  let secondKey : Fin n := ⟨second, second_lt_n⟩
  let thirdKey : Fin n := ⟨third, third_lt_n⟩
  let beforeGrand : AtNode n := {
    lower := lower
    root := first
    upper := upper
    left := a
    right := .node (.node b c) d
    upper_le_n := upper_le_n
  }
  let beforeParent : AtNode n := {
    lower := first + 1
    root := third
    upper := upper
    left := .node b c
    right := d
    upper_le_n := upper_le_n
  }
  let beforePromoted : AtNode n := {
    lower := first + 1
    root := second
    upper := third
    left := b
    right := c
    upper_le_n := third_le_n
  }
  let afterPromoted : AtNode n := {
    lower := lower
    root := second
    upper := upper
    left := .node a b
    right := .node c d
    upper_le_n := upper_le_n
  }
  let afterParent : AtNode n := {
    lower := lower
    root := first
    upper := second
    left := a
    right := b
    upper_le_n := second_le_n
  }
  let afterGrand : AtNode n := {
    lower := second + 1
    root := third
    upper := upper
    left := c
    right := d
    upper_le_n := upper_le_n
  }
  let beforeGrandBranch := beforeGrand.heavyBranch snapshot
  let beforeParentBranch := beforeParent.heavyBranch snapshot
  let beforePromotedBranch := beforePromoted.heavyBranch snapshot
  let afterPromotedBranch := afterPromoted.heavyBranch snapshot
  let afterParentBranch := afterParent.heavyBranch snapshot
  let afterGrandBranch := afterGrand.heavyBranch snapshot
  let beforeAtFirst :=
    bendAt firstKey incoming beforeGrandBranch
  let beforeAtSecond :=
    bendAt secondKey
      (childIncoming beforeParentBranch .left) beforePromotedBranch
  let beforeAtThird :=
    bendAt thirdKey
      (childIncoming beforeGrandBranch .right) beforeParentBranch
  let beforeA :=
    bendsFrom snapshot a first_le_n
      (childIncoming beforeGrandBranch .left)
  let beforeB :=
    bendsFrom snapshot b second_le_n
      (childIncoming beforePromotedBranch .left)
  let beforeC :=
    bendsFrom snapshot c third_le_n
      (childIncoming beforePromotedBranch .right)
  let beforeD :=
    bendsFrom snapshot d upper_le_n
      (childIncoming beforeParentBranch .right)
  let afterAtFirst :=
    bendAt firstKey
      (childIncoming afterPromotedBranch .left) afterParentBranch
  let afterAtSecond :=
    bendAt secondKey incoming afterPromotedBranch
  let afterAtThird :=
    bendAt thirdKey
      (childIncoming afterPromotedBranch .right) afterGrandBranch
  let afterA :=
    bendsFrom snapshot a first_le_n
      (childIncoming afterParentBranch .left)
  let afterB :=
    bendsFrom snapshot b second_le_n
      (childIncoming afterParentBranch .right)
  let afterC :=
    bendsFrom snapshot c third_le_n
      (childIncoming afterGrandBranch .left)
  let afterD :=
    bendsFrom snapshot d upper_le_n
      (childIncoming afterGrandBranch .right)
  have beforeDecomposition :
      bendsFrom snapshot
          (.node a (.node (.node b c) d)) upper_le_n incoming =
        unionSeven beforeAtFirst beforeAtSecond beforeAtThird
          beforeA beforeB beforeC beforeD := by
    simp only [bendsFrom]
    simp only [beforeAtFirst, beforeAtSecond, beforeAtThird,
      beforeA, beforeB, beforeC, beforeD,
      beforeGrandBranch, beforeParentBranch, beforePromotedBranch,
      beforeGrand, beforeParent, beforePromoted,
      firstKey, secondKey, thirdKey, unionSeven]
    ac_rfl
  have afterDecomposition :
      bendsFrom snapshot
          (.node (.node a b) (.node c d)) upper_le_n incoming =
        unionSeven afterAtFirst afterAtSecond afterAtThird
          afterA afterB afterC afterD := by
    simp only [bendsFrom]
    simp only [afterAtFirst, afterAtSecond, afterAtThird,
      afterA, afterB, afterC, afterD,
      afterPromotedBranch, afterParentBranch, afterGrandBranch,
      afterPromoted, afterParent, afterGrand,
      firstKey, secondKey, thirdKey, unionSeven]
    ac_rfl
  rw [afterDecomposition, beforeDecomposition]
  apply card_sdiff_unionSeven_le_seven
  · exact
      (card_sdiff_le_card_left _ _).trans
        (bendAt_card_le_one _ _ _)
  · exact
      (card_sdiff_le_card_left _ _).trans
        (bendAt_card_le_one _ _ _)
  · exact
      (card_sdiff_le_card_left _ _).trans
        (bendAt_card_le_one _ _ _)
  · exact bendsFrom_sdiff_le_one snapshot a first_le_n _ _
  · exact bendsFrom_sdiff_le_one snapshot b second_le_n _ _
  · exact bendsFrom_sdiff_le_one snapshot c third_le_n _ _
  · exact bendsFrom_sdiff_le_one snapshot d upper_le_n _ _

/--
A genuine zig-zag double rotation under an arbitrary binary-search-tree
context.  This is the zig-zag-only subrelation of `BST.DoubleRotationAt`.
-/
inductive ZigZagAt :
    ℕ → {lower upper : ℕ} → BST lower upper → BST lower upper → Prop
  | leftRight
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      ZigZagAt second
        (.node (.node a (.node b c)) d)
        (.node (.node a b) (.node c d))
  | rightLeft
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      ZigZagAt second
        (.node a (.node (.node b c) d))
        (.node (.node a b) (.node c d))
  | leftContext
      {key lower root upper : ℕ} {before after : BST lower root}
      (step : ZigZagAt key before after)
      (right : BST (root + 1) upper) :
      ZigZagAt key (.node before right) (.node after right)
  | rightContext
      {key lower root upper : ℕ}
      (left : BST lower root)
      {before after : BST (root + 1) upper}
      (step : ZigZagAt key before after) :
      ZigZagAt key (.node left before) (.node left after)

namespace ZigZagAt

/-- `ZigZagAt` forgets to the existing proof-indexed splay-step relation. -/
theorem toDoubleRotationAt
    {key lower upper : ℕ} {before after : BST lower upper}
    (step : ZigZagAt key before after) :
    ∃ depth, BST.DoubleRotationAt depth key before after := by
  induction step with
  | leftRight a b c d =>
      exact
        ⟨0, .root (.zigZagLeftRight a b c d)⟩
  | rightLeft a b c d =>
      exact
        ⟨0, .root (.zigZagRightLeft a b c d)⟩
  | leftContext step right ih =>
      obtain ⟨depth, inner⟩ := ih
      exact ⟨depth.succ, .leftContext inner right⟩
  | rightContext left step ih =>
      obtain ⟨depth, inner⟩ := ih
      exact ⟨depth.succ, .rightContext left inner⟩

/--
The seven-site creation estimate survives every BST context.

Ancestors of the rotated interval select the same heavy branch before and
after: their root and complete inorder interval are unchanged.  Their local
bend contribution and the untouched sibling are therefore common finite-set
components, which cannot increase the number of created identities.
-/
theorem created_le_seven
    {n key lower upper : ℕ} {before after : BST lower upper}
    (step : ZigZagAt key before after)
    (snapshot : Snapshot n) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    ((bendsFrom snapshot after upper_le_n incoming) \
      (bendsFrom snapshot before upper_le_n incoming)).card ≤ 7 := by
  induction step generalizing incoming with
  | leftRight a b c d =>
      exact zigZagLeftRight_created_le_seven
        snapshot a b c d upper_le_n incoming
  | rightLeft a b c d =>
      exact zigZagRightLeft_created_le_seven
        snapshot a b c d upper_le_n incoming
  | @leftContext key lower root upper before after step right ih =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := before
        right := right
        upper_le_n := upper_le_n
      }
      let outgoing := node.heavyBranch snapshot
      have innerBound : root ≤ n := by
        have hRight := right.lower_le_upper
        omega
      have inner :=
        ih innerBound (childIncoming outgoing .left)
      simp only [bendsFrom]
      apply le_trans
        (card_sdiff_same_union_le
          (bendAt ⟨root, by
              have hRight := right.lower_le_upper
              omega⟩ incoming outgoing)
          _ _)
      apply le_trans
        (card_sdiff_union_same_le
          (bendsFrom snapshot after innerBound
            (childIncoming outgoing .left))
          (bendsFrom snapshot before innerBound
            (childIncoming outgoing .left))
          (bendsFrom snapshot right upper_le_n
            (childIncoming outgoing .right)))
      exact inner
  | @rightContext key lower root upper left before after step ih =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := before
        upper_le_n := upper_le_n
      }
      let outgoing := node.heavyBranch snapshot
      have inner :=
        ih upper_le_n (childIncoming outgoing .right)
      simp only [bendsFrom]
      apply le_trans
        (card_sdiff_same_union_le
          (bendAt ⟨root, by
              have hRight := before.lower_le_upper
              omega⟩ incoming outgoing)
          _ _)
      have reordered :
          ((bendsFrom snapshot left (by
                have hRight := before.lower_le_upper
                omega)
              (childIncoming outgoing .left) ∪
              bendsFrom snapshot after upper_le_n
                (childIncoming outgoing .right)) \
            (bendsFrom snapshot left (by
                have hRight := before.lower_le_upper
                omega)
              (childIncoming outgoing .left) ∪
              bendsFrom snapshot before upper_le_n
                (childIncoming outgoing .right))).card ≤
            (bendsFrom snapshot after upper_le_n
                (childIncoming outgoing .right) \
              bendsFrom snapshot before upper_le_n
                (childIncoming outgoing .right)).card :=
        card_sdiff_same_union_le _ _ _
      exact reordered.trans inner

end ZigZagAt

/--
The complete root-local data of a left-right zig-zag.  The dependent tree
indices enforce `first < second < third < n` whenever the configuration
exists.
-/
structure LeftRightZigZagConfiguration (n : ℕ) where
  first : ℕ
  second : ℕ
  third : ℕ
  a : BST 0 first
  b : BST (first + 1) second
  c : BST (second + 1) third
  d : BST (third + 1) n

namespace LeftRightZigZagConfiguration

variable {n : ℕ} (configuration : LeftRightZigZagConfiguration n)

theorem first_lt_second : configuration.first < configuration.second := by
  have := configuration.b.lower_le_upper
  omega

theorem second_lt_third : configuration.second < configuration.third := by
  have := configuration.c.lower_le_upper
  omega

theorem third_lt_n : configuration.third < n := by
  have := configuration.d.lower_le_upper
  omega

theorem first_lt_n : configuration.first < n :=
  lt_trans configuration.first_lt_second
    (lt_trans configuration.second_lt_third configuration.third_lt_n)

theorem second_lt_n : configuration.second < n :=
  lt_trans configuration.second_lt_third configuration.third_lt_n

/-- Tree immediately before the root left-right zig-zag. -/
def before : BST 0 n :=
  .node (.node configuration.a
    (.node configuration.b configuration.c)) configuration.d

/-- Tree immediately after the root left-right zig-zag. -/
def after : BST 0 n :=
  .node (.node configuration.a configuration.b)
    (.node configuration.c configuration.d)

/-- The proof-indexed operational zig-zag represented by the configuration. -/
theorem step :
    BST.DoubleRotation configuration.second
      configuration.before configuration.after :=
  .zigZagLeftRight
    configuration.a configuration.b configuration.c configuration.d

/-- The promoted internal key as an ambient finite key. -/
def promotedKey : Fin n :=
  ⟨configuration.second, configuration.second_lt_n⟩

/-- The lower hit node, which is the bend removed by this zig-zag. -/
def lowerHitKey : Fin n :=
  ⟨configuration.first, configuration.first_lt_n⟩

/-- External value position whose heavy path is being splayed. -/
def promotedPosition : External n :=
  valuePos configuration.promotedKey

/-- Grandparent/root node before the zig-zag. -/
def grandBefore : AtNode n where
  lower := 0
  root := configuration.third
  upper := n
  left := .node configuration.a
    (.node configuration.b configuration.c)
  right := configuration.d
  upper_le_n := Nat.le_refl n

/-- Parent/lower-hit node before the zig-zag. -/
def parentBefore : AtNode n where
  lower := 0
  root := configuration.first
  upper := configuration.third
  left := configuration.a
  right := .node configuration.b configuration.c
  upper_le_n := Nat.le_of_lt configuration.third_lt_n

/-- Promoted node after the zig-zag. -/
def promotedAfter : AtNode n where
  lower := 0
  root := configuration.second
  upper := n
  left := .node configuration.a configuration.b
  right := .node configuration.c configuration.d
  upper_le_n := Nat.le_refl n

/--
The semantic heavy-path hypothesis for this local zig-zag: the minimum-rank
external node of the complete rotated interval is the accessed value.
-/
def OwnerIsPromoted (snapshot : Snapshot n) : Prop :=
  (configuration.grandBefore.owner snapshot) =
    configuration.promotedPosition

/-- A comparison tree serving the promoted key supplies the owner fact. -/
theorem ownerIsPromoted_of_comparisonRoot
    (comparison : BST 0 n)
    (root : comparison.HasRoot configuration.second) :
    configuration.OwnerIsPromoted (Snapshot.ofTree comparison) := by
  have root' :
      comparison.HasRoot configuration.promotedKey.val := by
    simpa [promotedKey] using root
  have global :=
    globalIntervalMin_eq_valuePos_of_hasRoot
      comparison configuration.promotedKey root'
  simpa [OwnerIsPromoted, grandBefore, AtNode.owner,
    AtNode.wholeLower, AtNode.wholeUpper, promotedPosition] using global

/--
A promoted owner forces precisely the three heavy-branch facts used by the
zig-zag bend argument: grandparent-to-parent is heavy left,
parent-to-promoted is heavy right, and after promotion the heavy path ends at
the promoted value.
-/
theorem heavyBranches_of_owner
    (snapshot : Snapshot n)
    (owner : configuration.OwnerIsPromoted snapshot) :
    configuration.grandBefore.heavyBranch snapshot = .left ∧
      configuration.parentBefore.heavyBranch snapshot = .right ∧
      configuration.promotedAfter.heavyBranch snapshot = .middle := by
  have wholeMin :
      IsIntervalMin snapshot.rank
        configuration.grandBefore.wholeLower
        configuration.grandBefore.wholeUpper
        configuration.promotedPosition := by
    rw [← owner]
    exact configuration.grandBefore.owner_isMin snapshot
  have grandHeavy :
      snapshot.IsHeavyBranch
        configuration.grandBefore.wholeLower
        configuration.grandBefore.wholeUpper
        configuration.third .left := by
    refine ⟨configuration.promotedPosition, wholeMin, ?_⟩
    change 2 * configuration.second + 1 ≤ 2 * configuration.third
    have := configuration.second_lt_third
    omega
  have grandBranch :
      configuration.grandBefore.heavyBranch snapshot = .left := by
    exact
      (snapshot.heavyBranch_unique
        configuration.grandBefore.wholeLower
        configuration.grandBefore.wholeUpper
        configuration.grandBefore.whole_nonempty
        configuration.third grandHeavy).symm
  have parentMin :
      IsIntervalMin snapshot.rank
        configuration.parentBefore.wholeLower
        configuration.parentBefore.wholeUpper
        configuration.promotedPosition := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 ≤ 2 * configuration.second + 1
      omega
    · change 2 * configuration.second + 1 ≤ 2 * configuration.third
      have := configuration.second_lt_third
      omega
    · intro node lowerBound upperBound
      apply wholeMin.2.2 node
      · exact lowerBound
      · have upperInside :
            configuration.parentBefore.wholeUpper ≤
              configuration.grandBefore.wholeUpper := by
          change 2 * configuration.third ≤ 2 * n
          have := configuration.third_lt_n
          omega
        exact upperBound.trans upperInside
  have parentHeavy :
      snapshot.IsHeavyBranch
        configuration.parentBefore.wholeLower
        configuration.parentBefore.wholeUpper
        configuration.first .right := by
    refine ⟨configuration.promotedPosition, parentMin, ?_⟩
    change 2 * configuration.first + 2 ≤
      2 * configuration.second + 1
    have := configuration.first_lt_second
    omega
  have parentBranch :
      configuration.parentBefore.heavyBranch snapshot = .right := by
    exact
      (snapshot.heavyBranch_unique
        configuration.parentBefore.wholeLower
        configuration.parentBefore.wholeUpper
        configuration.parentBefore.whole_nonempty
        configuration.first parentHeavy).symm
  have afterMin :
      IsIntervalMin snapshot.rank
        configuration.promotedAfter.wholeLower
        configuration.promotedAfter.wholeUpper
        configuration.promotedPosition := by
    simpa [grandBefore, promotedAfter, AtNode.wholeLower,
      AtNode.wholeUpper] using wholeMin
  have afterHeavy :
      snapshot.IsHeavyBranch
        configuration.promotedAfter.wholeLower
        configuration.promotedAfter.wholeUpper
        configuration.second .middle := by
    refine ⟨configuration.promotedPosition, afterMin, ?_⟩
    rfl
  have afterBranch :
      configuration.promotedAfter.heavyBranch snapshot = .middle := by
    exact
      (snapshot.heavyBranch_unique
        configuration.promotedAfter.wholeLower
        configuration.promotedAfter.wholeUpper
        configuration.promotedAfter.whole_nonempty
        configuration.second afterHeavy).symm
  exact ⟨grandBranch, parentBranch, afterBranch⟩

/-- Genuine bend set immediately before this root zig-zag. -/
noncomputable def beforeBends (snapshot : Snapshot n) : Finset (Fin n) :=
  bends snapshot configuration.before

/-- Genuine bend set immediately after this root zig-zag. -/
noncomputable def afterBends (snapshot : Snapshot n) : Finset (Fin n) :=
  bends snapshot configuration.after

/-- Exact finite-set action induced by the root zig-zag. -/
noncomputable def bendAction (snapshot : Snapshot n) : BendAction :=
  BendAction.between .splay 0 1
    (configuration.beforeBends snapshot)
    (configuration.afterBends snapshot)

/-- The universal seven-site locality estimate specialized to this action. -/
theorem created_le_seven (snapshot : Snapshot n) :
    ((configuration.afterBends snapshot) \
      (configuration.beforeBends snapshot)).card ≤ 7 := by
  simpa [beforeBends, afterBends, bends, before, after] using
    zigZagLeftRight_created_le_seven
      snapshot configuration.a configuration.b configuration.c
        configuration.d (Nat.le_refl n) none

/--
When the accessed value owns the heavy path, the lower hit node is a bend
before the zig-zag and is not a bend afterwards.
-/
theorem lowerHit_mem_removed
    (snapshot : Snapshot n)
    (owner : configuration.OwnerIsPromoted snapshot) :
    configuration.lowerHitKey ∈
      (configuration.beforeBends snapshot) \
        (configuration.afterBends snapshot) := by
  obtain ⟨grandBranch, parentBranch, afterBranch⟩ :=
    configuration.heavyBranches_of_owner snapshot owner
  have grandBranch' :
      (({
        lower := 0
        root := configuration.third
        upper := n
        left := .node configuration.a
          (.node configuration.b configuration.c)
        right := configuration.d
        upper_le_n := Nat.le_refl n
      } : AtNode n).heavyBranch snapshot) = .left := by
    simpa [grandBefore] using grandBranch
  have parentBranch' :
      (({
        lower := 0
        root := configuration.first
        upper := configuration.third
        left := configuration.a
        right := .node configuration.b configuration.c
        upper_le_n := Nat.le_of_lt configuration.third_lt_n
      } : AtNode n).heavyBranch snapshot) = .right := by
    simpa [parentBefore] using parentBranch
  have beforeMember :
      configuration.lowerHitKey ∈
        configuration.beforeBends snapshot := by
    simp [beforeBends, bends, before, bendsFrom,
      grandBranch', parentBranch',
      childIncoming, bendAt, Turns, lowerHitKey]
  have afterNotMember :
      configuration.lowerHitKey ∉
        configuration.afterBends snapshot := by
    intro member
    have afterBranch' :
        (({
          lower := 0
          root := configuration.second
          upper := n
          left := .node configuration.a configuration.b
          right := .node configuration.c configuration.d
          upper_le_n := Nat.le_refl n
        } : AtNode n).heavyBranch snapshot) = .middle := by
      simpa [promotedAfter] using afterBranch
    simp [afterBends, bends, after, bendsFrom,
      afterBranch', childIncoming, bendAt, Turns] at member
    rcases member with inA | inB | inC | inD
    · have bounds :=
        mem_bendsFrom_bounds snapshot configuration.a
          (Nat.le_of_lt configuration.first_lt_n) _ inA
      exact (Nat.lt_irrefl configuration.first) bounds.2
    · have bounds :=
        mem_bendsFrom_bounds snapshot configuration.b
          (Nat.le_of_lt configuration.second_lt_n) _ inB
      have lower := bounds.1
      change configuration.first + 1 ≤ configuration.first at lower
      omega
    · have bounds :=
        mem_bendsFrom_bounds snapshot configuration.c
          (Nat.le_of_lt configuration.third_lt_n) _ inC
      have lower := bounds.1
      change configuration.second + 1 ≤ configuration.first at lower
      have order := configuration.first_lt_second
      omega
    · have bounds :=
        mem_bendsFrom_bounds snapshot configuration.d
          (Nat.le_refl n) _ inD
      have lower := bounds.1
      change configuration.third + 1 ≤ configuration.first at lower
      have order₁ := configuration.first_lt_second
      have order₂ := configuration.second_lt_third
      omega
  exact Finset.mem_sdiff.mpr ⟨beforeMember, afterNotMember⟩

/-- Every genuine root left-right zig-zag removes at least one old bend. -/
theorem one_le_removed
    (snapshot : Snapshot n)
    (owner : configuration.OwnerIsPromoted snapshot) :
    1 ≤ ((configuration.beforeBends snapshot) \
      (configuration.afterBends snapshot)).card := by
  exact Finset.one_le_card.mpr
    ⟨configuration.lowerHitKey,
      configuration.lowerHit_mem_removed snapshot owner⟩

/--
The action is exactly one locally sound zig-zag once the uniform splay
allowance is at least seven.
-/
theorem bendAction_locallySound
    (snapshot : Snapshot n) (constants : BendConstants)
    (splayAllowance : 7 ≤ constants.splay)
    (owner : configuration.OwnerIsPromoted snapshot) :
    (configuration.bendAction snapshot).LocallySound constants := by
  constructor
  · simpa [bendAction, BendAction.between] using
      configuration.one_le_removed snapshot owner
  · have created := configuration.created_le_seven snapshot
    simpa [bendAction, BendAction.between] using
      created.trans splayAllowance

/--
Operational form: a comparison state that serves the promoted key at its
root discharges the owner premise automatically.
-/
theorem bendAction_locallySound_of_comparisonRoot
    (comparison : BST 0 n) (constants : BendConstants)
    (splayAllowance : 7 ≤ constants.splay)
    (root : comparison.HasRoot configuration.second) :
    (configuration.bendAction
      (Snapshot.ofTree comparison)).LocallySound constants :=
  configuration.bendAction_locallySound
    (Snapshot.ofTree comparison) constants splayAllowance
    (configuration.ownerIsPromoted_of_comparisonRoot comparison root)

/-- The exact singleton finite-bend history of this local action. -/
theorem bendAction_history (snapshot : Snapshot n) :
    FiniteBendHistory n
      (configuration.beforeBends snapshot)
      [configuration.bendAction snapshot]
      (configuration.afterBends snapshot) := by
  simpa [bendAction] using
    (FiniteBendHistory.cons
      (n := n) (before := configuration.beforeBends snapshot)
      .splay 0 1
      (FiniteBendHistory.nil
        (configuration.afterBends snapshot)))

/--
Packaged local finite-bend witness for a left-right zig-zag served by a
comparison-tree root.
-/
noncomputable def finiteBendStep_of_comparisonRoot
    (comparison : BST 0 n) (constants : BendConstants)
    (splayAllowance : 7 ≤ constants.splay)
    (root : comparison.HasRoot configuration.second) :
    LocalFiniteBendStep constants n where
  beforeBends :=
    configuration.beforeBends (Snapshot.ofTree comparison)
  afterBends :=
    configuration.afterBends (Snapshot.ofTree comparison)
  action :=
    configuration.bendAction (Snapshot.ofTree comparison)
  history :=
    configuration.bendAction_history (Snapshot.ofTree comparison)
  locallySound :=
    configuration.bendAction_locallySound_of_comparisonRoot
      comparison constants splayAllowance root

end LeftRightZigZagConfiguration

/-- Root-local data for the mirror-image right-left zig-zag. -/
structure RightLeftZigZagConfiguration (n : ℕ) where
  first : ℕ
  second : ℕ
  third : ℕ
  a : BST 0 first
  b : BST (first + 1) second
  c : BST (second + 1) third
  d : BST (third + 1) n

namespace RightLeftZigZagConfiguration

variable {n : ℕ} (configuration : RightLeftZigZagConfiguration n)

theorem first_lt_second : configuration.first < configuration.second := by
  have := configuration.b.lower_le_upper
  omega

theorem second_lt_third : configuration.second < configuration.third := by
  have := configuration.c.lower_le_upper
  omega

theorem third_lt_n : configuration.third < n := by
  have := configuration.d.lower_le_upper
  omega

theorem first_lt_n : configuration.first < n :=
  lt_trans configuration.first_lt_second
    (lt_trans configuration.second_lt_third configuration.third_lt_n)

theorem second_lt_n : configuration.second < n :=
  lt_trans configuration.second_lt_third configuration.third_lt_n

/-- Tree immediately before the root right-left zig-zag. -/
def before : BST 0 n :=
  .node configuration.a
    (.node (.node configuration.b configuration.c) configuration.d)

/-- Tree immediately after the root right-left zig-zag. -/
def after : BST 0 n :=
  .node (.node configuration.a configuration.b)
    (.node configuration.c configuration.d)

/-- The corresponding proof-indexed operational double rotation. -/
theorem step :
    BST.DoubleRotation configuration.second
      configuration.before configuration.after :=
  .zigZagRightLeft
    configuration.a configuration.b configuration.c configuration.d

def promotedKey : Fin n :=
  ⟨configuration.second, configuration.second_lt_n⟩

def lowerHitKey : Fin n :=
  ⟨configuration.third, configuration.third_lt_n⟩

def promotedPosition : External n :=
  valuePos configuration.promotedKey

def grandBefore : AtNode n where
  lower := 0
  root := configuration.first
  upper := n
  left := configuration.a
  right := .node (.node configuration.b configuration.c)
    configuration.d
  upper_le_n := Nat.le_refl n

def parentBefore : AtNode n where
  lower := configuration.first + 1
  root := configuration.third
  upper := n
  left := .node configuration.b configuration.c
  right := configuration.d
  upper_le_n := Nat.le_refl n

def promotedAfter : AtNode n where
  lower := 0
  root := configuration.second
  upper := n
  left := .node configuration.a configuration.b
  right := .node configuration.c configuration.d
  upper_le_n := Nat.le_refl n

def OwnerIsPromoted (snapshot : Snapshot n) : Prop :=
  (configuration.grandBefore.owner snapshot) =
    configuration.promotedPosition

/-- A serving comparison-tree state also supplies the mirror owner fact. -/
theorem ownerIsPromoted_of_comparisonRoot
    (comparison : BST 0 n)
    (root : comparison.HasRoot configuration.second) :
    configuration.OwnerIsPromoted (Snapshot.ofTree comparison) := by
  have root' :
      comparison.HasRoot configuration.promotedKey.val := by
    simpa [promotedKey] using root
  have global :=
    globalIntervalMin_eq_valuePos_of_hasRoot
      comparison configuration.promotedKey root'
  simpa [OwnerIsPromoted, grandBefore, AtNode.owner,
    AtNode.wholeLower, AtNode.wholeUpper, promotedPosition] using global

/-- Mirror-image heavy-branch consequences of an accessed owner. -/
theorem heavyBranches_of_owner
    (snapshot : Snapshot n)
    (owner : configuration.OwnerIsPromoted snapshot) :
    configuration.grandBefore.heavyBranch snapshot = .right ∧
      configuration.parentBefore.heavyBranch snapshot = .left ∧
      configuration.promotedAfter.heavyBranch snapshot = .middle := by
  have wholeMin :
      IsIntervalMin snapshot.rank
        configuration.grandBefore.wholeLower
        configuration.grandBefore.wholeUpper
        configuration.promotedPosition := by
    rw [← owner]
    exact configuration.grandBefore.owner_isMin snapshot
  have grandHeavy :
      snapshot.IsHeavyBranch
        configuration.grandBefore.wholeLower
        configuration.grandBefore.wholeUpper
        configuration.first .right := by
    refine ⟨configuration.promotedPosition, wholeMin, ?_⟩
    change 2 * configuration.first + 2 ≤
      2 * configuration.second + 1
    have := configuration.first_lt_second
    omega
  have grandBranch :
      configuration.grandBefore.heavyBranch snapshot = .right := by
    exact
      (snapshot.heavyBranch_unique
        configuration.grandBefore.wholeLower
        configuration.grandBefore.wholeUpper
        configuration.grandBefore.whole_nonempty
        configuration.first grandHeavy).symm
  have parentMin :
      IsIntervalMin snapshot.rank
        configuration.parentBefore.wholeLower
        configuration.parentBefore.wholeUpper
        configuration.promotedPosition := by
    refine ⟨?_, ?_, ?_⟩
    · change 2 * (configuration.first + 1) ≤
        2 * configuration.second + 1
      have := configuration.first_lt_second
      omega
    · change 2 * configuration.second + 1 ≤ 2 * n
      have := configuration.second_lt_n
      omega
    · intro node lowerBound upperBound
      apply wholeMin.2.2 node
      · have lowerInside :
            configuration.grandBefore.wholeLower ≤
              configuration.parentBefore.wholeLower := by
          change 0 ≤ 2 * (configuration.first + 1)
          omega
        exact lowerInside.trans lowerBound
      · exact upperBound
  have parentHeavy :
      snapshot.IsHeavyBranch
        configuration.parentBefore.wholeLower
        configuration.parentBefore.wholeUpper
        configuration.third .left := by
    refine ⟨configuration.promotedPosition, parentMin, ?_⟩
    change 2 * configuration.second + 1 ≤ 2 * configuration.third
    have := configuration.second_lt_third
    omega
  have parentBranch :
      configuration.parentBefore.heavyBranch snapshot = .left := by
    exact
      (snapshot.heavyBranch_unique
        configuration.parentBefore.wholeLower
        configuration.parentBefore.wholeUpper
        configuration.parentBefore.whole_nonempty
        configuration.third parentHeavy).symm
  have afterMin :
      IsIntervalMin snapshot.rank
        configuration.promotedAfter.wholeLower
        configuration.promotedAfter.wholeUpper
        configuration.promotedPosition := by
    simpa [grandBefore, promotedAfter, AtNode.wholeLower,
      AtNode.wholeUpper] using wholeMin
  have afterHeavy :
      snapshot.IsHeavyBranch
        configuration.promotedAfter.wholeLower
        configuration.promotedAfter.wholeUpper
        configuration.second .middle := by
    refine ⟨configuration.promotedPosition, afterMin, ?_⟩
    rfl
  have afterBranch :
      configuration.promotedAfter.heavyBranch snapshot = .middle := by
    exact
      (snapshot.heavyBranch_unique
        configuration.promotedAfter.wholeLower
        configuration.promotedAfter.wholeUpper
        configuration.promotedAfter.whole_nonempty
        configuration.second afterHeavy).symm
  exact ⟨grandBranch, parentBranch, afterBranch⟩

noncomputable def beforeBends (snapshot : Snapshot n) : Finset (Fin n) :=
  bends snapshot configuration.before

noncomputable def afterBends (snapshot : Snapshot n) : Finset (Fin n) :=
  bends snapshot configuration.after

noncomputable def bendAction (snapshot : Snapshot n) : BendAction :=
  BendAction.between .splay 0 1
    (configuration.beforeBends snapshot)
    (configuration.afterBends snapshot)

theorem created_le_seven (snapshot : Snapshot n) :
    ((configuration.afterBends snapshot) \
      (configuration.beforeBends snapshot)).card ≤ 7 := by
  simpa [beforeBends, afterBends, bends, before, after] using
    zigZagRightLeft_created_le_seven
      snapshot configuration.a configuration.b configuration.c
        configuration.d (Nat.le_refl n) none

/-- The lower hit node is genuinely removed in the mirror orientation. -/
theorem lowerHit_mem_removed
    (snapshot : Snapshot n)
    (owner : configuration.OwnerIsPromoted snapshot) :
    configuration.lowerHitKey ∈
      (configuration.beforeBends snapshot) \
        (configuration.afterBends snapshot) := by
  obtain ⟨grandBranch, parentBranch, afterBranch⟩ :=
    configuration.heavyBranches_of_owner snapshot owner
  have grandBranch' :
      (({
        lower := 0
        root := configuration.first
        upper := n
        left := configuration.a
        right := .node (.node configuration.b configuration.c)
          configuration.d
        upper_le_n := Nat.le_refl n
      } : AtNode n).heavyBranch snapshot) = .right := by
    simpa [grandBefore] using grandBranch
  have parentBranch' :
      (({
        lower := configuration.first + 1
        root := configuration.third
        upper := n
        left := .node configuration.b configuration.c
        right := configuration.d
        upper_le_n := Nat.le_refl n
      } : AtNode n).heavyBranch snapshot) = .left := by
    simpa [parentBefore] using parentBranch
  have beforeMember :
      configuration.lowerHitKey ∈
        configuration.beforeBends snapshot := by
    simp [beforeBends, bends, before, bendsFrom,
      grandBranch', parentBranch',
      childIncoming, bendAt, Turns, lowerHitKey]
  have afterNotMember :
      configuration.lowerHitKey ∉
        configuration.afterBends snapshot := by
    intro member
    have afterBranch' :
        (({
          lower := 0
          root := configuration.second
          upper := n
          left := .node configuration.a configuration.b
          right := .node configuration.c configuration.d
          upper_le_n := Nat.le_refl n
        } : AtNode n).heavyBranch snapshot) = .middle := by
      simpa [promotedAfter] using afterBranch
    simp [afterBends, bends, after, bendsFrom,
      afterBranch', childIncoming, bendAt, Turns] at member
    rcases member with inA | inB | inC | inD
    · have bounds :=
        mem_bendsFrom_bounds snapshot configuration.a
          (Nat.le_of_lt configuration.first_lt_n) _ inA
      have upper := bounds.2
      change configuration.third < configuration.first at upper
      have order₁ := configuration.first_lt_second
      have order₂ := configuration.second_lt_third
      omega
    · have bounds :=
        mem_bendsFrom_bounds snapshot configuration.b
          (Nat.le_of_lt configuration.second_lt_n) _ inB
      have upper := bounds.2
      change configuration.third < configuration.second at upper
      have order := configuration.second_lt_third
      omega
    · have bounds :=
        mem_bendsFrom_bounds snapshot configuration.c
          (Nat.le_of_lt configuration.third_lt_n) _ inC
      exact (Nat.lt_irrefl configuration.third) bounds.2
    · have bounds :=
        mem_bendsFrom_bounds snapshot configuration.d
          (Nat.le_refl n) _ inD
      have lower := bounds.1
      change configuration.third + 1 ≤ configuration.third at lower
      omega
  exact Finset.mem_sdiff.mpr ⟨beforeMember, afterNotMember⟩

theorem one_le_removed
    (snapshot : Snapshot n)
    (owner : configuration.OwnerIsPromoted snapshot) :
    1 ≤ ((configuration.beforeBends snapshot) \
      (configuration.afterBends snapshot)).card := by
  exact Finset.one_le_card.mpr
    ⟨configuration.lowerHitKey,
      configuration.lowerHit_mem_removed snapshot owner⟩

theorem bendAction_locallySound
    (snapshot : Snapshot n) (constants : BendConstants)
    (splayAllowance : 7 ≤ constants.splay)
    (owner : configuration.OwnerIsPromoted snapshot) :
    (configuration.bendAction snapshot).LocallySound constants := by
  constructor
  · simpa [bendAction, BendAction.between] using
      configuration.one_le_removed snapshot owner
  · have created := configuration.created_le_seven snapshot
    simpa [bendAction, BendAction.between] using
      created.trans splayAllowance

theorem bendAction_locallySound_of_comparisonRoot
    (comparison : BST 0 n) (constants : BendConstants)
    (splayAllowance : 7 ≤ constants.splay)
    (root : comparison.HasRoot configuration.second) :
    (configuration.bendAction
      (Snapshot.ofTree comparison)).LocallySound constants :=
  configuration.bendAction_locallySound
    (Snapshot.ofTree comparison) constants splayAllowance
    (configuration.ownerIsPromoted_of_comparisonRoot comparison root)

theorem bendAction_history (snapshot : Snapshot n) :
    FiniteBendHistory n
      (configuration.beforeBends snapshot)
      [configuration.bendAction snapshot]
      (configuration.afterBends snapshot) := by
  simpa [bendAction] using
    (FiniteBendHistory.cons
      (n := n) (before := configuration.beforeBends snapshot)
      .splay 0 1
      (FiniteBendHistory.nil
        (configuration.afterBends snapshot)))

/-- Packaged local witness for the mirror right-left zig-zag. -/
noncomputable def finiteBendStep_of_comparisonRoot
    (comparison : BST 0 n) (constants : BendConstants)
    (splayAllowance : 7 ≤ constants.splay)
    (root : comparison.HasRoot configuration.second) :
    LocalFiniteBendStep constants n where
  beforeBends :=
    configuration.beforeBends (Snapshot.ofTree comparison)
  afterBends :=
    configuration.afterBends (Snapshot.ofTree comparison)
  action :=
    configuration.bendAction (Snapshot.ofTree comparison)
  history :=
    configuration.bendAction_history (Snapshot.ofTree comparison)
  locallySound :=
    configuration.bendAction_locallySound_of_comparisonRoot
      comparison constants splayAllowance root

end RightLeftZigZagConfiguration

end Splay.Accounting.LocalBendGeometry
