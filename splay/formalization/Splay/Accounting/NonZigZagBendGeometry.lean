import Splay.Accounting.LocalBendGeometry
import Splay.Accounting.ConcreteSplayCost

namespace Splay.Accounting.NonZigZagBendGeometry

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry

private def unionFive {α : Type*} [DecidableEq α]
    (first second third fourth fifth : Finset α) : Finset α :=
  first ∪ (second ∪ (third ∪ (fourth ∪ fifth)))

/--
If five corresponding local components each create at most one identity,
their unions create at most five identities.
-/
private theorem card_sdiff_unionFive_le_five
    {α : Type*} [DecidableEq α]
    (after₁ after₂ after₃ after₄ after₅ :
      Finset α)
    (before₁ before₂ before₃ before₄ before₅ :
      Finset α)
    (h₁ : (after₁ \ before₁).card ≤ 1)
    (h₂ : (after₂ \ before₂).card ≤ 1)
    (h₃ : (after₃ \ before₃).card ≤ 1)
    (h₄ : (after₄ \ before₄).card ≤ 1)
    (h₅ : (after₅ \ before₅).card ≤ 1) :
    ((unionFive after₁ after₂ after₃ after₄ after₅) \
      (unionFive before₁ before₂ before₃ before₄ before₅)).card ≤ 5 := by
  have bound₄ :=
    card_sdiff_union_le_add after₄ after₅ before₄ before₅
  have bound₃ :=
    card_sdiff_union_le_add after₃ (after₄ ∪ after₅)
      before₃ (before₄ ∪ before₅)
  have bound₂ :=
    card_sdiff_union_le_add after₂
      (after₃ ∪ (after₄ ∪ after₅))
      before₂ (before₃ ∪ (before₄ ∪ before₅))
  have bound₁ :=
    card_sdiff_union_le_add after₁
      (after₂ ∪ (after₃ ∪ (after₄ ∪ after₅)))
      before₁ (before₂ ∪ (before₃ ∪ (before₄ ∪ before₅)))
  unfold unionFive
  omega

private def unionSeven {α : Type*} [DecidableEq α]
    (first second third fourth fifth sixth seventh : Finset α) :
    Finset α :=
  first ∪ (second ∪ (third ∪
    (fourth ∪ (fifth ∪ (sixth ∪ seventh)))))

/--
If seven corresponding local components each create at most one identity,
their unions create at most seven identities.
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
  have bound₆ :=
    card_sdiff_union_le_add after₆ after₇ before₆ before₇
  have bound₅ :=
    card_sdiff_union_le_add after₅ (after₆ ∪ after₇)
      before₅ (before₆ ∪ before₇)
  have bound₄ :=
    card_sdiff_union_le_add after₄
      (after₅ ∪ (after₆ ∪ after₇))
      before₄ (before₅ ∪ (before₆ ∪ before₇))
  have bound₃ :=
    card_sdiff_union_le_add after₃
      (after₄ ∪ (after₅ ∪ (after₆ ∪ after₇)))
      before₃ (before₄ ∪ (before₅ ∪ (before₆ ∪ before₇)))
  have bound₂ :=
    card_sdiff_union_le_add after₂
      (after₃ ∪ (after₄ ∪ (after₅ ∪ (after₆ ∪ after₇))))
      before₂
      (before₃ ∪ (before₄ ∪ (before₅ ∪ (before₆ ∪ before₇))))
  have bound₁ :=
    card_sdiff_union_le_add after₁
      (after₂ ∪
        (after₃ ∪ (after₄ ∪ (after₅ ∪ (after₆ ∪ after₇)))))
      before₁
      (before₂ ∪
        (before₃ ∪ (before₄ ∪ (before₅ ∪ (before₆ ∪ before₇)))))
  unfold unionSeven
  omega

namespace Zig

/--
A root zig changes bend status only at its two rotation keys and at the
roots of its three hanging subtrees.
-/
theorem created_le_five
    {n key lower upper : ℕ} {before after : BST lower upper}
    (step : Splay.Tree.BST.Zig key before after)
    (snapshot : Snapshot n) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    ((bendsFrom snapshot after upper_le_n incoming) \
      (bendsFrom snapshot before upper_le_n incoming)).card ≤ 5 := by
  cases step with
  | @fromLeft lower promoted demoted upper a b c =>
      have promoted_lt_n : key < n := by
        have hb := b.lower_le_upper
        have hc := c.lower_le_upper
        omega
      have demoted_lt_n : demoted < n := by
        have hc := c.lower_le_upper
        omega
      have promoted_le_n : key ≤ n :=
        Nat.le_of_lt promoted_lt_n
      have demoted_le_n : demoted ≤ n :=
        Nat.le_of_lt demoted_lt_n
      let promotedKey : Fin n := ⟨key, promoted_lt_n⟩
      let demotedKey : Fin n := ⟨demoted, demoted_lt_n⟩
      let beforePromoted : AtNode n := {
        lower := lower
        root := key
        upper := demoted
        left := a
        right := b
        upper_le_n := demoted_le_n
      }
      let beforeDemoted : AtNode n := {
        lower := lower
        root := demoted
        upper := upper
        left := .node a b
        right := c
        upper_le_n := upper_le_n
      }
      let afterPromoted : AtNode n := {
        lower := lower
        root := key
        upper := upper
        left := a
        right := .node b c
        upper_le_n := upper_le_n
      }
      let afterDemoted : AtNode n := {
        lower := key + 1
        root := demoted
        upper := upper
        left := b
        right := c
        upper_le_n := upper_le_n
      }
      let beforePromotedBranch := beforePromoted.heavyBranch snapshot
      let beforeDemotedBranch := beforeDemoted.heavyBranch snapshot
      let afterPromotedBranch := afterPromoted.heavyBranch snapshot
      let afterDemotedBranch := afterDemoted.heavyBranch snapshot
      let beforeAtPromoted :=
        bendAt promotedKey
          (childIncoming beforeDemotedBranch .left)
          beforePromotedBranch
      let beforeAtDemoted :=
        bendAt demotedKey incoming beforeDemotedBranch
      let beforeA :=
        bendsFrom snapshot a promoted_le_n
          (childIncoming beforePromotedBranch .left)
      let beforeB :=
        bendsFrom snapshot b demoted_le_n
          (childIncoming beforePromotedBranch .right)
      let beforeC :=
        bendsFrom snapshot c upper_le_n
          (childIncoming beforeDemotedBranch .right)
      let afterAtPromoted :=
        bendAt promotedKey incoming afterPromotedBranch
      let afterAtDemoted :=
        bendAt demotedKey
          (childIncoming afterPromotedBranch .right)
          afterDemotedBranch
      let afterA :=
        bendsFrom snapshot a promoted_le_n
          (childIncoming afterPromotedBranch .left)
      let afterB :=
        bendsFrom snapshot b demoted_le_n
          (childIncoming afterDemotedBranch .left)
      let afterC :=
        bendsFrom snapshot c upper_le_n
          (childIncoming afterDemotedBranch .right)
      have beforeDecomposition :
          bendsFrom snapshot
              (.node (.node a b) c) upper_le_n incoming =
            unionFive beforeAtPromoted beforeAtDemoted
              beforeA beforeB beforeC := by
        simp only [bendsFrom]
        simp only [beforeAtPromoted, beforeAtDemoted,
          beforeA, beforeB, beforeC,
          beforePromotedBranch, beforeDemotedBranch,
          beforePromoted, beforeDemoted,
          promotedKey, demotedKey, unionFive]
        ac_rfl
      have afterDecomposition :
          bendsFrom snapshot
              (.node a (.node b c)) upper_le_n incoming =
            unionFive afterAtPromoted afterAtDemoted
              afterA afterB afterC := by
        simp only [bendsFrom]
        simp only [afterAtPromoted, afterAtDemoted,
          afterA, afterB, afterC,
          afterPromotedBranch, afterDemotedBranch,
          afterPromoted, afterDemoted,
          promotedKey, demotedKey, unionFive]
        ac_rfl
      rw [afterDecomposition, beforeDecomposition]
      apply card_sdiff_unionFive_le_five
      · exact
          (card_sdiff_le_card_left _ _).trans
            (bendAt_card_le_one _ _ _)
      · exact
          (card_sdiff_le_card_left _ _).trans
            (bendAt_card_le_one _ _ _)
      · exact bendsFrom_sdiff_le_one snapshot a promoted_le_n _ _
      · exact bendsFrom_sdiff_le_one snapshot b demoted_le_n _ _
      · exact bendsFrom_sdiff_le_one snapshot c upper_le_n _ _
  | @fromRight lower demoted promoted upper a b c =>
      have demoted_lt_n : demoted < n := by
        have hb := b.lower_le_upper
        have hc := c.lower_le_upper
        omega
      have promoted_lt_n : key < n := by
        have hc := c.lower_le_upper
        omega
      have demoted_le_n : demoted ≤ n :=
        Nat.le_of_lt demoted_lt_n
      have promoted_le_n : key ≤ n :=
        Nat.le_of_lt promoted_lt_n
      let demotedKey : Fin n := ⟨demoted, demoted_lt_n⟩
      let promotedKey : Fin n := ⟨key, promoted_lt_n⟩
      let beforeDemoted : AtNode n := {
        lower := lower
        root := demoted
        upper := upper
        left := a
        right := .node b c
        upper_le_n := upper_le_n
      }
      let beforePromoted : AtNode n := {
        lower := demoted + 1
        root := key
        upper := upper
        left := b
        right := c
        upper_le_n := upper_le_n
      }
      let afterDemoted : AtNode n := {
        lower := lower
        root := demoted
        upper := key
        left := a
        right := b
        upper_le_n := promoted_le_n
      }
      let afterPromoted : AtNode n := {
        lower := lower
        root := key
        upper := upper
        left := .node a b
        right := c
        upper_le_n := upper_le_n
      }
      let beforeDemotedBranch := beforeDemoted.heavyBranch snapshot
      let beforePromotedBranch := beforePromoted.heavyBranch snapshot
      let afterDemotedBranch := afterDemoted.heavyBranch snapshot
      let afterPromotedBranch := afterPromoted.heavyBranch snapshot
      let beforeAtDemoted :=
        bendAt demotedKey incoming beforeDemotedBranch
      let beforeAtPromoted :=
        bendAt promotedKey
          (childIncoming beforeDemotedBranch .right)
          beforePromotedBranch
      let beforeA :=
        bendsFrom snapshot a demoted_le_n
          (childIncoming beforeDemotedBranch .left)
      let beforeB :=
        bendsFrom snapshot b promoted_le_n
          (childIncoming beforePromotedBranch .left)
      let beforeC :=
        bendsFrom snapshot c upper_le_n
          (childIncoming beforePromotedBranch .right)
      let afterAtDemoted :=
        bendAt demotedKey
          (childIncoming afterPromotedBranch .left)
          afterDemotedBranch
      let afterAtPromoted :=
        bendAt promotedKey incoming afterPromotedBranch
      let afterA :=
        bendsFrom snapshot a demoted_le_n
          (childIncoming afterDemotedBranch .left)
      let afterB :=
        bendsFrom snapshot b promoted_le_n
          (childIncoming afterDemotedBranch .right)
      let afterC :=
        bendsFrom snapshot c upper_le_n
          (childIncoming afterPromotedBranch .right)
      have beforeDecomposition :
          bendsFrom snapshot
              (.node a (.node b c)) upper_le_n incoming =
            unionFive beforeAtDemoted beforeAtPromoted
              beforeA beforeB beforeC := by
        simp only [bendsFrom]
        simp only [beforeAtDemoted, beforeAtPromoted,
          beforeA, beforeB, beforeC,
          beforeDemotedBranch, beforePromotedBranch,
          beforeDemoted, beforePromoted,
          demotedKey, promotedKey, unionFive]
        ac_rfl
      have afterDecomposition :
          bendsFrom snapshot
              (.node (.node a b) c) upper_le_n incoming =
            unionFive afterAtDemoted afterAtPromoted
              afterA afterB afterC := by
        simp only [bendsFrom]
        simp only [afterAtDemoted, afterAtPromoted,
          afterA, afterB, afterC,
          afterDemotedBranch, afterPromotedBranch,
          afterDemoted, afterPromoted,
          demotedKey, promotedKey, unionFive]
        ac_rfl
      rw [afterDecomposition, beforeDecomposition]
      apply card_sdiff_unionFive_le_five
      · exact
          (card_sdiff_le_card_left _ _).trans
            (bendAt_card_le_one _ _ _)
      · exact
          (card_sdiff_le_card_left _ _).trans
            (bendAt_card_le_one _ _ _)
      · exact bendsFrom_sdiff_le_one snapshot a demoted_le_n _ _
      · exact bendsFrom_sdiff_le_one snapshot b promoted_le_n _ _
      · exact bendsFrom_sdiff_le_one snapshot c upper_le_n _ _

/-- The weaker seven-site form used by the transcript accounting API. -/
theorem created_le_seven
    {n key lower upper : ℕ} {before after : BST lower upper}
    (step : Splay.Tree.BST.Zig key before after)
    (snapshot : Snapshot n) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    ((bendsFrom snapshot after upper_le_n incoming) \
      (bendsFrom snapshot before upper_le_n incoming)).card ≤ 7 :=
  (created_le_five step snapshot upper_le_n incoming).trans (by omega)

/-- A whole-tree zig creates at most seven bends. -/
theorem bends_created_le_seven
    {n key : ℕ} {before after : BST 0 n}
    (step : Splay.Tree.BST.Zig key before after)
    (snapshot : Snapshot n) :
    ((bends snapshot after) \ (bends snapshot before)).card ≤ 7 := by
  simpa [bends] using
    created_le_seven step snapshot (Nat.le_refl n) none

end Zig

/--
The two same-direction root double rotations have the same seven local
components: three rotation keys and the roots of four hanging subtrees.
The statement is symmetric so that one decomposition proves both
zig-zig orientations.
-/
private theorem zigZig_created_le_seven_both
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    (((bendsFrom snapshot
        (.node a (.node b (.node c d))) upper_le_n incoming) \
      (bendsFrom snapshot
        (.node (.node (.node a b) c) d) upper_le_n incoming)).card ≤ 7) ∧
    (((bendsFrom snapshot
        (.node (.node (.node a b) c) d) upper_le_n incoming) \
      (bendsFrom snapshot
        (.node a (.node b (.node c d))) upper_le_n incoming)).card ≤ 7) := by
  have first_lt_n : first < n := by
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have second_lt_n : second < n := by
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    omega
  have third_lt_n : third < n := by
    have hd := d.lower_le_upper
    omega
  have first_le_n : first ≤ n := Nat.le_of_lt first_lt_n
  have second_le_n : second ≤ n := Nat.le_of_lt second_lt_n
  have third_le_n : third ≤ n := Nat.le_of_lt third_lt_n
  let firstKey : Fin n := ⟨first, first_lt_n⟩
  let secondKey : Fin n := ⟨second, second_lt_n⟩
  let thirdKey : Fin n := ⟨third, third_lt_n⟩
  let leftFirst : AtNode n := {
    lower := lower
    root := first
    upper := second
    left := a
    right := b
    upper_le_n := second_le_n
  }
  let leftSecond : AtNode n := {
    lower := lower
    root := second
    upper := third
    left := .node a b
    right := c
    upper_le_n := third_le_n
  }
  let leftThird : AtNode n := {
    lower := lower
    root := third
    upper := upper
    left := .node (.node a b) c
    right := d
    upper_le_n := upper_le_n
  }
  let rightFirst : AtNode n := {
    lower := lower
    root := first
    upper := upper
    left := a
    right := .node b (.node c d)
    upper_le_n := upper_le_n
  }
  let rightSecond : AtNode n := {
    lower := first + 1
    root := second
    upper := upper
    left := b
    right := .node c d
    upper_le_n := upper_le_n
  }
  let rightThird : AtNode n := {
    lower := second + 1
    root := third
    upper := upper
    left := c
    right := d
    upper_le_n := upper_le_n
  }
  let leftFirstBranch := leftFirst.heavyBranch snapshot
  let leftSecondBranch := leftSecond.heavyBranch snapshot
  let leftThirdBranch := leftThird.heavyBranch snapshot
  let rightFirstBranch := rightFirst.heavyBranch snapshot
  let rightSecondBranch := rightSecond.heavyBranch snapshot
  let rightThirdBranch := rightThird.heavyBranch snapshot
  let leftAtFirst :=
    bendAt firstKey
      (childIncoming leftSecondBranch .left) leftFirstBranch
  let leftAtSecond :=
    bendAt secondKey
      (childIncoming leftThirdBranch .left) leftSecondBranch
  let leftAtThird :=
    bendAt thirdKey incoming leftThirdBranch
  let leftA :=
    bendsFrom snapshot a first_le_n
      (childIncoming leftFirstBranch .left)
  let leftB :=
    bendsFrom snapshot b second_le_n
      (childIncoming leftFirstBranch .right)
  let leftC :=
    bendsFrom snapshot c third_le_n
      (childIncoming leftSecondBranch .right)
  let leftD :=
    bendsFrom snapshot d upper_le_n
      (childIncoming leftThirdBranch .right)
  let rightAtFirst :=
    bendAt firstKey incoming rightFirstBranch
  let rightAtSecond :=
    bendAt secondKey
      (childIncoming rightFirstBranch .right) rightSecondBranch
  let rightAtThird :=
    bendAt thirdKey
      (childIncoming rightSecondBranch .right) rightThirdBranch
  let rightA :=
    bendsFrom snapshot a first_le_n
      (childIncoming rightFirstBranch .left)
  let rightB :=
    bendsFrom snapshot b second_le_n
      (childIncoming rightSecondBranch .left)
  let rightC :=
    bendsFrom snapshot c third_le_n
      (childIncoming rightThirdBranch .left)
  let rightD :=
    bendsFrom snapshot d upper_le_n
      (childIncoming rightThirdBranch .right)
  have leftDecomposition :
      bendsFrom snapshot
          (.node (.node (.node a b) c) d) upper_le_n incoming =
        unionSeven leftAtFirst leftAtSecond leftAtThird
          leftA leftB leftC leftD := by
    simp only [bendsFrom]
    simp only [leftAtFirst, leftAtSecond, leftAtThird,
      leftA, leftB, leftC, leftD,
      leftFirstBranch, leftSecondBranch, leftThirdBranch,
      leftFirst, leftSecond, leftThird,
      firstKey, secondKey, thirdKey, unionSeven]
    ac_rfl
  have rightDecomposition :
      bendsFrom snapshot
          (.node a (.node b (.node c d))) upper_le_n incoming =
        unionSeven rightAtFirst rightAtSecond rightAtThird
          rightA rightB rightC rightD := by
    simp only [bendsFrom]
    simp only [rightAtFirst, rightAtSecond, rightAtThird,
      rightA, rightB, rightC, rightD,
      rightFirstBranch, rightSecondBranch, rightThirdBranch,
      rightFirst, rightSecond, rightThird,
      firstKey, secondKey, thirdKey, unionSeven]
    ac_rfl
  constructor
  · rw [rightDecomposition, leftDecomposition]
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
  · rw [leftDecomposition, rightDecomposition]
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

namespace DoubleOrientationAt

/--
Every proof-classified contextual double rotation creates at most seven
bends.  The theorem is Boolean-general; in particular its `true`
specialization is the zig-zig creation bound needed by the transcript.
-/
theorem created_le_seven
    {isZigZig : Bool} {n depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      Splay.Accounting.DoubleOrientationAt isZigZig
        (depth := depth) (key := key) before after)
    (snapshot : Snapshot n) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    ((bendsFrom snapshot after upper_le_n incoming) \
      (bendsFrom snapshot before upper_le_n incoming)).card ≤ 7 := by
  induction orientation generalizing incoming with
  | zigZigLeft a b c d =>
      exact
        (zigZig_created_le_seven_both
          snapshot a b c d upper_le_n incoming).1
  | zigZigRight a b c d =>
      exact
        (zigZig_created_le_seven_both
          snapshot a b c d upper_le_n incoming).2
  | zigZagLeftRight a b c d =>
      exact
        zigZagLeftRight_created_le_seven
          snapshot a b c d upper_le_n incoming
  | zigZagRightLeft a b c d =>
      exact
        zigZagRightLeft_created_le_seven
          snapshot a b c d upper_le_n incoming
  | @leftContext isZigZig depth key lower root upper
      before after orientation right ih =>
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
  | @rightContext isZigZig depth key lower root upper
      left before after orientation ih =>
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

/-- A whole-tree contextual double rotation creates at most seven bends. -/
theorem bends_created_le_seven
    {isZigZig : Bool} {n depth key : ℕ}
    {before after : BST 0 n}
    (orientation :
      Splay.Accounting.DoubleOrientationAt isZigZig
        (depth := depth) (key := key) before after)
    (snapshot : Snapshot n) :
    ((bends snapshot after) \ (bends snapshot before)).card ≤ 7 := by
  simpa [bends] using
    created_le_seven orientation snapshot (Nat.le_refl n) none

/-- Explicit zig-zig specialization of `bends_created_le_seven`. -/
theorem true_bends_created_le_seven
    {n depth key : ℕ} {before after : BST 0 n}
    (orientation :
      Splay.Accounting.DoubleOrientationAt true
        (depth := depth) (key := key) before after)
    (snapshot : Snapshot n) :
    ((bends snapshot after) \ (bends snapshot before)).card ≤ 7 :=
  bends_created_le_seven orientation snapshot

end DoubleOrientationAt

end Splay.Accounting.NonZigZagBendGeometry
