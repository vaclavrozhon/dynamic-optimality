import Splay.Accounting.LocalBendGeometry

namespace Splay.Accounting.ContextualBendGeometry

open Splay.Rank
open Splay.Tree
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry

/--
The accessed value is a minimum-rank external node of an indexed splay-tree
interval.  The tree shape supplies only the interval endpoints; the rank
snapshot comes from the comparison tree.
-/
def IntervalOwner
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) : Prop :=
  IsIntervalMin snapshot.rank
    (subtreeLower tree upper_le_n)
    (subtreeUpper tree upper_le_n)
    (valuePos key)

namespace IntervalOwner

/--
An interval owner remains the owner of every nested indexed subtree that
contains the same value key.
-/
theorem restrict
    {n outerLower outerUpper innerLower innerUpper : ℕ}
    {snapshot : Snapshot n}
    {outer : BST outerLower outerUpper}
    {inner : BST innerLower innerUpper}
    {outer_le_n : outerUpper ≤ n}
    {key : Fin n}
    (owner : IntervalOwner snapshot outer outer_le_n key)
    (inner_le_n : innerUpper ≤ n)
    (lowerContained : outerLower ≤ innerLower)
    (upperContained : innerUpper ≤ outerUpper)
    (keyLower : innerLower ≤ key.val)
    (keyUpper : key.val < innerUpper) :
    IntervalOwner snapshot inner inner_le_n key := by
  unfold IntervalOwner at owner ⊢
  refine ⟨?_, ?_, ?_⟩
  · change 2 * innerLower ≤ 2 * key.val + 1
    omega
  · change 2 * key.val + 1 ≤ 2 * innerUpper
    omega
  · intro node nodeLower nodeUpper
    apply owner.2.2 node
    · have endpoint :
          subtreeLower outer outer_le_n ≤
            subtreeLower inner inner_le_n := by
        change 2 * outerLower ≤ 2 * innerLower
        omega
      exact endpoint.trans nodeLower
    · have endpoint :
          subtreeUpper inner inner_le_n ≤
            subtreeUpper outer outer_le_n := by
        change 2 * innerUpper ≤ 2 * outerUpper
        omega
      exact nodeUpper.trans endpoint

/--
For a nonempty node interval, an interval owner selects whichever ternary
branch contains its value position.
-/
theorem heavyBranch_eq
    {n lower root upper : ℕ}
    {snapshot : Snapshot n}
    (left : BST lower root) (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) (key : Fin n)
    (owner :
      IntervalOwner snapshot (.node left right) upper_le_n key)
    (branch : TernaryBranch)
    (contains : branch.Contains root (valuePos key).val) :
    let node : AtNode n := {
      lower := lower
      root := root
      upper := upper
      left := left
      right := right
      upper_le_n := upper_le_n
    }
    node.heavyBranch snapshot = branch := by
  let node : AtNode n := {
    lower := lower
    root := root
    upper := upper
    left := left
    right := right
    upper_le_n := upper_le_n
  }
  have owner' :
      IsIntervalMin snapshot.rank
        node.wholeLower node.wholeUpper (valuePos key) := by
    simpa [IntervalOwner, node, subtreeLower, subtreeUpper,
      AtNode.wholeLower, AtNode.wholeUpper] using owner
  have heavy :
      snapshot.IsHeavyBranch
        node.wholeLower node.wholeUpper root branch :=
    ⟨valuePos key, owner', contains⟩
  exact
    (snapshot.heavyBranch_unique
      node.wholeLower node.wholeUpper node.whole_nonempty
      root heavy).symm

end IntervalOwner

/--
The lower hit node of an arbitrary-interval left-right zig-zag is genuinely
removed whenever the promoted value owns the rotated interval.
-/
theorem leftRight_lowerHit_mem_removed
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    (owner :
      IntervalOwner snapshot
        (.node (.node a (.node b c)) d) upper_le_n
        (⟨second, by
          have hc := c.lower_le_upper
          have hd := d.lower_le_upper
          omega⟩ : Fin n)) :
    (⟨first, by
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega⟩ : Fin n) ∈
      (bendsFrom snapshot
          (.node (.node a (.node b c)) d) upper_le_n incoming) \
        (bendsFrom snapshot
          (.node (.node a b) (.node c d)) upper_le_n incoming) := by
  have first_lt_second : first < second := by
    have hb := b.lower_le_upper
    omega
  have second_lt_third : second < third := by
    have hc := c.lower_le_upper
    omega
  have third_lt_upper : third < upper := by
    have hd := d.lower_le_upper
    omega
  have first_lt_n : first < n := by omega
  have second_lt_n : second < n := by omega
  have first_le_n : first ≤ n := Nat.le_of_lt first_lt_n
  have second_le_n : second ≤ n := Nat.le_of_lt second_lt_n
  have third_le_n : third ≤ n := by omega
  let promoted : Fin n := ⟨second, second_lt_n⟩
  let lowerHit : Fin n := ⟨first, first_lt_n⟩
  have owner' :
      IntervalOwner snapshot
        (.node (.node a (.node b c)) d) upper_le_n promoted := by
    simpa [promoted] using owner
  have grandBranch :
      (({
        lower := lower
        root := third
        upper := upper
        left := .node a (.node b c)
        right := d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left := by
    apply IntervalOwner.heavyBranch_eq
      (.node a (.node b c)) d upper_le_n promoted owner' .left
    change 2 * second + 1 ≤ 2 * third
    omega
  have parentOwner :
      IntervalOwner snapshot
        (.node a (.node b c)) third_le_n promoted := by
    apply owner'.restrict third_le_n
    · exact Nat.le_refl lower
    · exact Nat.le_of_lt third_lt_upper
    · change lower ≤ second
      have ha := a.lower_le_upper
      omega
    · exact second_lt_third
  have parentBranch :
      (({
        lower := lower
        root := first
        upper := third
        left := a
        right := .node b c
        upper_le_n := third_le_n
      } : AtNode n).heavyBranch snapshot) = .right := by
    apply IntervalOwner.heavyBranch_eq
      a (.node b c) third_le_n promoted parentOwner .right
    change 2 * first + 2 ≤ 2 * second + 1
    omega
  have afterOwner :
      IntervalOwner snapshot
        (.node (.node a b) (.node c d)) upper_le_n promoted := by
    simpa [IntervalOwner, subtreeLower, subtreeUpper] using owner'
  have afterBranch :
      (({
        lower := lower
        root := second
        upper := upper
        left := .node a b
        right := .node c d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle := by
    apply IntervalOwner.heavyBranch_eq
      (.node a b) (.node c d) upper_le_n promoted afterOwner .middle
    rfl
  have beforeMember :
      lowerHit ∈
        bendsFrom snapshot
          (.node (.node a (.node b c)) d) upper_le_n incoming := by
    simp [bendsFrom, grandBranch, parentBranch,
      childIncoming, bendAt, Turns, lowerHit]
  have afterNotMember :
      lowerHit ∉
        bendsFrom snapshot
          (.node (.node a b) (.node c d)) upper_le_n incoming := by
    intro member
    simp [bendsFrom, afterBranch, childIncoming, bendAt, Turns] at member
    rcases member with inA | inB | inC | inD
    · have bounds :=
        mem_bendsFrom_bounds snapshot a first_le_n _ inA
      exact (Nat.lt_irrefl first) bounds.2
    · have bounds :=
        mem_bendsFrom_bounds snapshot b second_le_n _ inB
      have lowerBound := bounds.1
      change first + 1 ≤ first at lowerBound
      omega
    · have bounds :=
        mem_bendsFrom_bounds snapshot c third_le_n _ inC
      have lowerBound := bounds.1
      change second + 1 ≤ first at lowerBound
      omega
    · have bounds :=
        mem_bendsFrom_bounds snapshot d upper_le_n _ inD
      have lowerBound := bounds.1
      change third + 1 ≤ first at lowerBound
      omega
  exact Finset.mem_sdiff.mpr ⟨beforeMember, afterNotMember⟩

/-- Mirror-image arbitrary-interval removal theorem. -/
theorem rightLeft_lowerHit_mem_removed
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    (owner :
      IntervalOwner snapshot
        (.node a (.node (.node b c) d)) upper_le_n
        (⟨second, by
          have hc := c.lower_le_upper
          have hd := d.lower_le_upper
          omega⟩ : Fin n)) :
    (⟨third, by
      have hd := d.lower_le_upper
      omega⟩ : Fin n) ∈
      (bendsFrom snapshot
          (.node a (.node (.node b c) d)) upper_le_n incoming) \
        (bendsFrom snapshot
          (.node (.node a b) (.node c d)) upper_le_n incoming) := by
  have first_lt_second : first < second := by
    have hb := b.lower_le_upper
    omega
  have second_lt_third : second < third := by
    have hc := c.lower_le_upper
    omega
  have third_lt_upper : third < upper := by
    have hd := d.lower_le_upper
    omega
  have first_lt_n : first < n := by omega
  have second_lt_n : second < n := by omega
  have third_lt_n : third < n := by omega
  have first_le_n : first ≤ n := Nat.le_of_lt first_lt_n
  have second_le_n : second ≤ n := Nat.le_of_lt second_lt_n
  have third_le_n : third ≤ n := Nat.le_of_lt third_lt_n
  let promoted : Fin n := ⟨second, second_lt_n⟩
  let lowerHit : Fin n := ⟨third, third_lt_n⟩
  have owner' :
      IntervalOwner snapshot
        (.node a (.node (.node b c) d)) upper_le_n promoted := by
    simpa [promoted] using owner
  have grandBranch :
      (({
        lower := lower
        root := first
        upper := upper
        left := a
        right := .node (.node b c) d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .right := by
    apply IntervalOwner.heavyBranch_eq
      a (.node (.node b c) d) upper_le_n promoted owner' .right
    change 2 * first + 2 ≤ 2 * second + 1
    omega
  have parentOwner :
      IntervalOwner snapshot
        (.node (.node b c) d) upper_le_n promoted := by
    apply owner'.restrict upper_le_n
    · have ha := a.lower_le_upper
      omega
    · exact Nat.le_refl upper
    · change first + 1 ≤ second
      omega
    · change second < upper
      omega
  have parentBranch :
      (({
        lower := first + 1
        root := third
        upper := upper
        left := .node b c
        right := d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left := by
    apply IntervalOwner.heavyBranch_eq
      (.node b c) d upper_le_n promoted parentOwner .left
    change 2 * second + 1 ≤ 2 * third
    omega
  have afterOwner :
      IntervalOwner snapshot
        (.node (.node a b) (.node c d)) upper_le_n promoted := by
    simpa [IntervalOwner, subtreeLower, subtreeUpper] using owner'
  have afterBranch :
      (({
        lower := lower
        root := second
        upper := upper
        left := .node a b
        right := .node c d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle := by
    apply IntervalOwner.heavyBranch_eq
      (.node a b) (.node c d) upper_le_n promoted afterOwner .middle
    rfl
  have beforeMember :
      lowerHit ∈
        bendsFrom snapshot
          (.node a (.node (.node b c) d)) upper_le_n incoming := by
    simp [bendsFrom, grandBranch, parentBranch,
      childIncoming, bendAt, Turns, lowerHit]
  have afterNotMember :
      lowerHit ∉
        bendsFrom snapshot
          (.node (.node a b) (.node c d)) upper_le_n incoming := by
    intro member
    simp [bendsFrom, afterBranch, childIncoming, bendAt, Turns] at member
    rcases member with inA | inB | inC | inD
    · have bounds :=
        mem_bendsFrom_bounds snapshot a first_le_n _ inA
      have upperBound := bounds.2
      change third < first at upperBound
      omega
    · have bounds :=
        mem_bendsFrom_bounds snapshot b second_le_n _ inB
      have upperBound := bounds.2
      change third < second at upperBound
      omega
    · have bounds :=
        mem_bendsFrom_bounds snapshot c third_le_n _ inC
      exact (Nat.lt_irrefl third) bounds.2
    · have bounds :=
        mem_bendsFrom_bounds snapshot d upper_le_n _ inD
      have lowerBound := bounds.1
      change third + 1 ≤ third at lowerBound
      omega
  exact Finset.mem_sdiff.mpr ⟨beforeMember, afterNotMember⟩

namespace ZigZagAt

/-- The accessed key lies in every interval indexed by a contextual zig-zag. -/
theorem key_bounds
    {key lower upper : ℕ} {before after : BST lower upper}
    (step : ZigZagAt key before after) :
    lower ≤ key ∧ key < upper := by
  obtain ⟨depth, double⟩ := step.toDoubleRotationAt
  exact double.key_bounds

/-- A removed identity in a left child remains removed after adding a context. -/
theorem lift_removed_leftContext
    {n lower root upper : ℕ}
    (snapshot : Snapshot n)
    (before after : BST lower root)
    (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    {removed : Fin n}
    (localRemoved :
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := before
        right := right
        upper_le_n := upper_le_n
      }
      let outgoing := node.heavyBranch snapshot
      removed ∈
        (bendsFrom snapshot before (by
            have hRight := right.lower_le_upper
            omega) (childIncoming outgoing .left)) \
          (bendsFrom snapshot after (by
            have hRight := right.lower_le_upper
            omega) (childIncoming outgoing .left))) :
    removed ∈
      (bendsFrom snapshot (.node before right) upper_le_n incoming) \
        (bendsFrom snapshot (.node after right) upper_le_n incoming) := by
  let node : AtNode n := {
    lower := lower
    root := root
    upper := upper
    left := before
    right := right
    upper_le_n := upper_le_n
  }
  let outgoing := node.heavyBranch snapshot
  have inner_le_n : root ≤ n := by
    have hRight := right.lower_le_upper
    omega
  have localRemoved' :
      removed ∈
        (bendsFrom snapshot before inner_le_n
            (childIncoming outgoing .left)) \
          (bendsFrom snapshot after inner_le_n
            (childIncoming outgoing .left)) := by
    simpa [node, outgoing] using localRemoved
  have localBefore :=
    (Finset.mem_sdiff.mp localRemoved').1
  have localAfter :=
    (Finset.mem_sdiff.mp localRemoved').2
  have removedBounds :=
    mem_bendsFrom_bounds snapshot before inner_le_n
      (childIncoming outgoing .left) localBefore
  have beforeMember :
      removed ∈
        bendsFrom snapshot (.node before right) upper_le_n incoming := by
    simp only [bendsFrom, Finset.mem_union]
    exact Or.inr (Or.inl localBefore)
  have afterNotMember :
      removed ∉
        bendsFrom snapshot (.node after right) upper_le_n incoming := by
    intro member
    simp only [bendsFrom, Finset.mem_union] at member
    rcases member with atRoot | inInner | inRight
    · unfold bendAt at atRoot
      split at atRoot
      · have removed_eq :
            removed.val = root := by
          simpa using congrArg Fin.val (Finset.mem_singleton.mp atRoot)
        omega
      · simp at atRoot
    · exact localAfter inInner
    · have siblingBounds :=
        mem_bendsFrom_bounds snapshot right upper_le_n _ inRight
      omega
  exact Finset.mem_sdiff.mpr ⟨beforeMember, afterNotMember⟩

/-- Mirror context lift for a removed identity in a right child. -/
theorem lift_removed_rightContext
    {n lower root upper : ℕ}
    (snapshot : Snapshot n)
    (left : BST lower root)
    (before after : BST (root + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    {removed : Fin n}
    (localRemoved :
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := before
        upper_le_n := upper_le_n
      }
      let outgoing := node.heavyBranch snapshot
      removed ∈
        (bendsFrom snapshot before upper_le_n
            (childIncoming outgoing .right)) \
          (bendsFrom snapshot after upper_le_n
            (childIncoming outgoing .right))) :
    removed ∈
      (bendsFrom snapshot (.node left before) upper_le_n incoming) \
        (bendsFrom snapshot (.node left after) upper_le_n incoming) := by
  let node : AtNode n := {
    lower := lower
    root := root
    upper := upper
    left := left
    right := before
    upper_le_n := upper_le_n
  }
  let outgoing := node.heavyBranch snapshot
  have localRemoved' :
      removed ∈
        (bendsFrom snapshot before upper_le_n
            (childIncoming outgoing .right)) \
          (bendsFrom snapshot after upper_le_n
            (childIncoming outgoing .right)) := by
    simpa [node, outgoing] using localRemoved
  have localBefore :=
    (Finset.mem_sdiff.mp localRemoved').1
  have localAfter :=
    (Finset.mem_sdiff.mp localRemoved').2
  have removedBounds :=
    mem_bendsFrom_bounds snapshot before upper_le_n
      (childIncoming outgoing .right) localBefore
  have left_le_n : root ≤ n := by
    have hBefore := before.lower_le_upper
    omega
  have beforeMember :
      removed ∈
        bendsFrom snapshot (.node left before) upper_le_n incoming := by
    simp only [bendsFrom, Finset.mem_union]
    exact Or.inr (Or.inr localBefore)
  have afterNotMember :
      removed ∉
        bendsFrom snapshot (.node left after) upper_le_n incoming := by
    intro member
    simp only [bendsFrom, Finset.mem_union] at member
    rcases member with atRoot | inLeft | inInner
    · unfold bendAt at atRoot
      split at atRoot
      · have removed_eq :
            removed.val = root := by
          simpa using congrArg Fin.val (Finset.mem_singleton.mp atRoot)
        omega
      · simp at atRoot
    · have siblingBounds :=
        mem_bendsFrom_bounds snapshot left left_le_n _ inLeft
      omega
    · exact localAfter inInner
  exact Finset.mem_sdiff.mpr ⟨beforeMember, afterNotMember⟩

/--
Every contextual zig-zag removes a genuine bend when the accessed value owns
the complete interval on which the contextual action is viewed.
-/
theorem exists_removed_of_intervalOwner
    {n key lower upper : ℕ}
    {before after : BST lower upper}
    (step : ZigZagAt key before after)
    (snapshot : Snapshot n) (upper_le_n : upper ≤ n)
    (key_lt_n : key < n)
    (incoming : Option TernaryBranch)
    (owner :
      IntervalOwner snapshot before upper_le_n
        (⟨key, key_lt_n⟩ : Fin n)) :
    ∃ removed : Fin n,
      removed ∈
        (bendsFrom snapshot before upper_le_n incoming) \
          (bendsFrom snapshot after upper_le_n incoming) := by
  induction step generalizing incoming with
  | @leftRight lower first second third upper a b c d =>
      let removed : Fin n := ⟨first, by
        have hb := b.lower_le_upper
        have hc := c.lower_le_upper
        have hd := d.lower_le_upper
        omega⟩
      refine ⟨removed, ?_⟩
      exact leftRight_lowerHit_mem_removed
        snapshot a b c d upper_le_n incoming (by simpa using owner)
  | @rightLeft lower first second third upper a b c d =>
      let removed : Fin n := ⟨third, by
        have hd := d.lower_le_upper
        omega⟩
      refine ⟨removed, ?_⟩
      exact rightLeft_lowerHit_mem_removed
        snapshot a b c d upper_le_n incoming (by simpa using owner)
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
      have inner_le_n : root ≤ n := by
        have hRight := right.lower_le_upper
        omega
      have bounds := key_bounds step
      have innerOwner :
          IntervalOwner snapshot before inner_le_n
            (⟨key, key_lt_n⟩ : Fin n) := by
        apply owner.restrict inner_le_n
        · exact Nat.le_refl lower
        · have hRight := right.lower_le_upper
          omega
        · exact bounds.1
        · exact bounds.2
      obtain ⟨removed, localRemoved⟩ :=
        ih inner_le_n key_lt_n (childIncoming outgoing .left)
          innerOwner
      refine ⟨removed, ?_⟩
      exact lift_removed_leftContext
        snapshot before after right upper_le_n incoming
          (by simpa [node, outgoing] using localRemoved)
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
      have bounds := key_bounds step
      have innerOwner :
          IntervalOwner snapshot before upper_le_n
            (⟨key, key_lt_n⟩ : Fin n) := by
        apply owner.restrict upper_le_n
        · have hLeft := left.lower_le_upper
          omega
        · exact Nat.le_refl upper
        · exact bounds.1
        · exact bounds.2
      obtain ⟨removed, localRemoved⟩ :=
        ih upper_le_n key_lt_n (childIncoming outgoing .right)
          innerOwner
      refine ⟨removed, ?_⟩
      exact lift_removed_rightContext
        snapshot left before after upper_le_n incoming
          (by simpa [node, outgoing] using localRemoved)

/--
A comparison tree serving `key` at its root makes `key` the owner of the
complete interval of any splay-tree shape on the same key universe.
-/
theorem fullIntervalOwner_of_comparisonRoot
    {n : ℕ} (key : Fin n)
    (splayTree comparison : BST 0 n)
    (root : comparison.HasRoot key.val) :
    IntervalOwner (Snapshot.ofTree comparison) splayTree
      (Nat.le_refl n) key := by
  let lower : External n := ⟨0, by omega⟩
  let upper : External n := ⟨2 * n, by omega⟩
  have minimum :=
    (Snapshot.ofTree comparison).intervalMin_isMin
      lower upper (by
        change (0 : ℕ) ≤ 2 * n
        omega)
  have minimum_eq :=
    globalIntervalMin_eq_valuePos_of_hasRoot comparison key root
  rw [minimum_eq] at minimum
  simpa [IntervalOwner, lower, upper, subtreeLower, subtreeUpper] using
    minimum

/-- Exact finite bend action of a contextual zig-zag. -/
noncomputable def bendAction
    {n : ℕ} {key : Fin n} {before after : BST 0 n}
    (_step : ZigZagAt key.val before after)
    (snapshot : Snapshot n) : BendAction :=
  BendAction.between .splay 0 1
    (bends snapshot before) (bends snapshot after)

/-- A served contextual zig-zag removes at least one actual bend identity. -/
theorem one_le_removed_of_comparisonRoot
    {n : ℕ} {key : Fin n} {before after : BST 0 n}
    (step : ZigZagAt key.val before after)
    (comparison : BST 0 n)
    (root : comparison.HasRoot key.val) :
    1 ≤ ((bends (Snapshot.ofTree comparison) before) \
      (bends (Snapshot.ofTree comparison) after)).card := by
  have owner :=
    fullIntervalOwner_of_comparisonRoot
      key before comparison root
  obtain ⟨removed, member⟩ :=
    exists_removed_of_intervalOwner step
      (Snapshot.ofTree comparison) (Nat.le_refl n)
      key.isLt none owner
  exact Finset.one_le_card.mpr ⟨removed, by
    simpa [bends] using member⟩

/--
The contextual action satisfies exactly the local zig-zag clause consumed by
`ZigZagBend`: one zig-zag, no zig-zig, at least one removal, and at most seven
creations.
-/
theorem bendAction_locallySound_of_comparisonRoot
    {n : ℕ} {key : Fin n} {before after : BST 0 n}
    (step : ZigZagAt key.val before after)
    (comparison : BST 0 n) (constants : BendConstants)
    (splayAllowance : 7 ≤ constants.splay)
    (root : comparison.HasRoot key.val) :
    (bendAction step
      (Snapshot.ofTree comparison)).LocallySound constants := by
  constructor
  · simpa [bendAction, BendAction.between] using
      one_le_removed_of_comparisonRoot step comparison root
  · have created :=
      step.created_le_seven
        (Snapshot.ofTree comparison) (Nat.le_refl n) none
    simpa [bendAction, bends, BendAction.between] using
      created.trans splayAllowance

/-- Exact singleton finite-set history for a contextual zig-zag. -/
theorem bendAction_history
    {n : ℕ} {key : Fin n} {before after : BST 0 n}
    (step : ZigZagAt key.val before after)
    (snapshot : Snapshot n) :
    FiniteBendHistory n
      (bends snapshot before)
      [bendAction step snapshot]
      (bends snapshot after) := by
  simpa [bendAction] using
    (FiniteBendHistory.cons
      (n := n) (before := bends snapshot before)
      .splay 0 1
      (FiniteBendHistory.nil (bends snapshot after)))

/--
The requested packaged local witness, now valid at arbitrary contextual
depth and discharged directly from a serving comparison-tree state.
-/
noncomputable def finiteBendStep_of_comparisonRoot
    {n : ℕ} {key : Fin n} {before after : BST 0 n}
    (step : ZigZagAt key.val before after)
    (comparison : BST 0 n) (constants : BendConstants)
    (splayAllowance : 7 ≤ constants.splay)
    (root : comparison.HasRoot key.val) :
    LocalFiniteBendStep constants n where
  beforeBends := bends (Snapshot.ofTree comparison) before
  afterBends := bends (Snapshot.ofTree comparison) after
  action := bendAction step (Snapshot.ofTree comparison)
  history := bendAction_history step (Snapshot.ofTree comparison)
  locallySound :=
    bendAction_locallySound_of_comparisonRoot step
      comparison constants splayAllowance root

end ZigZagAt

end Splay.Accounting.ContextualBendGeometry
