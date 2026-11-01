import Splay.Accounting.WholeSplayTemporaryPriorityReduction
import Splay.Accounting.WholeSplayBendCounterexample

namespace Splay.Accounting.WholeSplayTemporaryCoreGeometry

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction

/--
The accessed value keeps priority zero in the canonical two-boundary
temporary snapshot.

This is the first of the three rank facts used by the core splay geometry:
the accessed value has priority zero, the two selected boundary positions
have priority one, and every other position has an even positive priority.
-/
@[simp]
theorem temporarySnapshot_rank_valuePos
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right) :
    (temporarySnapshot comparison key root left right ordered).rank
        (valuePos key) = 0 := by
  rw [temporarySnapshot_rank,
    twoBoundaryTemporaryRank_eq_truePriority]
  · simp [truePriority,
      ofTree_rank_valuePos_eq_zero_of_hasRoot comparison key root]
  · constructor
    · intro equal
      have values := congrArg Fin.val equal
      have less : left.val < (valuePos key).val := ordered.1
      omega
    · intro equal
      have values := congrArg Fin.val equal
      have less : (valuePos key).val < right.val := ordered.2
      omega

/-- The selected left boundary has artificial priority one. -/
@[simp]
theorem temporarySnapshot_rank_left
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right) :
    (temporarySnapshot comparison key root left right ordered).rank left = 1 := by
  rw [temporarySnapshot_rank,
    twoBoundaryTemporaryRank_eq_one_left]

/-- The selected right boundary has artificial priority one. -/
@[simp]
theorem temporarySnapshot_rank_right
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right) :
    (temporarySnapshot comparison key root left right ordered).rank right = 1 := by
  rw [temporarySnapshot_rank,
    twoBoundaryTemporaryRank_eq_one_right]

/--
Every genuine comparison-snapshot position other than the served root has
positive rank.
-/
theorem ofTree_rank_pos_of_ne_valuePos
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (element : External n)
    (different : element ≠ valuePos key) :
    0 < (Snapshot.ofTree comparison).rank element := by
  obtain ⟨leftSubtree, rightSubtree, rfl⟩ := root
  change 0 <
    _root_.Splay.Tree.BST.externalDepth
      (.node leftSubtree rightSubtree) element.val
  have notRoot : element.val ≠ 2 * key.val + 1 := by
    intro equal
    apply different
    apply Fin.ext
    simpa [valuePos] using equal
  by_cases beforeRoot : element.val < 2 * key.val + 1
  · rw [_root_.Splay.Tree.BST.externalDepth_node_of_lt_root
      leftSubtree rightSubtree beforeRoot]
    omega
  · have afterRoot : 2 * key.val + 1 < element.val := by
      omega
    rw [_root_.Splay.Tree.BST.externalDepth_node_of_root_lt
      leftSubtree rightSubtree afterRoot]
    omega

/--
Every ordinary temporary position has an even positive priority, hence at
least two.
-/
theorem two_le_temporarySnapshot_rank_of_ordinary
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right element : External n)
    (ordered : left < valuePos key ∧ valuePos key < right)
    (notLeft : element ≠ left)
    (notRoot : element ≠ valuePos key)
    (notRight : element ≠ right) :
    2 ≤
      (temporarySnapshot comparison key root left right ordered).rank
        element := by
  rw [temporarySnapshot_rank,
    twoBoundaryTemporaryRank_eq_truePriority
      (ordinary := ⟨notLeft, notRight⟩)]
  have positive :=
    ofTree_rank_pos_of_ne_valuePos comparison key root element notRoot
  simp only [truePriority]
  omega

/--
The accessed value is the minimum of every interval that contains it in the
temporary snapshot.  Thus every node on the pre-splay search path selects
the branch leading to the accessed value, independently of the two child
boundary choices.
-/
theorem valuePos_isIntervalMin
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right lower upper : External n)
    (ordered : left < valuePos key ∧ valuePos key < right)
    (inside : lower ≤ valuePos key ∧ valuePos key ≤ upper) :
    IsIntervalMin
      (temporarySnapshot comparison key root left right ordered).rank
      lower upper (valuePos key) := by
  refine ⟨inside.1, inside.2, ?_⟩
  intro element _ _
  rw [temporarySnapshot_rank_valuePos]
  exact Nat.zero_le _

/--
Canonical-owner form of `valuePos_isIntervalMin`.
-/
theorem intervalMin_eq_valuePos
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right lower upper : External n)
    (ordered : left < valuePos key ∧ valuePos key < right)
    (nonempty : lower ≤ upper)
    (inside : lower ≤ valuePos key ∧ valuePos key ≤ upper) :
    (temporarySnapshot comparison key root left right ordered).intervalMin
        lower upper nonempty =
      valuePos key := by
  symm
  apply
    (temporarySnapshot comparison key root left right ordered).intervalMin_unique
  exact valuePos_isIntervalMin comparison key root left right lower upper
    ordered inside

/--
On an interval wholly left of the accessed value, the selected left
boundary is the unique minimum whenever it lies in that interval.
-/
theorem left_isIntervalMin
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right lower upper : External n)
    (ordered : left < valuePos key ∧ valuePos key < right)
    (inside : lower ≤ left ∧ left ≤ upper)
    (leftSide : upper < valuePos key) :
    IsIntervalMin
      (temporarySnapshot comparison key root left right ordered).rank
      lower upper left := by
  refine ⟨inside.1, inside.2, ?_⟩
  intro element elementLower elementUpper
  rw [temporarySnapshot_rank_left]
  by_cases atLeft : element = left
  · subst element
    simp
  have notRoot : element ≠ valuePos key := by
    intro equal
    subst element
    have := elementUpper.trans_lt leftSide
    exact (lt_irrefl _ this)
  have notRight : element ≠ right := by
    intro equal
    subst element
    have elementBeforeRoot := elementUpper.trans_lt leftSide
    exact (not_lt_of_ge (Nat.le_of_lt ordered.2)) elementBeforeRoot
  exact
    (two_le_temporarySnapshot_rank_of_ordinary
      comparison key root left right element ordered atLeft notRoot
        notRight).trans' (by omega)

/--
On an interval wholly right of the accessed value, the selected right
boundary is the unique minimum whenever it lies in that interval.
-/
theorem right_isIntervalMin
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (root : comparison.HasRoot key.val)
    (left right lower upper : External n)
    (ordered : left < valuePos key ∧ valuePos key < right)
    (inside : lower ≤ right ∧ right ≤ upper)
    (rightSide : valuePos key < lower) :
    IsIntervalMin
      (temporarySnapshot comparison key root left right ordered).rank
      lower upper right := by
  refine ⟨inside.1, inside.2, ?_⟩
  intro element elementLower elementUpper
  rw [temporarySnapshot_rank_right]
  by_cases atRight : element = right
  · subst element
    simp
  have notRoot : element ≠ valuePos key := by
    intro equal
    subst element
    have := rightSide.trans_le elementLower
    exact (lt_irrefl _ this)
  have notLeft : element ≠ left := by
    intro equal
    subst element
    have rootBeforeElement := rightSide.trans_le elementLower
    exact (not_lt_of_ge (Nat.le_of_lt ordered.1)) rootBeforeElement
  exact
    (two_le_temporarySnapshot_rank_of_ordinary
      comparison key root left right element ordered notLeft notRoot
        atRight).trans' (by omega)

/--
The two selected positions lie in the exact left- and right-child external
intervals of the accessed node in the pre-splay tree.

This proof-relevant relation follows the search context down to `key`.  At
its terminal constructor the indexed BST exposes the child intervals
`[lower,key)` and `[key+1,upper)`; the four inequalities say precisely that
the selected external positions belong to their closed external inorder
intervals.  This is the structural premise missing from a mere
`left < valuePos key < right` assumption.
-/
inductive BoundaryPlacementAt {n : ℕ}
    (key : Fin n) (left right : External n) :
    {lower upper : ℕ} → BST lower upper → Prop
  | root {lower upper : ℕ}
      (leftSubtree : BST lower key.val)
      (rightSubtree : BST (key.val + 1) upper)
      (leftLower : 2 * lower ≤ left.val)
      (leftUpper : left.val ≤ 2 * key.val)
      (rightLower : 2 * (key.val + 1) ≤ right.val)
      (rightUpper : right.val ≤ 2 * upper) :
      BoundaryPlacementAt key left right
        (.node leftSubtree rightSubtree)
  | leftContext {lower pivot upper : ℕ}
      {leftSubtree : BST lower pivot}
      (placement : BoundaryPlacementAt key left right leftSubtree)
      (rightSubtree : BST (pivot + 1) upper) :
      BoundaryPlacementAt key left right
        (.node leftSubtree rightSubtree)
  | rightContext {lower pivot upper : ℕ}
      (leftSubtree : BST lower pivot)
      {rightSubtree : BST (pivot + 1) upper}
      (placement : BoundaryPlacementAt key left right rightSubtree) :
      BoundaryPlacementAt key left right
        (.node leftSubtree rightSubtree)

namespace BoundaryPlacementAt

/-- Exact child-interval placement implies the required strict order. -/
theorem ordered
    {n lower upper : ℕ} {key : Fin n} {left right : External n}
    {tree : BST lower upper}
    (placement : BoundaryPlacementAt key left right tree) :
    left < valuePos key ∧ valuePos key < right := by
  induction placement with
  | root leftSubtree rightSubtree leftLower leftUpper
      rightLower rightUpper =>
      constructor
      · change left.val < 2 * key.val + 1
        omega
      · change 2 * key.val + 1 < right.val
        omega
  | leftContext placement rightSubtree ih =>
      exact ih
  | rightContext leftSubtree placement ih =>
      exact ih

/--
Elimination form exposing the actual focused child subtrees and both exact
external intervals.
-/
theorem exists_focused_children
    {n lower upper : ℕ} {key : Fin n} {left right : External n}
    {tree : BST lower upper}
    (placement : BoundaryPlacementAt key left right tree) :
    ∃ (childLower childUpper : ℕ)
        (leftSubtree : BST childLower key.val)
        (rightSubtree : BST (key.val + 1) childUpper),
      2 * childLower ≤ left.val ∧
        left.val ≤ 2 * key.val ∧
        2 * (key.val + 1) ≤ right.val ∧
        right.val ≤ 2 * childUpper := by
  induction placement with
  | root leftSubtree rightSubtree leftLower leftUpper
      rightLower rightUpper =>
      exact
        ⟨_, _, leftSubtree, rightSubtree, leftLower, leftUpper,
          rightLower, rightUpper⟩
  | leftContext placement rightSubtree ih =>
      exact ih
  | rightContext leftSubtree placement ih =>
      exact ih

end BoundaryPlacementAt

/--
Endpoint bend identities created by the core splay.
-/
abbrev CreatedIdentity
    {n : ℕ} {before after : BST 0 n}
    (snapshot : Snapshot n) :=
  ↥((bends snapshot after) \ (bends snapshot before))

/--
Endpoint bend identities removed by the core splay.
-/
abbrev RemovedIdentity
    {n : ℕ} {before after : BST 0 n}
    (snapshot : Snapshot n) :=
  ↥((bends snapshot before) \ (bends snapshot after))

/--
The exact finite endpoint classification asserted by the manuscript's core
heavy-path argument.

* At most two newly created identities are administrative: the possible
  attachment bend on the new monotone prefix to each selected boundary.
* Every other newly created identity injects into a genuine zig-zig.  It is
  the possible new top bend of that zig-zig's winning hanging subtree.
* Every genuine zig-zag injects into a distinct endpoint-persistent removed
  identity, namely its lower hit node.

The maps deliberately target the *actual endpoint set differences*.  This
rules out the remove/re-create bug of legacy endpoint aggregation and states
precisely the remaining tree-combinatorial content of the temporary-priority
core proof.
-/
structure EndpointHitClassification
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    (transcript : SplayExecutionTranscriptWitness execution)
    (snapshot : Snapshot n) : Type where
  administrative :
    Finset (CreatedIdentity (before := before) (after := after) snapshot)
  administrative_card_le_two :
    administrative.card ≤ 2
  zigZigWinner :
    ↥((Finset.univ :
      Finset (CreatedIdentity (before := before) (after := after) snapshot)) \
        administrative) →
      Fin transcript.zigZig
  zigZigWinner_injective :
    Function.Injective zigZigWinner
  zigZagVictim :
    Fin transcript.zigZag →
      RemovedIdentity (before := before) (after := after) snapshot
  zigZagVictim_injective :
    Function.Injective zigZagVictim

namespace EndpointHitClassification

/--
The winner/administrative classification proves the sharp endpoint creation
bound `created ≤ #zig-zigs + 2`.
-/
theorem created_le_zigZig_add_two
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    {snapshot : Snapshot n}
    (classification :
      EndpointHitClassification transcript snapshot) :
    ((bends snapshot after) \ (bends snapshot before)).card ≤
      transcript.zigZig + 2 := by
  have charged :
      ((bends snapshot after) \ (bends snapshot before)).card ≤
        transcript.zigZig + classification.administrative.card := by
    simpa using
      Fintype.card_le_of_injective
        classification.zigZigWinner
        classification.zigZigWinner_injective
  exact charged.trans
    (Nat.add_le_add_left
      classification.administrative_card_le_two transcript.zigZig)

/--
The distinct persistent lower-hit identities prove the sharp endpoint
zig-zag removal bound.
-/
theorem zigZag_le_removed
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    {snapshot : Snapshot n}
    (classification :
      EndpointHitClassification transcript snapshot) :
    transcript.zigZag ≤
      ((bends snapshot before) \ (bends snapshot after)).card := by
  simpa using
    Fintype.card_le_of_injective
      classification.zigZagVictim
      classification.zigZagVictim_injective

end EndpointHitClassification

/--
Core endpoint geometry specialized to the canonical temporary snapshot of an
actual splay execution.  The stored `BoundaryPlacementAt` proof prevents the
two artificial priorities from being placed elsewhere on the two sides of
the key; mere order around the key is insufficient for the persistent
zig-zag-victim clause.
-/
structure TemporaryCoreCertificate
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (transcript : SplayExecutionTranscriptWitness execution)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right) : Type where
  placement :
    BoundaryPlacementAt key left right before
  endpoint :
    EndpointHitClassification transcript
      (temporarySnapshot comparison key comparisonRoot left right ordered)

namespace TemporaryCoreCertificate

/-- The canonical temporary core creates at most one bend per zig-zig plus two. -/
theorem created_le
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    (certificate :
      TemporaryCoreCertificate comparison key execution comparisonRoot
        transcript left right ordered) :
    ((bends
        (temporarySnapshot comparison key comparisonRoot left right ordered)
        after) \
      (bends
        (temporarySnapshot comparison key comparisonRoot left right ordered)
        before)).card ≤
      transcript.zigZig + 2 :=
  certificate.endpoint.created_le_zigZig_add_two

/-- Every zig-zag contributes a distinct endpoint-persistent removed bend. -/
theorem zigZag_le_removed
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    {left right : External n}
    {ordered : left < valuePos key ∧ valuePos key < right}
    (certificate :
      TemporaryCoreCertificate comparison key execution comparisonRoot
        transcript left right ordered) :
    transcript.zigZag ≤
      ((bends
          (temporarySnapshot comparison key comparisonRoot left right ordered)
          before) \
        (bends
          (temporarySnapshot comparison key comparisonRoot left right ordered)
          after)).card :=
  certificate.endpoint.zigZag_le_removed

/--
The core classification discharges both core fields of the existing
temporary-priority reduction with budget two.  This low-level adapter still
takes preprocessing invariance and the two restoration chains explicitly;
`WholeSplayTemporaryGeometry` constructs them automatically.
-/
def toCoreTwoCertificate
    {constants : BendConstants}
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    {transcript : SplayExecutionTranscriptWitness execution}
    (selection :
      BoundaryMinimumSelection (Snapshot.ofTree comparison) key)
    (certificate :
      TemporaryCoreCertificate comparison key execution comparisonRoot
        transcript selection.left selection.right selection.ordered)
    {afterLeft : Snapshot n}
    (before_bends_eq :
      bends (Snapshot.ofTree comparison) before =
        bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered) before)
    (restoration :
      TwoBoundaryRestoration comparison selection.left selection.right
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)
        afterLeft after) :
    TemporarySplayBendCertificate.CoreTwoCertificate
      constants comparison key execution comparisonRoot transcript
      selection.left selection.right selection.ordered afterLeft :=
  TemporarySplayBendCertificate.ofBoundaryMinima
    selection before_bends_eq certificate.created_le
      certificate.zigZag_le_removed restoration

end TemporaryCoreCertificate

/-
Checked counterexample to the tempting ordered-only weakening.

The underlying execution is the two-zig-zag example from
`WholeSplayBendCounterexample`.  The artificial positions `4 < 5 < 9` are
correctly ordered around the accessed value position `5`, but position `9`
does not lie in the accessed node's pre-splay right-child interval, which is
the singleton external interval at position `6`.  Under this wrongly placed
temporary priority, the two endpoint bend sets remove only one identity.
-/
namespace OrderedOnlyCounterexample

namespace Base

abbrev E0 := WholeSplayBendCounterexample.E0
abbrev E1 := WholeSplayBendCounterexample.E1
abbrev E2 := WholeSplayBendCounterexample.E2
abbrev E3 := WholeSplayBendCounterexample.E3
abbrev E4 := WholeSplayBendCounterexample.E4
abbrev E5 := WholeSplayBendCounterexample.E5
abbrev E6 := WholeSplayBendCounterexample.E6
abbrev one := WholeSplayBendCounterexample.one
abbrev four := WholeSplayBendCounterexample.four
abbrev threeFour := WholeSplayBendCounterexample.threeFour
abbrev comparison := WholeSplayBendCounterexample.comparison
abbrev before := WholeSplayBendCounterexample.before
abbrev after := WholeSplayBendCounterexample.after
theorem comparison_hasRoot : comparison.HasRoot 2 :=
  WholeSplayBendCounterexample.comparison_hasRoot

end Base

abbrev key : Fin 6 := ⟨2, by omega⟩
abbrev left : External 6 := ⟨4, by omega⟩
abbrev right : External 6 := ⟨9, by omega⟩

theorem ordered : left < valuePos key ∧ valuePos key < right := by
  simp [left, right, key, valuePos]

abbrev snapshot : Snapshot 6 :=
  temporarySnapshot Base.comparison key Base.comparison_hasRoot
    left right ordered

abbrev nodeAt
    {lower pivot upper : ℕ}
    (leftSubtree : BST lower pivot)
    (rightSubtree : BST (pivot + 1) upper)
    (upper_le : upper ≤ 6) : AtNode 6 where
  lower := lower
  root := pivot
  upper := upper
  left := leftSubtree
  right := rightSubtree
  upper_le_n := upper_le

private theorem heavyBranch_eq_of_min
    {lower pivot upper : ℕ}
    (leftSubtree : BST lower pivot)
    (rightSubtree : BST (pivot + 1) upper)
    (upper_le : upper ≤ 6)
    (candidate : External 6)
    (minimum :
      IsIntervalMin snapshot.rank
        ⟨2 * lower, by
          have := leftSubtree.lower_le_upper
          have := rightSubtree.lower_le_upper
          omega⟩
        ⟨2 * upper, by omega⟩ candidate)
    (branch : TernaryBranch)
    (contains : branch.Contains pivot candidate.val) :
    (nodeAt leftSubtree rightSubtree upper_le).heavyBranch snapshot =
      branch := by
  let node := nodeAt leftSubtree rightSubtree upper_le
  have minimum' :
      IsIntervalMin snapshot.rank
        node.wholeLower node.wholeUpper candidate := by
    simpa [node, nodeAt, AtNode.wholeLower, AtNode.wholeUpper] using
      minimum
  have heavy :
      snapshot.IsHeavyBranch
        node.wholeLower node.wholeUpper pivot branch :=
    ⟨candidate, minimum', contains⟩
  exact
    (snapshot.heavyBranch_unique
      node.wholeLower node.wholeUpper node.whole_nonempty pivot heavy).symm

private theorem key_min
    (lower upper : External 6)
    (inside : lower ≤ valuePos key ∧ valuePos key ≤ upper) :
    IsIntervalMin snapshot.rank lower upper (valuePos key) :=
  valuePos_isIntervalMin Base.comparison key Base.comparison_hasRoot
    left right lower upper ordered inside

private theorem left_min
    (lower upper : External 6)
    (inside : lower ≤ left ∧ left ≤ upper)
    (leftSide : upper < valuePos key) :
    IsIntervalMin snapshot.rank lower upper left :=
  left_isIntervalMin Base.comparison key Base.comparison_hasRoot
    left right lower upper ordered inside leftSide

private theorem right_min
    (lower upper : External 6)
    (inside : lower ≤ right ∧ right ≤ upper)
    (rightSide : valuePos key < lower) :
    IsIntervalMin snapshot.rank lower upper right :=
  right_isIntervalMin Base.comparison key Base.comparison_hasRoot
    left right lower upper ordered inside rightSide

theorem before_root_heavy :
    (nodeAt
      (.node Base.E0
        (.node Base.E1
          (.node (.node Base.E2 Base.E3) Base.four)))
      Base.E6 (by omega)).heavyBranch snapshot = .left := by
  apply heavyBranch_eq_of_min
    (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem before_zero_heavy :
    (nodeAt Base.E0
      (.node Base.E1
        (.node (.node Base.E2 Base.E3) Base.four))
      (by omega)).heavyBranch snapshot = .right := by
  apply heavyBranch_eq_of_min
    (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem before_one_heavy :
    (nodeAt Base.E1
      (.node (.node Base.E2 Base.E3) Base.four)
      (by omega)).heavyBranch snapshot = .right := by
  apply heavyBranch_eq_of_min
    (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem before_three_heavy :
    (nodeAt (.node Base.E2 Base.E3) Base.four
      (by omega)).heavyBranch snapshot = .left := by
  apply heavyBranch_eq_of_min
    (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem before_two_heavy :
    (nodeAt Base.E2 Base.E3
      (by omega)).heavyBranch snapshot = .middle := by
  apply heavyBranch_eq_of_min
    (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem four_heavy :
    (nodeAt Base.E4 Base.E5
      (by omega)).heavyBranch snapshot = .middle := by
  apply heavyBranch_eq_of_min
    (candidate := right)
  · apply right_min
    · simp [right]
    · simp [key, valuePos]
  · simp [TernaryBranch.Contains, right]

theorem bends_before :
    bends snapshot Base.before =
      {(⟨0, by omega⟩ : Fin 6), (⟨3, by omega⟩ : Fin 6)} := by
  simp [bends, bendsFrom, Base.before,
    before_root_heavy, before_zero_heavy, before_one_heavy,
    before_three_heavy, before_two_heavy, four_heavy,
    bendAt, Turns, childIncoming]

theorem after_root_heavy :
    (nodeAt
      (.node Base.E0 Base.one)
      (.node Base.threeFour Base.E6)
      (by omega)).heavyBranch snapshot = .middle := by
  apply heavyBranch_eq_of_min
    (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem after_zero_heavy :
    (nodeAt Base.E0 Base.one
      (by omega)).heavyBranch snapshot = .right := by
  apply heavyBranch_eq_of_min
    (candidate := left)
  · apply left_min
    · simp [left]
    · simp [left, key, valuePos]
  · simp [TernaryBranch.Contains, left]

theorem one_heavy :
    (nodeAt Base.E1 Base.E2
      (by omega)).heavyBranch snapshot = .right := by
  apply heavyBranch_eq_of_min
    (candidate := left)
  · apply left_min
    · simp [left]
    · simp [left, key, valuePos]
  · simp [TernaryBranch.Contains, left]

theorem after_five_heavy :
    (nodeAt Base.threeFour Base.E6
      (by omega)).heavyBranch snapshot = .left := by
  apply heavyBranch_eq_of_min
    (candidate := right)
  · apply right_min
    · simp [right]
    · simp [key, valuePos]
  · simp [TernaryBranch.Contains, right]

theorem three_heavy :
    (nodeAt Base.E3 Base.four
      (by omega)).heavyBranch snapshot = .right := by
  apply heavyBranch_eq_of_min
    (candidate := right)
  · apply right_min
    · simp [right]
    · simp [key, valuePos]
  · simp [TernaryBranch.Contains, right]

theorem bends_after :
    bends snapshot Base.after =
      {(⟨3, by omega⟩ : Fin 6)} := by
  simp [bends, bendsFrom, Base.after,
    after_root_heavy, after_zero_heavy, one_heavy,
    after_five_heavy, three_heavy, four_heavy,
    bendAt, Turns, childIncoming]

/-- Two zig-zags have only one endpoint-persistent removed bend. -/
theorem endpoint_removed_eq_one :
    ((bends snapshot Base.before) \
      (bends snapshot Base.after)).card = 1 := by
  simp [bends_before, bends_after]

/--
Strict order of the two artificial positions around the accessed value does
not imply the zig-zag endpoint-removal inequality.
-/
theorem not_orderedOnly_zigZag_le_removed :
    ¬(2 ≤
      ((bends snapshot Base.before) \
        (bends snapshot Base.after)).card) := by
  rw [endpoint_removed_eq_one]
  decide

end OrderedOnlyCounterexample

end Splay.Accounting.WholeSplayTemporaryCoreGeometry
