import Splay.Accounting.WholeSplayTemporaryCoreGeometry
import Splay.Accounting.WholeSplayTemporaryBoundaryGeometry

namespace Splay.Accounting.WholeSplayTemporaryCoreClassification

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.ContextualBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryBoundaryGeometry

/--
Number of left/right turns on the search path to `key`, with an optional
incoming direction from a surrounding context.

This is the purely structural counterpart of bends on the owner path: when
the accessed external value is the interval minimum, every search edge is
heavy, so exactly these direction changes are path bends.
-/
def searchTurnCountFrom
    {lower upper : ℕ} (incoming : Option TernaryBranch) :
    BST lower upper → ℕ → ℕ
  | .empty _, _ => 0
  | .node (root := root) left right, key =>
      if key = root then
        0
      else if key < root then
        (if LocalBendGeometry.Turns incoming .left then 1 else 0) +
          searchTurnCountFrom (some .left) left key
      else
        (if LocalBendGeometry.Turns incoming .right then 1 else 0) +
          searchTurnCountFrom (some .right) right key

/-- Global search-path turn count. -/
def searchTurnCount
    {lower upper : ℕ} (tree : BST lower upper) (key : ℕ) : ℕ :=
  searchTurnCountFrom none tree key

/--
A same-direction double rotation cannot increase the residual search-path
turn count, while an opposite-direction double rotation consumes at least
one turn.  The statement is generalized over `incoming`, so surrounding
contexts lift without any boundary case.
-/
theorem searchTurnCountFrom_after_add_orientation_le_before
    {isZigZig : Bool} {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt isZigZig
        (depth := depth) (key := key) before after)
    (incoming : Option TernaryBranch) :
    searchTurnCountFrom incoming after key +
        (if isZigZig then 0 else 1) ≤
      searchTurnCountFrom incoming before key := by
  induction orientation generalizing incoming with
  | @zigZigLeft lower first second third upper a b c d =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      have dBounds := d.lower_le_upper
      have first_lt_second : first < second := by omega
      simp [searchTurnCountFrom, LocalBendGeometry.Turns,
        first_lt_second]
  | @zigZigRight lower first second third upper a b c d =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      have dBounds := d.lower_le_upper
      simp [searchTurnCountFrom, LocalBendGeometry.Turns]
  | @zigZagLeftRight lower first second third upper a b c d =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      have dBounds := d.lower_le_upper
      have second_lt_third : second < third := by omega
      have second_ne_first : second ≠ first := by omega
      have second_ne_third : second ≠ third := by omega
      have not_second_lt_first : ¬ second < first := by omega
      simp [searchTurnCountFrom, LocalBendGeometry.Turns,
        second_lt_third, second_ne_first,
        second_ne_third, not_second_lt_first]
  | @zigZagRightLeft lower first second third upper a b c d =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      have dBounds := d.lower_le_upper
      have second_lt_third : second < third := by omega
      have second_ne_first : second ≠ first := by omega
      have second_ne_third : second ≠ third := by omega
      have not_second_lt_first : ¬ second < first := by omega
      simp [searchTurnCountFrom, LocalBendGeometry.Turns,
        second_lt_third, second_ne_first,
        second_ne_third, not_second_lt_first]
  | @leftContext isZigZig depth key lower root upper
      before after orientation contextRight ih =>
      have keyBounds := doubleOrientationAt_key_bounds orientation
      have rightBounds := contextRight.lower_le_upper
      simp only [searchTurnCountFrom]
      split
      · omega
      · split
        · have nested := ih (some .left)
          omega
        · omega
  | @rightContext isZigZig depth key lower root upper
      contextLeft before after orientation ih =>
      have keyBounds := doubleOrientationAt_key_bounds orientation
      have leftBounds := contextLeft.lower_le_upper
      simp only [searchTurnCountFrom]
      split
      · omega
      · split
        · omega
        · have nested := ih (some .right)
          omega

theorem searchTurnCountFrom_after_le_before_of_zigZig
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt true
        (depth := depth) (key := key) before after)
    (incoming : Option TernaryBranch) :
    searchTurnCountFrom incoming after key ≤
      searchTurnCountFrom incoming before key := by
  simpa using
    searchTurnCountFrom_after_add_orientation_le_before
      orientation incoming

theorem searchTurnCountFrom_after_succ_le_before_of_zigZag
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt false
        (depth := depth) (key := key) before after)
    (incoming : Option TernaryBranch) :
    searchTurnCountFrom incoming after key + 1 ≤
      searchTurnCountFrom incoming before key := by
  simpa using
    searchTurnCountFrom_after_add_orientation_le_before
      orientation incoming

namespace BoundaryPlacementAt

/-- The focused key belongs to every tree interval carrying its placement. -/
theorem key_bounds
    {n lower upper : ℕ} {key : Fin n} {left right : External n}
    {tree : BST lower upper}
    (placement : BoundaryPlacementAt key left right tree) :
    lower ≤ key.val ∧ key.val < upper := by
  induction placement with
  | root leftSubtree rightSubtree =>
      have leftBounds := leftSubtree.lower_le_upper
      have rightBounds := rightSubtree.lower_le_upper
      omega
  | leftContext placement rightSubtree ih =>
      have rightBounds := rightSubtree.lower_le_upper
      omega
  | rightContext leftSubtree placement ih =>
      have leftBounds := leftSubtree.lower_le_upper
      omega

/--
The exact placement of the two artificial boundary minima is preserved by
the final one-level splay rotation.
-/
theorem after_zig
    {n lower upper : ℕ} {key : Fin n} {left right : External n}
    {before after : BST lower upper}
    (placement : BoundaryPlacementAt key left right before)
    (step : Zig key.val before after) :
    BoundaryPlacementAt key left right after := by
  cases step with
  | @fromLeft lower promoted demoted upper a b c =>
      cases placement with
      | root leftSubtree rightSubtree leftLower leftUpper
          rightLower rightUpper =>
          have bounds := b.lower_le_upper
          omega
      | leftContext placement c =>
          cases placement with
          | root a b leftLower leftUpper rightLower rightUpper =>
              exact .root a (.node b c) leftLower leftUpper
                rightLower (by
                  have bounds := c.lower_le_upper
                  omega)
          | leftContext placement b =>
              have bounds := key_bounds placement
              omega
          | rightContext a placement =>
              have bounds := key_bounds placement
              omega
      | rightContext leftSubtree placement =>
          have bounds := key_bounds placement
          have middleBounds := b.lower_le_upper
          omega
  | @fromRight lower demoted promoted upper a b c =>
      cases placement with
      | root leftSubtree rightSubtree leftLower leftUpper
          rightLower rightUpper =>
          have bounds := b.lower_le_upper
          omega
      | leftContext placement rightSubtree =>
          have bounds := key_bounds placement
          have middleBounds := b.lower_le_upper
          omega
      | rightContext a placement =>
          cases placement with
          | root b c leftLower leftUpper rightLower rightUpper =>
              exact .root (.node a b) c
                (by
                  have bounds := a.lower_le_upper
                  omega)
                leftUpper rightLower rightUpper
          | leftContext placement c =>
              have bounds := key_bounds placement
              omega
          | rightContext b placement =>
              have bounds := key_bounds placement
              omega

/--
The boundary placement is preserved by a root double rotation.  In each of
the four orientations, the two selected external positions remain in the
two child intervals of the promoted key.
-/
theorem after_doubleRotation
    {n lower upper : ℕ} {key : Fin n} {left right : External n}
    {before after : BST lower upper}
    (placement : BoundaryPlacementAt key left right before)
    (step : DoubleRotation key.val before after) :
    BoundaryPlacementAt key left right after := by
  cases step with
  | @zigZigLeft lower first second third upper a b c d =>
      cases placement with
      | root leftSubtree rightSubtree leftLower leftUpper
          rightLower rightUpper =>
          have firstSecond := b.lower_le_upper
          have secondThird := c.lower_le_upper
          omega
      | leftContext placement d =>
          cases placement with
          | root leftSubtree rightSubtree leftLower leftUpper
              rightLower rightUpper =>
              have firstSecond := b.lower_le_upper
              omega
          | leftContext placement c =>
              cases placement with
              | root a b leftLower leftUpper rightLower rightUpper =>
                  exact .root a (.node b (.node c d))
                    leftLower leftUpper rightLower (by
                      have cBounds := c.lower_le_upper
                      have dBounds := d.lower_le_upper
                      omega)
              | leftContext placement b =>
                  have bounds := key_bounds placement
                  omega
              | rightContext a placement =>
                  have bounds := key_bounds placement
                  omega
          | rightContext leftSubtree placement =>
              have bounds := key_bounds placement
              have firstSecond := b.lower_le_upper
              omega
      | rightContext leftSubtree placement =>
          have bounds := key_bounds placement
          have firstSecond := b.lower_le_upper
          have secondThird := c.lower_le_upper
          omega
  | @zigZigRight lower first second third upper a b c d =>
      cases placement with
      | root leftSubtree rightSubtree leftLower leftUpper
          rightLower rightUpper =>
          have firstSecond := b.lower_le_upper
          have secondThird := c.lower_le_upper
          omega
      | leftContext placement rightSubtree =>
          have bounds := key_bounds placement
          have firstSecond := b.lower_le_upper
          have secondThird := c.lower_le_upper
          omega
      | rightContext a placement =>
          cases placement with
          | root leftSubtree rightSubtree leftLower leftUpper
              rightLower rightUpper =>
              have secondThird := c.lower_le_upper
              omega
          | leftContext placement d =>
              have bounds := key_bounds placement
              have secondThird := c.lower_le_upper
              omega
          | rightContext b placement =>
              cases placement with
              | root c d leftLower leftUpper rightLower rightUpper =>
                  exact .root (.node (.node a b) c) d
                    (by
                      have aBounds := a.lower_le_upper
                      have bBounds := b.lower_le_upper
                      omega)
                    leftUpper rightLower rightUpper
              | leftContext placement d =>
                  have bounds := key_bounds placement
                  omega
              | rightContext c placement =>
                  have bounds := key_bounds placement
                  omega
  | @zigZagLeftRight lower first second third upper a b c d =>
      cases placement with
      | root leftSubtree rightSubtree leftLower leftUpper
          rightLower rightUpper =>
          have secondThird := c.lower_le_upper
          omega
      | leftContext placement d =>
          cases placement with
          | root leftSubtree rightSubtree leftLower leftUpper
              rightLower rightUpper =>
              have firstSecond := b.lower_le_upper
              omega
          | leftContext placement rightSubtree =>
              have bounds := key_bounds placement
              have firstSecond := b.lower_le_upper
              omega
          | rightContext a placement =>
              cases placement with
              | root b c leftLower leftUpper rightLower rightUpper =>
                  exact .root (.node a b) (.node c d)
                    (by
                      have aBounds := a.lower_le_upper
                      omega)
                    leftUpper rightLower (by
                      have dBounds := d.lower_le_upper
                      omega)
              | leftContext placement c =>
                  have bounds := key_bounds placement
                  omega
              | rightContext b placement =>
                  have bounds := key_bounds placement
                  omega
      | rightContext leftSubtree placement =>
          have bounds := key_bounds placement
          have secondThird := c.lower_le_upper
          omega
  | @zigZagRightLeft lower first second third upper a b c d =>
      cases placement with
      | root leftSubtree rightSubtree leftLower leftUpper
          rightLower rightUpper =>
          have firstSecond := b.lower_le_upper
          omega
      | leftContext placement rightSubtree =>
          have bounds := key_bounds placement
          have firstSecond := b.lower_le_upper
          omega
      | rightContext a placement =>
          cases placement with
          | root leftSubtree rightSubtree leftLower leftUpper
              rightLower rightUpper =>
              have secondThird := c.lower_le_upper
              omega
          | leftContext placement d =>
              cases placement with
              | root b c leftLower leftUpper rightLower rightUpper =>
                  exact .root (.node a b) (.node c d)
                    (by
                      have aBounds := a.lower_le_upper
                      omega)
                    leftUpper rightLower (by
                      have dBounds := d.lower_le_upper
                      omega)
              | leftContext placement c =>
                  have bounds := key_bounds placement
                  omega
              | rightContext b placement =>
                  have bounds := key_bounds placement
                  omega
          | rightContext leftSubtree placement =>
              have bounds := key_bounds placement
              have secondThird := c.lower_le_upper
              omega

/--
Context lifting preserves boundary placement for a genuine contextual double
rotation.  Together with `after_doubleRotation`, this covers every non-final
splay step.
-/
private theorem after_doubleRotationAt_of_eq
    {n depth keyVal lower upper : ℕ} {key : Fin n}
    {left right : External n}
    {before after : BST lower upper}
    (placement : BoundaryPlacementAt key left right before)
    (step : DoubleRotationAt depth keyVal before after)
    (key_eq : key.val = keyVal) :
    BoundaryPlacementAt key left right after := by
  induction step generalizing key with
  | root step =>
      rw [← key_eq] at step
      exact after_doubleRotation placement step
  | @leftContext depth keyVal lower root upper
      before after step contextRight ih =>
      cases placement with
      | root leftSubtree rightSubtree leftLower leftUpper
          rightLower rightUpper =>
          have bounds := step.key_bounds
          omega
      | leftContext placement contextRight =>
          exact .leftContext (ih placement key_eq) contextRight
      | rightContext contextLeft placement =>
          have innerBounds := step.key_bounds
          have placementBounds := key_bounds placement
          omega
  | @rightContext depth keyVal lower root upper
      contextLeft before after step ih =>
      cases placement with
      | root leftSubtree rightSubtree leftLower leftUpper
          rightLower rightUpper =>
          have bounds := step.key_bounds
          omega
      | leftContext placement contextRight =>
          have innerBounds := step.key_bounds
          have placementBounds := key_bounds placement
          omega
      | rightContext contextLeft placement =>
          exact .rightContext contextLeft (ih placement key_eq)

/--
Context lifting preserves boundary placement for a genuine contextual double
rotation.  Together with `after_doubleRotation`, this covers every non-final
splay step.
-/
theorem after_doubleRotationAt
    {n depth lower upper : ℕ} {key : Fin n}
    {left right : External n}
    {before after : BST lower upper}
    (placement : BoundaryPlacementAt key left right before)
    (step : DoubleRotationAt depth key.val before after) :
    BoundaryPlacementAt key left right after :=
  after_doubleRotationAt_of_eq placement step rfl

/-- Every actual splay step preserves the selected boundary placement. -/
theorem after_splayStep
    {n lower upper : ℕ} {key : Fin n}
    {left right : External n}
    {before after : BST lower upper}
    (placement : BoundaryPlacementAt key left right before)
    (step : SplayStep key.val before after) :
    BoundaryPlacementAt key left right after := by
  cases step with
  | zig step =>
      exact after_zig placement step
  | double step =>
      exact after_doubleRotationAt placement step

/--
The two artificial positions remain in the accessed key's child intervals
throughout, and in particular in the final root decomposition of every
complete splay execution.
-/
theorem after_execution
    {n lower upper : ℕ} {key : Fin n}
    {left right : External n}
    {before after : BST lower upper}
    (placement : BoundaryPlacementAt key left right before)
    (execution : SplayExecution key.val before after) :
    BoundaryPlacementAt key left right after := by
  induction execution with
  | done root =>
      exact placement
  | next head tail ih =>
      exact ih (after_splayStep placement head)

end BoundaryPlacementAt

/--
The boundary minima selected from an actual key focus automatically satisfy
`BoundaryPlacementAt`; no caller-supplied placement proof is needed.
-/
theorem boundaryPlacementFromFocus
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n)
    (focus :
      WholeSplayTemporaryBoundaryGeometry.KeyFocus key.val tree) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelectionFrom
          snapshot tree upper_le_n key focus
    BoundaryPlacementAt key selection.left selection.right tree := by
  induction focus with
  | @root lower upper focusedLeft focusedRight =>
      have left_le_n : key.val ≤ n := by
        have bounds := focusedRight.lower_le_upper
        omega
      have leftMin :=
        subtreeOwner_isMin snapshot focusedLeft left_le_n
      have rightMin :=
        subtreeOwner_isMin snapshot focusedRight upper_le_n
      apply BoundaryPlacementAt.root
      · change 2 * lower ≤
          (subtreeOwner snapshot focusedLeft left_le_n).val
        exact leftMin.1
      · change
          (subtreeOwner snapshot focusedLeft left_le_n).val ≤
            2 * key.val
        exact leftMin.2.1
      · change 2 * (key.val + 1) ≤
          (subtreeOwner snapshot focusedRight upper_le_n).val
        exact rightMin.1
      · change
          (subtreeOwner snapshot focusedRight upper_le_n).val ≤
            2 * upper
        exact rightMin.2.1
  | @leftContext lower root upper focusedLeft focus focusedRight ih =>
      have left_le_n : root ≤ n := by
        have bounds := focusedRight.lower_le_upper
        omega
      simpa only [
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelectionFrom,
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.focusedBoundaryMinimumSelectionFrom] using
        BoundaryPlacementAt.leftContext (ih left_le_n) focusedRight
  | @rightContext lower root upper focusedLeft focusedRight focus ih =>
      simpa only [
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelectionFrom,
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.focusedBoundaryMinimumSelectionFrom] using
        BoundaryPlacementAt.rightContext focusedLeft (ih upper_le_n)

/--
Complete-tree specialization: the canonical boundary-minimum selection used
by preprocessing has an automatic exact placement in the pre-splay tree.
-/
theorem canonicalBoundaryPlacement
    {n : ℕ} (snapshot : Snapshot n) (before : BST 0 n)
    (key : Fin n) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        snapshot before key
    BoundaryPlacementAt key selection.left selection.right before := by
  simpa only [
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection] using
    boundaryPlacementFromFocus snapshot before (Nat.le_refl n) key
      (WholeSplayTemporaryBoundaryGeometry.KeyFocus.ofFin before key)

/--
The promoted value owns the complete interval of every intermediate
splay-tree shape under the canonical temporary snapshot.
-/
theorem temporarySnapshot_fullIntervalOwner
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (left right : External n)
    (ordered : left < valuePos key ∧ valuePos key < right)
    (tree : BST 0 n) :
    IntervalOwner
      (temporarySnapshot comparison key comparisonRoot left right ordered)
      tree (Nat.le_refl n) key := by
  unfold IntervalOwner
  simpa only [subtreeLower, subtreeUpper] using
    valuePos_isIntervalMin comparison key comparisonRoot
      left right
      (subtreeLower tree (Nat.le_refl n))
      (subtreeUpper tree (Nat.le_refl n))
      ordered (by
        constructor
        · change 0 ≤ 2 * key.val + 1
          omega
        · change 2 * key.val + 1 ≤ 2 * n
          omega)

/--
Proof-relevant winner/victim maps can be reconstructed non-causally from the
two sharp endpoint cardinality inequalities.

For creations, inject all endpoint identities into `Fin (zigZig + 2)`;
the last two slots are administrative and every remaining slot is a genuine
zig-zig slot.  For removals, the assumed cardinality bound directly embeds
the zig-zag indices into the removed identities.
-/
noncomputable def endpointHitClassificationOfBounds
    {n keyVal : ℕ} {before after : BST 0 n}
    {execution : SplayExecution keyVal before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    {snapshot : Snapshot n}
    (created_le :
      ((bends snapshot after) \ (bends snapshot before)).card ≤
        transcript.zigZig + 2)
    (zigZag_le_removed :
      transcript.zigZag ≤
        ((bends snapshot before) \ (bends snapshot after)).card) :
    EndpointHitClassification transcript snapshot := by
  classical
  let Created :=
    CreatedIdentity (before := before) (after := after) snapshot
  let Removed :=
    RemovedIdentity (before := before) (after := after) snapshot
  let createdCode : Created → Fin (transcript.zigZig + 2) :=
    fun identity =>
      Fin.castLE (by
        simpa only [Created, Fintype.card_coe] using created_le)
        (Fintype.equivFin Created identity)
  have createdCode_injective :
      Function.Injective createdCode := by
    intro first second equal
    apply (Fintype.equivFin Created).injective
    apply Fin.ext
    dsimp only [createdCode] at equal
    simpa using congrArg Fin.val equal
  let administrative : Finset Created :=
    Finset.univ.filter fun identity =>
      transcript.zigZig ≤ (createdCode identity).val
  have administrative_card_le_two :
      administrative.card ≤ 2 := by
    let administrativeCode : ↥administrative → Fin 2 :=
      fun identity =>
        ⟨(createdCode identity.val).val - transcript.zigZig, by
          have upper := (createdCode identity.val).isLt
          omega⟩
    have administrativeCode_injective :
        Function.Injective administrativeCode := by
      intro first second equal
      apply Subtype.ext
      apply createdCode_injective
      apply Fin.ext
      have firstLower :
          transcript.zigZig ≤ (createdCode first.val).val := by
        exact (Finset.mem_filter.mp first.property).2
      have secondLower :
          transcript.zigZig ≤ (createdCode second.val).val := by
        exact (Finset.mem_filter.mp second.property).2
      have values := congrArg Fin.val equal
      dsimp only [administrativeCode] at values
      omega
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective
        administrativeCode administrativeCode_injective
  let zigZigWinner :
      ↥((Finset.univ : Finset Created) \ administrative) →
        Fin transcript.zigZig :=
    fun identity =>
      Fin.castLT (createdCode identity.val) (by
        have outside := (Finset.mem_sdiff.mp identity.property).2
        have notLarge : ¬ transcript.zigZig ≤
            (createdCode identity.val).val := by
          intro large
          apply outside
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, large⟩
        omega)
  have zigZigWinner_injective :
      Function.Injective zigZigWinner := by
    intro first second equal
    apply Subtype.ext
    apply createdCode_injective
    apply Fin.ext
    dsimp only [zigZigWinner] at equal
    simpa using congrArg Fin.val equal
  let zigZagVictim : Fin transcript.zigZag → Removed :=
    fun index =>
      (Fintype.equivFin Removed).symm
        (Fin.castLE (by
          simpa only [Removed, Fintype.card_coe] using
            zigZag_le_removed) index)
  have zigZagVictim_injective :
      Function.Injective zigZagVictim := by
    intro first second equal
    apply Fin.ext
    have encoded :=
      (Fintype.equivFin Removed).symm.injective equal
    simpa using congrArg Fin.val encoded
  exact
    { administrative := administrative
      administrative_card_le_two := administrative_card_le_two
      zigZigWinner := zigZigWinner
      zigZigWinner_injective := zigZigWinner_injective
      zigZagVictim := zigZagVictim
      zigZagVictim_injective := zigZagVictim_injective }

/--
Canonical-selection constructor for the core certificate.

After the preprocessing module has selected the two actual child-subtree
minima, the placement field is now automatic.  The only remaining argument
is the endpoint winner/victim classification itself.
-/
noncomputable def canonicalTemporaryCoreCertificate
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (transcript : SplayExecutionTranscriptWitness execution)
    (endpoint :
      let selection :=
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          (Snapshot.ofTree comparison) before key
      EndpointHitClassification transcript
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    TemporaryCoreCertificate comparison key execution comparisonRoot
      transcript selection.left selection.right selection.ordered := by
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      (Snapshot.ofTree comparison) before key
  exact
    { placement := canonicalBoundaryPlacement
        (Snapshot.ofTree comparison) before key
      endpoint := endpoint }

/--
Public numeric constructor for the canonical temporary core.

All structural premises are discharged automatically: the two boundary
minima, their exact placement, and the finite winner/victim maps.  The
remaining pure-tree residue is exactly the pair of sharp endpoint
cardinality inequalities stated by the manuscript.
-/
noncomputable def canonicalTemporaryCoreCertificateOfBounds
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (transcript : SplayExecutionTranscriptWitness execution)
    (created_le :
      let selection :=
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          (Snapshot.ofTree comparison) before key
      ((bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          after) \
        (bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          before)).card ≤
        transcript.zigZig + 2)
    (zigZag_le_removed :
      let selection :=
        WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          (Snapshot.ofTree comparison) before key
      transcript.zigZag ≤
        ((bends
            (temporarySnapshot comparison key comparisonRoot
              selection.left selection.right selection.ordered)
            before) \
          (bends
            (temporarySnapshot comparison key comparisonRoot
              selection.left selection.right selection.ordered)
            after)).card) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    TemporaryCoreCertificate comparison key execution comparisonRoot
      transcript selection.left selection.right selection.ordered := by
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      (Snapshot.ofTree comparison) before key
  apply canonicalTemporaryCoreCertificate
  exact endpointHitClassificationOfBounds created_le zigZag_le_removed

end Splay.Accounting.WholeSplayTemporaryCoreClassification
