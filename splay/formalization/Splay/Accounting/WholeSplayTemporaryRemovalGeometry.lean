import Splay.Accounting.WholeSplayTemporaryCoreClassification

namespace Splay.Accounting.WholeSplayTemporaryRemovalGeometry

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.ContextualBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCoreClassification
open Splay.Accounting.WholeSplayTemporaryBoundaryGeometry

/--
A final one-level zig cannot increase the number of direction changes still
visible on the search path to the accessed key.  The generalized incoming
direction makes the statement stable under an arbitrary surrounding search
context.
-/
theorem searchTurnCountFrom_after_le_before_of_zig
    {key lower upper : ℕ} {before after : BST lower upper}
    (step : Zig key before after)
    (incoming : Option TernaryBranch) :
    searchTurnCountFrom incoming after key ≤
      searchTurnCountFrom incoming before key := by
  cases step with
  | fromLeft a b c =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      simp [searchTurnCountFrom, LocalBendGeometry.Turns]
  | fromRight a b c =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      simp [searchTurnCountFrom, LocalBendGeometry.Turns]

/--
The number of genuine zig-zags in any proof-relevant complete splay
transcript is bounded by the number of direction changes on its initial
search path.

This is the purely rotation-theoretic half of endpoint persistence.  A
zig-zag consumes at least one residual turn, while zigs and zig-zigs do not
increase the residual turn count.
-/
theorem transcript_zigZag_le_searchTurnCountFrom
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (incoming : Option TernaryBranch) :
    zigZag ≤ searchTurnCountFrom incoming before key := by
  induction transcript generalizing incoming with
  | done root =>
      simp
  | zig step tail transcript ih =>
      exact (ih incoming).trans
        (searchTurnCountFrom_after_le_before_of_zig step incoming)
  | zigZig step orientation tail transcript ih =>
      exact (ih incoming).trans
        (searchTurnCountFrom_after_le_before_of_zigZig
          orientation incoming)
  | zigZag step orientation tail transcript ih =>
      have tailBound := ih incoming
      have consumed :=
        searchTurnCountFrom_after_succ_le_before_of_zigZag
          orientation incoming
      omega

/-- Global-search specialization of the transcript turn bound. -/
theorem transcript_zigZag_le_searchTurnCount
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    zigZag ≤ searchTurnCount before key := by
  simpa [searchTurnCount] using
    transcript_zigZag_le_searchTurnCountFrom transcript none

/--
The actual internal keys at which the initial search path changes direction.

Unlike the numerical `searchTurnCountFrom`, this finite set remembers the
endpoint bend identities to be charged.  Indexed-BST interval bounds make
the identities distinct automatically.
-/
noncomputable def searchTurnKeysFrom
    {n lower upper : ℕ} (incoming : Option TernaryBranch)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : ℕ) : Finset (Fin n) :=
  match tree with
  | .empty _ => ∅
  | .node (root := root) left right =>
      let rootKey : Fin n := ⟨root, by
        have rightBounds := right.lower_le_upper
        omega⟩
      if key = root then
        ∅
      else if key < root then
        let tail :=
          searchTurnKeysFrom (some .left) left (by
            have rightBounds := right.lower_le_upper
            omega) key
        if LocalBendGeometry.Turns incoming .left then
          insert rootKey tail
        else
          tail
      else
        let tail :=
          searchTurnKeysFrom (some .right) right upper_le_n key
        if LocalBendGeometry.Turns incoming .right then
          insert rootKey tail
        else
          tail
termination_by tree.size
decreasing_by
  all_goals simp [_root_.Splay.Tree.BST.size] <;> omega

/-- Global initial-search turn identities. -/
noncomputable def searchTurnKeys
    {n : ℕ} (tree : BST 0 n) (key : ℕ) : Finset (Fin n) :=
  searchTurnKeysFrom none tree (Nat.le_refl n) key

/-- Every recorded turn key belongs to the indexed interval of its tree. -/
theorem mem_searchTurnKeysFrom_bounds
    {n lower upper : ℕ} {incoming : Option TernaryBranch}
    {tree : BST lower upper} {upper_le_n : upper ≤ n}
    {key : ℕ} {turn : Fin n}
    (member :
      turn ∈ searchTurnKeysFrom incoming tree upper_le_n key) :
    lower ≤ turn.val ∧ turn.val < upper := by
  induction tree generalizing incoming key with
  | empty =>
      simp [searchTurnKeysFrom] at member
  | @node lower root upper left right leftIH rightIH =>
      have leftBounds := left.lower_le_upper
      have rightBounds := right.lower_le_upper
      simp only [searchTurnKeysFrom] at member
      split at member
      · simp at member
      · split at member
        · split at member
          · rcases Finset.mem_insert.mp member with atRoot | inTail
            · subst turn
              simp
              omega
            · have bounds := leftIH inTail
              omega
          · have bounds := leftIH member
            omega
        · split at member
          · rcases Finset.mem_insert.mp member with atRoot | inTail
            · subst turn
              simp
              omega
            · have bounds := rightIH inTail
              omega
          · have bounds := rightIH member
            omega

/--
The proof-relevant turn-key set has exactly the numerical search-turn
cardinality.
-/
theorem card_searchTurnKeysFrom
    {n lower upper : ℕ} (incoming : Option TernaryBranch)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : ℕ) :
    (searchTurnKeysFrom incoming tree upper_le_n key).card =
      searchTurnCountFrom incoming tree key := by
  induction tree generalizing incoming key with
  | empty =>
      simp [searchTurnKeysFrom, searchTurnCountFrom]
  | @node lower root upper left right leftIH rightIH =>
      have leftBounds := left.lower_le_upper
      have rightBounds := right.lower_le_upper
      simp only [searchTurnKeysFrom, searchTurnCountFrom]
      split
      · simp
      · split
        · split
          · have notMember :
                (⟨root, by omega⟩ : Fin n) ∉
                  searchTurnKeysFrom (some .left) left (by omega) key := by
              intro member
              have bounds :=
                mem_searchTurnKeysFrom_bounds member
              have impossible := bounds.2
              change root < root at impossible
              omega
            rw [Finset.card_insert_of_notMem notMember,
              leftIH (some .left) (by omega) key]
            omega
          · simpa using leftIH (some .left) (by omega) key
        · split
          · have notMember :
                (⟨root, by omega⟩ : Fin n) ∉
                  searchTurnKeysFrom (some .right) right upper_le_n key := by
              intro member
              have bounds :=
                mem_searchTurnKeysFrom_bounds member
              have impossible := bounds.1
              change root + 1 ≤ root at impossible
              omega
            rw [Finset.card_insert_of_notMem notMember,
              rightIH (some .right) upper_le_n key]
            omega
          · simpa using rightIH (some .right) upper_le_n key

/-- Global cardinality form. -/
theorem card_searchTurnKeys
    {n : ℕ} (tree : BST 0 n) (key : ℕ) :
    (searchTurnKeys tree key).card = searchTurnCount tree key := by
  simpa [searchTurnKeys, searchTurnCount] using
    card_searchTurnKeysFrom none tree (Nat.le_refl n) key

/--
Every search-direction turn is already a genuine bend in the initial fixed
snapshot whenever the accessed value owns the complete tree interval.

This discharges the initial-membership half of persistence independently of
the later splay rotations.
-/
theorem searchTurnKeysFrom_subset_bendsFrom_of_intervalOwner
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) (incoming : Option TernaryBranch)
    (owner : IntervalOwner snapshot tree upper_le_n key) :
    searchTurnKeysFrom incoming tree upper_le_n key.val ⊆
      bendsFrom snapshot tree upper_le_n incoming := by
  induction tree generalizing incoming with
  | empty =>
      simp [searchTurnKeysFrom]
  | @node lower root upper left right leftIH rightIH =>
      have leftBounds := left.lower_le_upper
      have rightBounds := right.lower_le_upper
      have keyBounds :
          lower ≤ key.val ∧ key.val < upper := by
        have owned := owner
        unfold IntervalOwner IsIntervalMin at owned
        simp only [subtreeLower, subtreeUpper, valuePos,
          Fin.mk_le_mk] at owned
        omega
      simp only [searchTurnKeysFrom]
      split
      · simp
      · split
        · have heavy :
              AtNode.heavyBranch snapshot
                ({
                  lower := lower
                  root := root
                  upper := upper
                  left := left
                  right := right
                  upper_le_n := upper_le_n
                } : AtNode n) = .left := by
            simpa only using
              owner.heavyBranch_eq left right upper_le_n key .left
                (by
                  simp [TernaryBranch.Contains, valuePos]
                  omega)
          have innerOwner :
              IntervalOwner snapshot left (by omega) key := by
            apply owner.restrict (by omega)
            · exact Nat.le_refl lower
            · omega
            · exact keyBounds.1
            · omega
          split
          · intro turn member
            rcases Finset.mem_insert.mp member with atRoot | inTail
            · subst turn
              simp [bendsFrom, bendAt, childIncoming, *]
            · have inLeft :=
                leftIH (by omega) (some .left) innerOwner inTail
              simp [bendsFrom, heavy, childIncoming, inLeft]
          · intro turn member
            have inLeft :=
              leftIH (by omega) (some .left) innerOwner member
            simp [bendsFrom, heavy, childIncoming, inLeft]
        · have root_lt_key : root < key.val := by
            omega
          have heavy :
              AtNode.heavyBranch snapshot
                ({
                  lower := lower
                  root := root
                  upper := upper
                  left := left
                  right := right
                  upper_le_n := upper_le_n
                } : AtNode n) = .right := by
            simpa only using
              owner.heavyBranch_eq left right upper_le_n key .right
                (by
                  simp [TernaryBranch.Contains, valuePos]
                  omega)
          have innerOwner :
              IntervalOwner snapshot right upper_le_n key := by
            apply owner.restrict upper_le_n
            · omega
            · exact Nat.le_refl upper
            · omega
            · exact keyBounds.2
          split
          · intro turn member
            rcases Finset.mem_insert.mp member with atRoot | inTail
            · subst turn
              simp [bendsFrom, bendAt, childIncoming, *]
            · have inRight :=
                rightIH upper_le_n (some .right) innerOwner inTail
              simp [bendsFrom, heavy, childIncoming, inRight]
          · intro turn member
            have inRight :=
              rightIH upper_le_n (some .right) innerOwner member
            simp [bendsFrom, heavy, childIncoming, inRight]

/-- Complete-tree specialization of initial turn membership. -/
theorem searchTurnKeys_subset_bends_of_intervalOwner
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key : Fin n)
    (owner :
      IntervalOwner snapshot tree (Nat.le_refl n) key) :
    searchTurnKeys tree key.val ⊆ bends snapshot tree := by
  simpa [searchTurnKeys, bends] using
    searchTurnKeysFrom_subset_bendsFrom_of_intervalOwner
      snapshot tree (Nat.le_refl n) key none owner

/--
The remaining monotone-spine persistence invariant in proof-relevant form.

Its domain is not the chronological zig-zag list: it is the fixed set of
direction turns on the *initial* search path.  The invariant says that those
turns inject into actual bend identities present initially and absent at the
endpoint.  Thus it cannot be satisfied by repeatedly charging one
remove/re-create occurrence.
-/
structure SearchTurnRemovalEmbedding
    {n key : ℕ} (snapshot : Snapshot n)
    (before after : BST 0 n) : Type where
  victim :
    Fin (searchTurnCount before key) →
      RemovedIdentity (before := before) (after := after) snapshot
  victim_injective :
    Function.Injective victim

namespace SearchTurnRemovalEmbedding

/--
Construct fixed-turn persistence from only final-spine nonmembership.

Initial membership is automatic from `IntervalOwner`, and distinctness is
automatic because `searchTurnKeys` is a finite set of indexed BST keys.  The
caller therefore supplies no injection and no initial bend facts.
-/
noncomputable def ofFinalNonmembership
    {n : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n} (key : Fin n)
    (owner :
      IntervalOwner snapshot before (Nat.le_refl n) key)
    (finalAbsent :
      ∀ turn ∈ searchTurnKeys before key.val,
        turn ∉ bends snapshot after) :
    SearchTurnRemovalEmbedding
      (key := key.val) snapshot before after := by
  classical
  let TurnKeys : Type := ↥(searchTurnKeys before key.val)
  let turnAt :
      Fin (searchTurnCount before key.val) → TurnKeys :=
    fun index =>
      (Fintype.equivFin TurnKeys).symm
        (Fin.cast
          (by
            simpa only [TurnKeys, Fintype.card_coe] using
              (card_searchTurnKeys before key.val).symm)
          index)
  have turnAt_injective : Function.Injective turnAt := by
    intro first second equal
    apply Fin.ext
    have encoded :=
      (Fintype.equivFin TurnKeys).symm.injective equal
    simpa [turnAt] using congrArg Fin.val encoded
  let victim :
      Fin (searchTurnCount before key.val) →
        RemovedIdentity (before := before) (after := after) snapshot :=
    fun index =>
      ⟨(turnAt index).val, Finset.mem_sdiff.mpr
        ⟨searchTurnKeys_subset_bends_of_intervalOwner
            snapshot before key owner (turnAt index).property,
          finalAbsent (turnAt index).val (turnAt index).property⟩⟩
  have victim_injective : Function.Injective victim := by
    intro first second equal
    apply turnAt_injective
    apply Subtype.ext
    simpa [victim] using congrArg Subtype.val equal
  exact
    { victim := victim
      victim_injective := victim_injective }

/-- A search-turn removal embedding gives the corresponding cardinality bound. -/
theorem searchTurnCount_le_removed
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    (persistence :
      SearchTurnRemovalEmbedding (key := key) snapshot before after) :
    searchTurnCount before key ≤
      ((bends snapshot before) \ (bends snapshot after)).card := by
  simpa using
    Fintype.card_le_of_injective
      persistence.victim persistence.victim_injective

/--
Rotation consumption plus fixed-spine persistence proves the sharp endpoint
zig-zag removal inequality.
-/
theorem zigZag_le_removed
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    (persistence :
      SearchTurnRemovalEmbedding (key := key) snapshot before after) :
    transcript.zigZag ≤
      ((bends snapshot before) \ (bends snapshot after)).card := by
  exact
    (transcript_zigZag_le_searchTurnCount transcript.transcript).trans
      persistence.searchTurnCount_le_removed

end SearchTurnRemovalEmbedding

/--
Canonical temporary-snapshot endpoint removal from the sole remaining
monotone-spine persistence certificate.

Boundary minima and their exact child-interval placement are fixed
definitionally here.  The supplied certificate concerns only persistence of
the original search turns through the remainder of the complete splay.
-/
theorem canonical_zigZag_le_removed_of_searchTurnPersistence
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (persistence :
      let selection :=
        KeyFocus.boundaryMinimumSelection
          (Snapshot.ofTree comparison) before key
      SearchTurnRemovalEmbedding
        (key := key.val)
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)
        before after) :
    let transcript := splayExecutionTranscriptWitness execution
    let selection :=
      KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    transcript.zigZag ≤
      ((bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          before) \
        (bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          after)).card := by
  let transcript := splayExecutionTranscriptWitness execution
  let selection :=
    KeyFocus.boundaryMinimumSelection
      (Snapshot.ofTree comparison) before key
  exact persistence.zigZag_le_removed

/--
Canonical temporary-snapshot removal bound from only the final monotone-spine
fact.

All other ingredients are automatic:

* zig-zag count is bounded by the initial search-turn count;
* `temporarySnapshot_fullIntervalOwner` makes every initial turn a bend;
* the turn keys are distinct by indexed-BST intervals;
* the finite injection into endpoint removals is constructed internally.

Thus the sole premise below says exactly that no original search turn is a
bend in the final splayed tree.
-/
theorem canonical_zigZag_le_removed_of_finalSearchTurnsAbsent
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (finalAbsent :
      let selection :=
        KeyFocus.boundaryMinimumSelection
          (Snapshot.ofTree comparison) before key
      ∀ turn ∈ searchTurnKeys before key.val,
        turn ∉
          bends
            (temporarySnapshot comparison key comparisonRoot
              selection.left selection.right selection.ordered)
            after) :
    let transcript := splayExecutionTranscriptWitness execution
    let selection :=
      KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    transcript.zigZag ≤
      ((bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          before) \
        (bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          after)).card := by
  let transcript := splayExecutionTranscriptWitness execution
  let selection :=
    KeyFocus.boundaryMinimumSelection
      (Snapshot.ofTree comparison) before key
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      selection.left selection.right selection.ordered
  have owner :
      IntervalOwner snapshot before (Nat.le_refl n) key := by
    exact
      temporarySnapshot_fullIntervalOwner
        comparison key comparisonRoot
        selection.left selection.right selection.ordered before
  let persistence :
      SearchTurnRemovalEmbedding
        (key := key.val) snapshot before after :=
    SearchTurnRemovalEmbedding.ofFinalNonmembership
      key owner finalAbsent
  exact persistence.zigZag_le_removed

end Splay.Accounting.WholeSplayTemporaryRemovalGeometry
