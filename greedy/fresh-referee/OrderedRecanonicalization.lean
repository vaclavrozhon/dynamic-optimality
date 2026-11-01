import OrderedUniversalComparator
import CanonicalAdministration

/-!
Finite composition of actual fixed-rank refinement rotations. The resulting
state, actual logical birth journal, and support relation are constructed
by induction over the certified rotation sequence. At most two rotations
therefore cost at most forty births in this conservative formal protocol.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open GreedyMerge.PortCases
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

theorem administerRefinementRotation_ready {n depth : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key=record.val)
    (states : HeapSides n) (ready : Ready comparator beforeTree states) :
    Ready comparator afterTree
      (administerRefinementRotation comparator rotation families ids paidNames makeEntry states).1 ∧
    (administerRefinementRotation comparator rotation families ids paidNames makeEntry states).2 ≤ 20 := by
  obtain ⟨valid,sound,complete,persistent,budget⟩ := administerRefinementRotation_spec comparator rotation families ids
    paidNames makeEntry key states ready.valid ready.sound ready.complete ready.persistent
  exact ⟨⟨valid,sound,complete,persistent,
    administerRefinementRotation_bases comparator rotation families ids paidNames makeEntry key states
      ready.valid ready.sound ready.bases⟩,budget⟩

theorem refinementSteps_administration {n steps : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotations : RotationSteps steps beforeTree afterTree)
    (families ids : ℕ → NameSupply n) (paidNames : ℕ → ℕ → PaidNames)
    (makeEntry : ℕ → ℕ → External n → External n → Entry)
    (key : ∀ stage paidStage record owner, (makeEntry stage paidStage record owner).key=record.val)
    (stage : ℕ) (states : HeapSides n) (ready : Ready comparator beforeTree states) :
    ∃ finalStates births journal, Ready comparator afterTree finalStates ∧
      births ≤ 20*steps ∧ journal.length=births ∧ SupportsIds states finalStates journal := by
  induction steps generalizing beforeTree states stage with
  | zero =>
      cases rotations
      exact ⟨states,0,[],ready,by simp,rfl,supportsIds_refl states⟩
  | succ steps ih =>
    cases rotations with
    | @cons _ depth _ _ before middle after first rest =>
        let head := administerRefinementRotation comparator first (families stage) (ids stage)
          (paidNames stage) (makeEntry stage) states
        have headSpec := administerRefinementRotation_ready comparator first (families stage) (ids stage)
          (paidNames stage) (makeEntry stage) (key stage) states ready
        let headJournal := reparentSelectedIds comparator middle (families stage) (ids stage) (paidNames stage)
          (makeEntry stage) (refinementRotationPorts (Snapshot.ofTree comparator) first) states
        have headLength : headJournal.length=head.2 := reparentSelectedIds_length ..
        have headSupport : SupportsIds states head.1 headJournal := reparentSelected_id_support comparator middle (families stage) (ids stage) (paidNames stage) (makeEntry stage) (refinementRotationPorts (Snapshot.ofTree comparator) first) states
        obtain ⟨finalStates,tailBirths,tailJournal,finalReady,tailBound,tailLength,tailSupport⟩ :=
          ih rest (stage+1) head.1 headSpec.1
        refine ⟨finalStates,head.2+tailBirths,headJournal++tailJournal,finalReady,?_,?_,
          supportsIds_trans headSupport tailSupport⟩
        · have headBound : head.2≤20 := headSpec.2
          omega
        · simp only [List.length_append,headLength,tailLength]

/-- Actual recanonicalization supplies the at-most-two rotation sequence;
no aggregate block-birth allowance is passed to the constructor. -/
theorem recanonicalization_administration {height : ℕ → ℤ} {n depth : ℕ}
    {before after : BST 0 n} (rotation : RotationAt depth before after)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : Surface.Owners height before.depth oldOwner n)
    (newOwners : Surface.Owners height after.depth newOwner n)
    (oldTree newTree : BST 0 n)
    (oldCanonical : Surface.Canonical height (fun key => before.depth (oldOwner key)) oldTree)
    (newCanonical : Surface.Canonical height (fun key => after.depth (newOwner key)) newTree)
    (families ids : ℕ → NameSupply n) (paidNames : ℕ → ℕ → PaidNames)
    (makeEntry : ℕ → ℕ → External n → External n → Entry)
    (key : ∀ stage paidStage record owner, (makeEntry stage paidStage record owner).key=record.val)
    (states : HeapSides n) (ready : Ready after oldTree states) :
    ∃ finalStates births journal, Ready after newTree finalStates ∧ births≤40 ∧
      journal.length=births ∧ SupportsIds states finalStates journal := by
  obtain ⟨steps,bound,rotations⟩ := CanonicalBridge.actual_canonical_rotationAt rotation oldOwner newOwner
    oldOwners newOwners oldTree newTree oldCanonical newCanonical
  obtain ⟨finalStates,births,journal,finalReady,budget,length,support⟩ :=
    refinementSteps_administration after rotations families ids paidNames makeEntry key 0 states ready
  exact ⟨finalStates,births,journal,finalReady,by omega,length,support⟩

#print axioms administerRefinementRotation_ready
#print axioms refinementSteps_administration
#print axioms recanonicalization_administration

end GreedyMerge.OrderedBlocks
