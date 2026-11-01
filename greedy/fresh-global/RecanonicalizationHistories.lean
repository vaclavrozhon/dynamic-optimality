import ComparatorHistories

/-! The actual at-most-two refinement rotations preserve chronological
histories and advance a concrete paid-entry clock. An arbitrary padding
prefix and four paid timestamp slots are reserved per refinement rotation,
matching the conservative actual port-support constructor; unused slots
create no entries or births. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.PortCases

/-- Reserve an arbitrary initial label-update prefix before paid entries.
This theorem only closes entry chronology; the label timeline supplies
the numerical snapshot-equality proof independently. -/
theorem administerActualComparator_padded_chronology {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) (tree : BST 0 n)
    (families ids : NameSupply n) (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (clock padding : ℕ) (states : States n) (histories : Histories states) (beforeTime : BeforeTime clock states)
    (time : ∀ stage record owner, (makeEntry stage record owner).joined=clock+padding+stage) :
    Histories (administerActualComparator rotation tree families ids bulkFresh paidNames makeEntry states).1 ∧
      BeforeTime (clock+padding+3) (administerActualComparator rotation tree families ids bulkFresh paidNames makeEntry states).1 := by
  have padded : BeforeTime (clock+padding) states := by
    intro owner side entry member
    have earlier := beforeTime owner side entry member
    omega
  exact administerActualComparator_chronology rotation tree families ids bulkFresh paidNames makeEntry
    (clock+padding) states histories padded time

theorem reparentSelected_chronology {n : ℕ} (comparator afterTree : BST 0 n)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry) (ports : List (External n))
    (clock : ℕ) (states : States n) (good : Chronology clock states)
    (time : ∀ stage record owner, (makeEntry stage record owner).joined=clock+stage) :
    Chronology (clock+ports.length)
      (reparentSelected comparator afterTree families ids paidNames makeEntry ports states).1 := by
  have detached := detachPorts_chronology comparator families ids (ports.map Fin.val) 0 clock states good
  have restored := restorePorts_chronology (Snapshot.ofTree comparator) afterTree paidNames makeEntry
    ports clock 0 _ (by simpa using detached) time
  simpa only [reparentSelected,Nat.add_zero] using restored

theorem administerRefinementRotation_chronology {n depth : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (clock : ℕ) (states : States n) (good : Chronology clock states)
    (time : ∀ stage record owner, (makeEntry stage record owner).joined=clock+stage) :
    Chronology (clock+4)
      (administerRefinementRotation comparator rotation families ids paidNames makeEntry states).1 := by
  have result := reparentSelected_chronology comparator afterTree families ids paidNames makeEntry
    (refinementRotationPorts (Snapshot.ofTree comparator) rotation) clock states good time
  have bound := (refinementRotationPorts_spec (Snapshot.ofTree comparator) rotation).2.1
  exact result.mono (by omega)

theorem administerRefinementRotation_padded_chronology {n depth : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (clock padding : ℕ) (states : States n) (histories : Histories states) (beforeTime : BeforeTime clock states)
    (time : ∀ stage record owner, (makeEntry stage record owner).joined=clock+padding+stage) :
    Histories (administerRefinementRotation comparator rotation families ids paidNames makeEntry states).1 ∧
      BeforeTime (clock+padding+4)
        (administerRefinementRotation comparator rotation families ids paidNames makeEntry states).1 := by
  have good := (chronology_iff clock states).mpr ⟨histories,beforeTime⟩
  exact (chronology_iff ..).mp (administerRefinementRotation_chronology comparator rotation families ids paidNames
    makeEntry (clock+padding) states (good.mono (by omega)) time)

/-- Build the same literal administration sequence and its birth journal,
while retaining the chronology of every intermediate state. -/
theorem refinementSteps_administration_chronology {n steps : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotations : RotationSteps steps beforeTree afterTree)
    (families ids : ℕ → NameSupply n) (paidNames : ℕ → ℕ → PaidNames)
    (makeEntry : ℕ → ℕ → External n → External n → Entry)
    (key : ∀ stage paidStage record owner, (makeEntry stage paidStage record owner).key=record.val)
    (clock padding : ℕ)
    (time : ∀ stage paidStage record owner,
      (makeEntry stage paidStage record owner).joined=clock+(padding+4)*stage+padding+paidStage)
    (stage : ℕ) (states : States n) (ready : Ready comparator beforeTree states)
    (good : Chronology (clock+(padding+4)*stage) states) :
    ∃ finalStates births journal, Ready comparator afterTree finalStates ∧
      Chronology (clock+(padding+4)*(stage+steps)) finalStates ∧ births≤20*steps ∧
      journal.length=births ∧ SupportsIds states finalStates journal := by
  induction steps generalizing beforeTree states stage with
  | zero =>
    cases rotations
    exact ⟨states,0,[],ready,by simpa using good,by simp,rfl,supportsIds_refl states⟩
  | succ steps ih =>
    cases rotations with
    | @cons _ depth _ _ before middle after first rest =>
      let head := administerRefinementRotation comparator first (families stage) (ids stage)
        (paidNames stage) (makeEntry stage) states
      have headSpec := administerRefinementRotation_ready comparator first (families stage) (ids stage)
        (paidNames stage) (makeEntry stage) (key stage) states ready
      have headChronology := administerRefinementRotation_chronology comparator first (families stage) (ids stage)
        (paidNames stage) (makeEntry stage) (clock+(padding+4)*stage+padding) states
        (good.mono (by omega)) (time stage)
      have nextChronology : Chronology (clock+(padding+4)*(stage+1)) head.1 := by
        simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using headChronology
      let headJournal := reparentSelectedIds comparator middle (families stage) (ids stage) (paidNames stage)
        (makeEntry stage) (refinementRotationPorts (Snapshot.ofTree comparator) first) states
      have headLength : headJournal.length=head.2 := reparentSelectedIds_length ..
      have headSupport : SupportsIds states head.1 headJournal := reparentSelected_id_support comparator middle
        (families stage) (ids stage) (paidNames stage) (makeEntry stage)
        (refinementRotationPorts (Snapshot.ofTree comparator) first) states
      obtain ⟨finalStates,tailBirths,tailJournal,finalReady,finalChronology,tailBound,tailLength,tailSupport⟩ :=
        ih rest (stage+1) head.1 headSpec.1 nextChronology
      refine ⟨finalStates,head.2+tailBirths,headJournal++tailJournal,finalReady,?_,?_,?_,
        supportsIds_trans headSupport tailSupport⟩
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finalChronology
      · have headBound : head.2≤20 := headSpec.2
        omega
      · simp only [List.length_append,headLength,tailLength]

/-- Recanonicalization after an actual comparator rotation constructs its
at-most-two refinement rotations and returns the complete Ready/history
invariant. Neither the rotation count nor the chronological state is a
caller-supplied aggregate certificate. -/
theorem recanonicalization_administration_chronology {height : ℕ → ℤ} {n depth : ℕ}
    {before after : BST 0 n} (rotation : RotationAt depth before after)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : GreedyMerge.Surface.Owners height before.depth oldOwner n)
    (newOwners : GreedyMerge.Surface.Owners height after.depth newOwner n)
    (oldTree newTree : BST 0 n)
    (oldCanonical : GreedyMerge.Surface.Canonical height (fun key => before.depth (oldOwner key)) oldTree)
    (newCanonical : GreedyMerge.Surface.Canonical height (fun key => after.depth (newOwner key)) newTree)
    (families ids : ℕ → NameSupply n) (paidNames : ℕ → ℕ → PaidNames)
    (makeEntry : ℕ → ℕ → External n → External n → Entry)
    (key : ∀ stage paidStage record owner, (makeEntry stage paidStage record owner).key=record.val)
    (clock padding : ℕ)
    (time : ∀ stage paidStage record owner,
      (makeEntry stage paidStage record owner).joined=clock+(padding+4)*stage+padding+paidStage)
    (states : States n) (ready : Ready after oldTree states)
    (histories : Histories states) (beforeTime : BeforeTime clock states) :
    ∃ finalStates births journal, Ready after newTree finalStates ∧
      Histories finalStates ∧ BeforeTime (clock+2*(padding+4)) finalStates ∧ births≤40 ∧
      journal.length=births ∧ SupportsIds states finalStates journal := by
  obtain ⟨steps,bound,rotations⟩ := GreedyMerge.CanonicalBridge.actual_canonical_rotationAt rotation oldOwner newOwner
    oldOwners newOwners oldTree newTree oldCanonical newCanonical
  have good : Chronology (clock+(padding+4)*0) states := by
    simpa only [Nat.mul_zero,Nat.add_zero] using (chronology_iff clock states).mpr ⟨histories,beforeTime⟩
  obtain ⟨finalStates,births,journal,finalReady,finalChronology,budget,length,support⟩ :=
    refinementSteps_administration_chronology after rotations families ids paidNames makeEntry key clock padding time 0 states ready good
  have clockBound : clock+(padding+4)*(0+steps) ≤ clock+2*(padding+4) := by
    have twice := Nat.mul_le_mul_left (padding+4) bound
    simpa only [Nat.zero_add,Nat.mul_comm] using Nat.add_le_add_left twice clock
  have finalGood := (chronology_iff (clock+2*(padding+4)) finalStates).mp (finalChronology.mono clockBound)
  exact ⟨finalStates,births,journal,finalReady,finalGood.1,finalGood.2,by omega,length,support⟩

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.administerRefinementRotation_chronology
#print axioms GreedyMerge.ActualLinks.administerActualComparator_padded_chronology
#print axioms GreedyMerge.ActualLinks.administerRefinementRotation_padded_chronology
#print axioms GreedyMerge.ActualLinks.refinementSteps_administration_chronology
#print axioms GreedyMerge.ActualLinks.recanonicalization_administration_chronology
