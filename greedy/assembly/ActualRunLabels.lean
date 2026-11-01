import ActualLinkLabels
import ActualSourceDeletion

/-!
Execution of the parent map and numerical labels together with the
literal block-state link run. Live roots retain their source parent;
therefore every departing loser has its actual source membership. The
proof derives soundness, completeness and the exact folded bucket update
from the executed schedule and already established spatial prefix order.
-/
namespace GreedyMerge.ActualLinks

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open OrderedBlocks Primitives
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule

def runParents {n : ℕ} (parent : Parents n) (events : List (External n × External n)) : Parents n :=
  events.foldl (fun current event => linkParents current event.1 event.2) parent

@[simp] theorem runParents_append {n : ℕ} (parent : Parents n)
    (first second : List (External n × External n)) :
    runParents parent (first++second)=runParents (runParents parent first) second :=
  List.foldl_append


theorem runParents_provenance {n : ℕ} (parent : Parents n)
    (events : List (External n × External n)) (record owner : External n)
    (present : runParents parent events record=some owner) :
    parent record=some owner ∨ ∃ event∈events, event.2=record ∧ event.1=owner := by
  induction events generalizing parent with
  | nil => exact Or.inl present
  | cons event rest ih =>
      rcases ih (linkParents parent event.1 event.2) present with old | arrived
      · by_cases same : record=event.2
        · subst record
          have winner : event.1=owner := Option.some.inj (by simpa using old)
          exact Or.inr ⟨event,by simp,rfl,winner⟩
        · exact Or.inl (by simpa [linkParents,same] using old)
      · obtain ⟨e,member,loser,winner⟩ := arrived
        exact Or.inr ⟨e,List.mem_cons_of_mem _ member,loser,winner⟩

theorem runParents_none {n : ℕ} (parent : Parents n)
    (events : List (External n × External n)) (record : External n)
    (missing : runParents parent events record=none) : parent record=none := by
  induction events generalizing parent with
  | nil => exact missing
  | cons event rest ih =>
      have old := ih (linkParents parent event.1 event.2) missing
      by_cases same : record=event.2
      · simp [linkParents,same] at old
      · simpa [linkParents,same] using old

theorem runParents_source_iff {n : ℕ} (parent : Parents n)
    (events : List (External n × External n)) (source record : External n)
    (neverWins : ∀ event∈events, event.1≠source) :
    runParents parent events record=some source ↔
      parent record=some source ∧ record∉events.map Prod.snd := by
  induction events generalizing parent with
  | nil => simp [runParents]
  | cons event rest ih =>
      change runParents (linkParents parent event.1 event.2) rest record=some source ↔ _
      rw [ih _ (fun e he => neverWins e (List.mem_cons_of_mem _ he))]
      by_cases same : record=event.2
      · simp [linkParents,same,neverWins event (by simp)]
      · simp [linkParents,same]

theorem runParents_source_survivor {n : ℕ} (parent : Parents n)
    (events : List (External n × External n)) (source record : External n)
    (rank : ℕ → ℕ) (roots finalRoots : List ℕ)
    (links : Run rank (events.map eventKeys) roots finalRoots) (unique : roots.Nodup)
    (initial : parent record=some source ↔ record.val∈roots)
    (neverWins : ∀ event∈events, event.1≠source) :
    runParents parent events record=some source ↔ record.val∈finalRoots := by
  rw [runParents_source_iff parent events source record neverWins,initial]
  have loserMem : record∈events.map Prod.snd ↔ record.val∈(events.map eventKeys).map Prod.snd := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨event,member,equal⟩
      exact ⟨eventKeys event,⟨event,member,rfl⟩,congrArg Fin.val equal⟩
    · rintro ⟨pair,⟨event,member,rfl⟩,equal⟩
      exact ⟨event,member,Fin.ext equal⟩
  rw [loserMem]
  exact (HistoryProcess.run_survivor_iff links unique record.val).symm

/-- The prefix-order input is structural: ActualLinkRuns.runLinks_ordered
constructs it for each actual schedule prefix. The numerical equality and
intermediate parent soundness are conclusions, not prefix hypotheses. -/
theorem runLinks_sound_complete_labels {n : ℕ}
    (parent : Parents n) (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (reader : ℕ → States n → ℕ → ℤ) (time : ℕ) (states : States n)
    (events : List (External n × External n)) (roots finalRoots : List ℕ)
    (links : Run rank (events.map eventKeys) roots finalRoots)
    (uniqueRoots : roots.Nodup)
    (rootParent : ∀ record : External n, record.val∈roots → parent record=some source)
    (notSource : ∀ record∈roots, record≠source.val)
    (sound : SoundFor parent states) (complete : CompleteFor parent states)
    (persistent : Persistent states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[])
    (sideCorrect : ∀ event∈events, sourceSide event=decide (event.2.val<source.val))
    (orderedPrefixes : ∀ first second, events=first++second →
      Ordered (runLinks source sourceSide reader time states first)) :
    SoundFor (runParents parent events) (runLinks source sourceSide reader time states events) ∧
    CompleteFor (runParents parent events) (runLinks source sourceSide reader time states events) ∧
    StateLabels.label rank K (runLinks source sourceSide reader time states events) =
      GreedyForest.Phase.runLabels rank (StateLabels.label rank K states) (events.map eventKeys) := by
  induction events generalizing parent states time roots with
  | nil => exact ⟨sound,complete,rfl⟩
  | cons event rest ih =>
      change Run rank (eventKeys event :: rest.map eventKeys) roots finalRoots at links
      cases links with
      | @cons _ _ _ middle _ firstLink restLinks =>
          have ordered : Ordered states := by
            simpa only [runLinks] using orderedPrefixes [] (event::rest) rfl
          have winnerNe : source≠event.1 := by
            intro same
            exact notSource event.1.val firstLink.members.1 (congrArg Fin.val same.symm)
          obtain ⟨oldSide,oldEntry,oldMember,oldKey⟩ :=
            complete event.2 source (rootParent event.2 firstLink.members.2)
          have oldSideEq : oldSide=sourceSide event := by
            rw [sideCorrect event (by simp)]
            have onCorrectSide := (ordered source oldSide).2.1 oldEntry oldMember
            unfold onSide at onCorrectSide
            rw [oldKey] at onCorrectSide
            cases oldSide with
            | false =>
                have less : source.val<event.2.val := onCorrectSide
                have notLess : ¬event.2.val<source.val := by omega
                simp only [notLess,decide_false]
            | true =>
                have less : event.2.val<source.val := onCorrectSide
                simp only [less,decide_true]
          rw [oldSideEq] at oldMember
          let fresh := arrivalEntry (reader time states) event.1 event.2 time
          let next := linkState states source event.1 event.2 (sourceSide event) (targetSide event) fresh
          have nextSound : SoundFor (linkParents parent event.1 event.2) next :=
            linkState_sound parent states source event.1 event.2 (sourceSide event) (targetSide event)
              fresh sound ordered persistent winnerNe (emptySource _) oldEntry oldMember oldKey rfl
          have nextComplete : CompleteFor (linkParents parent event.1 event.2) next :=
            linkState_complete parent states source event.1 event.2 (sourceSide event) (targetSide event)
              fresh complete persistent (emptySource _) rfl
          have nextPersistent : Persistent next := linkState_persistent _ _ _ _ _ _ _ persistent
          have nextEmpty : ∀ side, growerEntries (next source side).grower=[] := by
            intro side
            dsimp only [next,linkState]
            simp only [winnerNe,false_and,↓reduceIte]
            split_ifs <;> exact emptySource side
          have nextRootParent : ∀ record : External n, record.val∈middle →
              linkParents parent event.1 event.2 record=some source := by
            intro record member
            have different : record≠event.2 := by
              intro same
              exact firstLink.loser_absent uniqueRoots (by simpa only [same,eventKeys] using member)
            rw [linkParents_other _ _ _ _ different]
            exact rootParent record (firstLink.sublist.subset member)
          have nextOrder : Ordered next := by
            simpa only [runLinks] using orderedPrefixes [event] rest rfl
          have oneLabel := StateLabels.linkState_label_of_next_sound
            (linkParents parent event.1 event.2) rank K states source event.1 event.2
            (sourceSide event) (targetSide event) fresh (persistent _ _) (emptySource _) rfl nextOrder nextSound
          have tail := ih (linkParents parent event.1 event.2) (time+1) next middle restLinks
            (uniqueRoots.sublist firstLink.sublist) nextRootParent
            (fun record member => notSource record (firstLink.sublist.subset member))
            nextSound nextComplete nextPersistent nextEmpty
            (fun e he => sideCorrect e (List.mem_cons_of_mem _ he))
            (by
              intro before after split
              have eq : event::rest=(event::before)++after := by simp [split]
              simpa only [runLinks] using orderedPrefixes (event::before) after eq)
          refine ⟨tail.1,tail.2.1,?_⟩
          change StateLabels.label rank K (runLinks source sourceSide reader (time+1) next rest) = _
          rw [tail.2.2]
          change GreedyForest.Phase.runLabels rank (StateLabels.label rank K next) (rest.map eventKeys) =
            GreedyForest.Phase.runLabels rank
              (GreedyForest.Phase.linkLabels rank (StateLabels.label rank K states) (eventKeys event))
              (rest.map eventKeys)
          rw [oneLabel]
          rfl

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.runLinks_sound_complete_labels

#print axioms GreedyMerge.ActualLinks.runParents_provenance
#print axioms GreedyMerge.ActualLinks.runParents_none
#print axioms GreedyMerge.ActualLinks.runParents_source_survivor
