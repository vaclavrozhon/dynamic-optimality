import ActualAccessRun
import OrderedUniversalComparator
import TaggedTransfer

/-! Close the access interface over concrete Ready states. The two root
conversions are executed at the actual owner rank, preserve every entry
and label, and create at most two replacement growing instances. Literal
link updates preserve all frozen absolute-base bounds. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.PathPlateau
open GreedyMerge.BlockCoverage (Complete Sound)

abbrev AllBases {n : ℕ} (rank : ℕ → ℕ) (states : States n) : Prop :=
  ∀ owner side, BasesValid rank owner.val (states owner side)

def convertRoot {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (families ids : Bool → ℕ) (states : States n) : States n :=
  fun owner side => if owner=source then
    convert owner.val (families side) (ids side) (rank owner.val) (states owner side)
  else states owner side

def rootConversionBirths {n : ℕ} (source : External n) (states : States n) : ℕ :=
  conversionBirths (states source false)+conversionBirths (states source true)

theorem conversionBirths_le_one (state : SideState) : conversionBirths state ≤ 1 := by
  cases hg : state.grower with
  | none => simp [conversionBirths,hg]
  | some grower =>
      by_cases empty : grower.members=[] <;> simp [conversionBirths,hg,empty]

theorem rootConversionBirths_le_two {n : ℕ} (source : External n) (states : States n) :
    rootConversionBirths source states ≤ 2 := by
  have left := conversionBirths_le_one (states source true)
  have right := conversionBirths_le_one (states source false)
  unfold rootConversionBirths
  omega

theorem convertRoot_entries {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (families ids : Bool → ℕ) (states : States n) (owner : External n) (side : Bool) :
    entries (convertRoot rank source families ids states owner side)=entries (states owner side) := by
  unfold convertRoot
  split_ifs <;> simp

theorem convertRoot_empty {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (families ids : Bool → ℕ) (states : States n) (side : Bool) :
    growerEntries (convertRoot rank source families ids states source side).grower=[] := by
  simp only [convertRoot,ite_true]
  exact converted_grower_empty ..

theorem convertRoot_tagged {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (families ids : Bool → ℕ) (states : States n) (owner : External n) (side : Bool) :
    StateLabels.tagged (rank owner.val) (convertRoot rank source families ids states owner side) =
      StateLabels.tagged (rank owner.val) (states owner side) := by
  unfold convertRoot
  split_ifs
  · exact StateLabels.tagged_convert ..
  · rfl

theorem convertRoot_labels {n : ℕ} (rank : ℕ → ℕ) (K : ℤ) (source : External n)
    (families ids : Bool → ℕ) (states : States n) :
    StateLabels.label rank K (convertRoot rank source families ids states)=StateLabels.label rank K states := by
  funext key
  apply StateLabels.label_congr
  intro base
  simp only [StateLabels.HasBase,convertRoot_tagged]

theorem convertRoot_ready {n : ℕ} (comparator tree : BST 0 n) (source : External n)
    (families ids : Bool → ℕ) (states : States n) (ready : Ready comparator tree states) :
    Ready comparator tree (convertRoot comparator.externalDepth source families ids states) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro owner side
    unfold convertRoot
    split_ifs
    · exact conversion_valid owner.val (families side) (ids side) (comparator.externalDepth owner.val)
        side (states owner side) (ready.valid owner side)
    · exact ready.valid owner side
  · intro owner side entry member
    rw [convertRoot_entries] at member
    exact ready.sound owner side entry member
  · intro record owner parent outside
    obtain ⟨side,entry,member,key⟩ := ready.complete record owner parent outside
    exact ⟨side,entry,by rwa [convertRoot_entries],key⟩
  · intro owner side
    unfold convertRoot
    split_ifs
    · rw [conversion_grower_isSome]
      exact ready.persistent owner side
    · exact ready.persistent owner side
  · intro owner side
    unfold convertRoot
    split_ifs
    · apply convert_bases comparator.externalDepth owner.val (families side) (ids side)
        (states owner side) (ready.bases owner side)
      intro entry member
      exact parentSound_rank_floor comparator tree owner _ (ready.sound owner side) entry
        (List.mem_append_right _ member)
    · exact ready.bases owner side

theorem conversion_histories (owner family id base : ℕ) (state : SideState)
    (histories : (∀ b∈state.shrinking, ∃ orientation, HistMonotone orientation b.members) ∧
      (∀ g, state.grower=some g → HistMonotone true g.members)) :
    (∀ b∈(convert owner family id base state).shrinking,
      ∃ orientation, HistMonotone orientation b.members) ∧
    (∀ g, (convert owner family id base state).grower=some g → HistMonotone true g.members) := by
  cases hg : state.grower with
  | none => simpa [convert,hg] using histories
  | some grower =>
      by_cases empty : grower.members=[]
      · simpa [convert,hg,empty] using histories
      · refine ⟨?_,?_⟩
        · intro block member
          have choices : block∈state.shrinking ∨ block=freeze grower.id base grower := by
            simpa [convert,hg,empty] using member
          rcases choices with old | rfl
          · exact histories.1 block old
          · exact ⟨true,histories.2 grower hg⟩
        · intro newGrower equal
          have same : newGrower=emptyGrower owner family id := by simpa [convert,hg,empty] using equal.symm
          rw [same]
          simp [HistMonotone,emptyGrower]

theorem convertRoot_histories {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (families ids : Bool → ℕ) (states : States n) (histories : Histories states) :
    Histories (convertRoot rank source families ids states) := by
  intro owner side
  unfold convertRoot
  split_ifs
  · exact conversion_histories _ _ _ _ _ (histories owner side)
  · exact histories owner side

theorem convertRoot_beforeTime {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (families ids : Bool → ℕ) (states : States n) (clock : ℕ) (before : BeforeTime clock states) :
    BeforeTime clock (convertRoot rank source families ids states) := by
  intro owner side entry member
  rw [convertRoot_entries] at member
  exact before owner side entry member

theorem linkState_bases {n : ℕ} (rank : ℕ → ℕ) (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (fresh : Entry) (bases : AllBases rank states) :
    AllBases rank (linkState states source winner loser sourceSide targetSide fresh) := by
  intro owner side
  unfold linkState
  split_ifs
  · exact bases owner side
  · exact eraseFrozenKey_bases rank owner.val loser.val _ (bases owner side)
  · exact bases owner side

theorem runLinks_bases {n : ℕ} (rank : ℕ → ℕ) (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock : ℕ) (states : States n) (events : List (External n × External n))
    (bases : AllBases rank states) : AllBases rank (runLinks source sourceSide reader clock states events) := by
  induction events generalizing clock states with
  | nil => exact bases
  | cons event rest ih => exact ih (clock+1) _ (linkState_bases _ _ _ _ _ _ _ _ bases)

/-- Convert both real root growers, run the actual Greedy access, and return
a complete Ready state for the next comparator macro. The label trace
starts at the original state because root conversion preserves labels. -/
theorem actual_access_ready {n access : ℕ}
    (height : ℕ → ℤ) (raiseTime : ℤ) (comparator oldTree newTree : BST 0 n)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : GreedyMerge.Surface.Owners height comparator.depth oldOwner n)
    (newOwners : GreedyMerge.Surface.Owners
      (GreedyMerge.Surface.RaiseSurface height n access raiseTime) comparator.depth newOwner n)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (fresh : ∀ key, key<n → height key<raiseTime)
    (oldCanonical : GreedyMerge.Surface.Canonical height
      (fun key => comparator.depth (oldOwner key)) oldTree)
    (newCanonical : GreedyMerge.Surface.Canonical
      (GreedyMerge.Surface.RaiseSurface height n access raiseTime)
      (fun key => comparator.depth (newOwner key)) newTree)
    (p : Decomposition oldTree access) (source : External n) (real : source.val=2*access+1)
    (families ids : Bool → ℕ) (states : States n) (K : ℤ) (clock : ℕ)
    (ready : Ready comparator oldTree states) (histories : Histories states)
    (beforeClock : BeforeTime clock states) :
    ∃ data : AccessScheduleData comparator oldTree newTree p,
      let events := data.events
      let prepared := convertRoot comparator.externalDepth source families ids states
      let reader := fun (_ : ℕ) (current : States n) => StateLabels.label comparator.externalDepth K current
      let sourceSide := fun event : External n × External n => decide (event.2.val<source.val)
      let after := runLinks source sourceSide reader clock prepared events
      Ready comparator newTree after ∧ Histories after ∧ BeforeTime (clock+events.length) after ∧
      StateLabels.label comparator.externalDepth K after =
        GreedyForest.Phase.runLabels comparator.externalDepth (StateLabels.label comparator.externalDepth K states)
          (events.map eventKeys) ∧
      events.length=2*p.count-2 ∧ events.length+rootConversionBirths source states ≤ 2*p.count := by
  let prepared := convertRoot comparator.externalDepth source families ids states
  have preparedReady : Ready comparator oldTree prepared :=
    convertRoot_ready comparator oldTree source families ids states ready
  have preparedHistories : Histories prepared := convertRoot_histories _ _ _ _ _ histories
  have preparedClock : BeforeTime clock prepared := convertRoot_beforeTime _ _ _ _ _ _ beforeClock
  have preparedComplete : CompleteFor (canonicalParent (Snapshot.ofTree comparator) oldTree) prepared := by
    intro record owner parent
    exact preparedReady.complete record owner parent (by simp)
  obtain ⟨data,newSound,newComplete,newOrder,newPersistent,newHistory,newClock,newLabels,eventCount⟩ :=
    actual_access_returns_canonical height raiseTime comparator oldTree newTree oldOwner newOwner oldOwners newOwners
      global fresh oldCanonical newCanonical p source real prepared K clock preparedReady.sound preparedComplete
      preparedReady.valid preparedReady.persistent preparedHistories preparedClock
      (convertRoot_empty _ _ _ _ _)
  refine ⟨data,?_,newHistory,newClock,?_,eventCount,?_⟩
  · refine ⟨newOrder,newSound,?_,newPersistent,?_⟩
    · intro record owner parent _
      exact newComplete record owner parent
    · exact runLinks_bases comparator.externalDepth source _ _ clock prepared data.events preparedReady.bases
  · have labelSame : StateLabels.label comparator.externalDepth K prepared =
        StateLabels.label comparator.externalDepth K states := convertRoot_labels _ _ _ _ _ _
    rw [labelSame] at newLabels
    exact newLabels
  · have births := rootConversionBirths_le_two source states
    have positive := p.positive
    omega

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.convertRoot_ready
#print axioms GreedyMerge.ActualLinks.convertRoot_labels
#print axioms GreedyMerge.ActualLinks.runLinks_bases

#print axioms GreedyMerge.ActualLinks.actual_access_ready
