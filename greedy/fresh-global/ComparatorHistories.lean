import AccessInventory
import OrderedRecanonicalization

/-! Chronology of literal comparator and refinement administration.
Cuts, moves, conversions and rebases retain immutable joined times. Paid
entries use the actual consecutive restoration stages. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives

def BlockChronology (clock : ℕ) (block : Frozen) : Prop :=
  (∃ orientation, HistMonotone orientation block.members) ∧
    ∀ entry∈block.members, entry.joined<clock

def GrowerChronology (clock : ℕ) (grower : Option Grower) : Prop :=
  ∀ g, grower=some g → HistMonotone true g.members ∧ ∀ entry∈g.members, entry.joined<clock

def SideChronology (clock : ℕ) (state : SideState) : Prop :=
  (∀ block∈state.shrinking, BlockChronology clock block) ∧ GrowerChronology clock state.grower

def Chronology {n : ℕ} (clock : ℕ) (states : States n) : Prop :=
  ∀ owner side, SideChronology clock (states owner side)

theorem chronology_iff {n : ℕ} (clock : ℕ) (states : States n) :
    Chronology clock states ↔ Histories states ∧ BeforeTime clock states := by
  constructor
  · intro good
    constructor
    · intro owner side
      exact ⟨fun block member => ((good owner side).1 block member).1,
        fun g present => ((good owner side).2 g present).1⟩
    · intro owner side entry member
      rcases List.mem_append.mp member with frozen | growing
      · obtain ⟨block,blockMem,entryMem⟩ := List.mem_flatMap.mp frozen
        exact ((good owner side).1 block blockMem).2 entry entryMem
      · cases hg : (states owner side).grower with
        | none => simp [growerEntries,hg] at growing
        | some g => exact ((good owner side).2 g hg).2 entry (by simpa [growerEntries,hg] using growing)
  · rintro ⟨histories,before⟩ owner side
    constructor
    · intro block member
      exact ⟨(histories owner side).1 block member,fun entry entryMem =>
        before owner side entry (List.mem_append_left _ (List.mem_flatMap.mpr ⟨block,member,entryMem⟩))⟩
    · intro g present
      refine ⟨(histories owner side).2 g present,?_⟩
      intro entry member
      apply before owner side entry
      exact List.mem_append_right _ (by simpa [growerEntries,present] using member)

theorem SideChronology.mono {first second : ℕ} {state : SideState}
    (good : SideChronology first state) (later : first ≤ second) : SideChronology second state := by
  exact ⟨fun block member => ⟨(good.1 block member).1,fun entry hm => lt_of_lt_of_le ((good.1 block member).2 entry hm) later⟩,
    fun g present => ⟨(good.2 g present).1,fun entry hm => lt_of_lt_of_le ((good.2 g present).2 entry hm) later⟩⟩

theorem Chronology.mono {n first second : ℕ} {states : States n}
    (good : Chronology first states) (later : first ≤ second) : Chronology second states :=
  fun owner side => (good owner side).mono later

theorem BlockChronology.inherit {clock : ℕ} {first second : Frozen}
    (good : BlockChronology clock first) (sublist : second.members.Sublist first.members) :
    BlockChronology clock second := by
  obtain ⟨⟨orientation,history⟩,before⟩ := good
  exact ⟨⟨orientation,history.sublist sublist⟩,fun entry member => before entry (sublist.subset member)⟩

theorem conversion_chronology (owner family id base clock : ℕ) (state : SideState)
    (good : SideChronology clock state) : SideChronology clock (convert owner family id base state) := by
  cases hg : state.grower with
  | none => simpa [convert,hg] using good
  | some g =>
    by_cases empty : g.members=[]
    · simpa [convert,hg,empty] using good
    · constructor
      · intro block member
        simp only [convert,hg,if_neg empty,List.mem_append,List.mem_singleton] at member
        rcases member with old | rfl
        · exact good.1 block old
        · exact ⟨⟨true,(good.2 g hg).1⟩,(good.2 g hg).2⟩
      · intro growing present
        have equal : growing=emptyGrower owner family id := by simpa [convert,hg,empty] using present.symm
        subst growing
        simp [HistMonotone,emptyGrower]

theorem eraseFrozenKey_chronology (key clock : ℕ) (state : SideState)
    (good : SideChronology clock state) : SideChronology clock (eraseFrozenKey key state) := by
  refine ⟨?_,good.2⟩
  intro block member
  obtain ⟨old,oldMem,rfl⟩ := List.mem_map.mp member
  exact (good.1 old oldMem).inherit List.filter_sublist

theorem cutState_chronology (side : Bool) (cut fresh clock : ℕ) (state : SideState)
    (good : SideChronology clock state) : SideChronology clock (cutState side cut fresh state) := by
  refine ⟨?_,good.2⟩
  intro block member
  obtain ⟨old,oldMem,descendant⟩ := cutList_descends side cut fresh state.shrinking block member
  exact (good.1 old oldMem).inherit descendant.2.2

theorem separateOuter_chronology (side : Bool) (cut fresh clock : ℕ) (state : SideState)
    (good : SideChronology clock state) :
    ∀ block∈(separateOuter side cut fresh state).1++(separateOuter side cut fresh state).2,
      BlockChronology clock block := by
  intro block member
  obtain ⟨old,oldMem,descendant⟩ := separateOuter_descends side cut fresh state block member
  exact (good.1 old oldMem).inherit descendant.2.2

theorem moveOuter_chronology (side : Bool) (cut fresh clock : ℕ) (source receiver : SideState)
    (sourceGood : SideChronology clock source) (receiverGood : SideChronology clock receiver) :
    SideChronology clock (moveOuter side cut fresh source receiver).1 ∧
      SideChronology clock (moveOuter side cut fresh source receiver).2 := by
  have pieces := separateOuter_chronology side cut fresh clock source sourceGood
  constructor
  · exact ⟨fun block member => pieces block (List.mem_append_left _ member),sourceGood.2⟩
  · refine ⟨?_,receiverGood.2⟩
    intro block member
    rcases List.mem_append.mp member with old | moved
    · exact receiverGood.1 block old
    · exact pieces block (List.mem_append_right _ moved)

theorem rebaseSide_chronology (beforeRank afterRank : ℕ → ℕ) (owner clock : ℕ) (state : SideState)
    (good : SideChronology clock state) : SideChronology clock (rebaseSide beforeRank afterRank owner state) := by
  refine ⟨?_,good.2⟩
  intro block member
  obtain ⟨old,oldMem,rfl⟩ := List.mem_map.mp member
  exact good.1 old oldMem

theorem installPaid_chronology (owner clock : ℕ) (side : Bool)
    (splitFresh paidId paidFamily base : ℕ) (entry : Entry) (state : SideState)
    (good : SideChronology clock state) (time : entry.joined<clock) :
    SideChronology clock (installPaid owner side splitFresh paidId paidFamily base entry state) := by
  refine ⟨?_,good.2⟩
  intro block member
  change block∈(separateOuter side entry.key splitFresh state).1++
    [singleton paidId paidFamily owner base entry]++(separateOuter side entry.key splitFresh state).2 at member
  rcases List.mem_append.mp member with inner | outer
  · rcases List.mem_append.mp inner with inner | paid
    · exact separateOuter_chronology side entry.key splitFresh clock state good block (List.mem_append_left _ inner)
    · have same := List.mem_singleton.mp paid
      subst block
      exact ⟨⟨true,by simp [OrderedBlocks.singleton,HistMonotone]⟩,by simpa [OrderedBlocks.singleton] using time⟩
  · exact separateOuter_chronology side entry.key splitFresh clock state good block (List.mem_append_right _ outer)

theorem paidInsertion_chronology (owner clock : ℕ) (side : Bool)
    (replacementFamily replacementId splitFresh paidId paidFamily base : ℕ) (entry : Entry) (state : SideState)
    (good : SideChronology clock state) (time : entry.joined<clock) :
    SideChronology clock (paidInsertion owner side replacementFamily replacementId splitFresh paidId paidFamily base entry state) :=
  installPaid_chronology owner clock side splitFresh paidId paidFamily base entry _
    (conversion_chronology owner replacementFamily replacementId base clock state good) time

theorem prepareAllGrowers_chronology {n : ℕ} (before after : BST 0 n)
    (families ids : External n → Bool → ℕ) (clock : ℕ) (states : States n)
    (good : Chronology clock states) :
    Chronology clock (prepareAllGrowers before after families ids states) := by
  intro owner side
  unfold prepareAllGrowers prepareGrower
  split_ifs
  · exact conversion_chronology _ _ _ _ clock _ (good owner side)
  · exact good owner side

theorem detachAll_chronology {n : ℕ} (before : BST 0 n) (key : ℕ)
    (families ids : External n → Bool → ℕ) (clock : ℕ) (states : States n)
    (good : Chronology clock states) : Chronology clock (detachAll before key families ids states) := by
  intro owner side
  apply eraseFrozenKey_chronology
  unfold sealPortSource
  split_ifs
  · exact conversion_chronology _ _ _ _ clock _ (good owner side)
  · exact good owner side

theorem detachPorts_chronology {n : ℕ} (before : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage clock : ℕ) (states : States n) (good : Chronology clock states) :
    Chronology clock (detachPorts before families ids ports stage states).1 := by
  induction ports generalizing stage states with
  | nil => exact good
  | cons key rest ih => exact ih (stage+1) _ (detachAll_chronology before key _ _ clock states good)

theorem sealOwners_chronology {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (clock : ℕ) (states : States n)
    (good : Chronology clock states) : Chronology clock (sealOwners before owners families ids states) := by
  intro owner side
  unfold sealOwners
  split_ifs
  · exact conversion_chronology _ _ _ _ clock _ (good owner side)
  · exact good owner side

theorem cutAllOwners_chronology {n : ℕ} (cut : ℕ) (allocate : External n → Bool → ℕ)
    (clock : ℕ) (states : States n) (good : Chronology clock states) :
    Chronology clock (cutAllOwners cut allocate states) :=
  fun owner side => cutState_chronology side cut (allocate owner side) clock _ (good owner side)

theorem prepareCuts_chronology {n : ℕ} (allocate : NameSupply n)
    (cuts : List (ℕ × ℕ)) (stage clock : ℕ) (states : States n) (good : Chronology clock states) :
    Chronology clock (prepareCuts allocate cuts stage states).1 := by
  induction cuts generalizing stage states with
  | nil => exact good
  | cons cut rest ih => exact ih (stage+1) _ (cutAllOwners_chronology cut.1 (allocate stage) clock states good)

theorem prepareComparator_chronology {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (clock : ℕ) (states : States n)
    (good : Chronology clock states) :
    Chronology clock (prepareComparator profile families ids ports bulkOwners states).1 := by
  apply prepareCuts_chronology
  apply sealOwners_chronology
  apply detachPorts_chronology
  exact prepareAllGrowers_chronology before after _ _ clock states good

theorem moveJunction_chronology {n : ℕ} (oldOwner newOwner : External n) (lo hi : ℕ)
    (fresh : Bool → ℕ) (clock : ℕ) (states : States n) (good : Chronology clock states) :
    Chronology clock (moveJunction oldOwner newOwner lo hi fresh states) := by
  intro owner side
  have moved := moveOuter_chronology side (junctionCut side lo hi) (fresh side) clock
    (states oldOwner side) (states newOwner side) (good oldOwner side) (good newOwner side)
  unfold moveJunction
  split_ifs
  · exact moved.1
  · exact moved.2
  · exact good owner side

theorem prepareMoveJunction_chronology {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (node : AtNode n) (oldOwner newOwner : External n) (bulkFresh : Bool → ℕ)
    (clock : ℕ) (states : States n) (good : Chronology clock states) :
    Chronology clock (prepareMoveJunction profile families ids node oldOwner newOwner bulkFresh states).1 := by
  apply moveJunction_chronology
  exact prepareComparator_chronology profile families ids _ _ clock states good

theorem rebaseAll_chronology {n : ℕ} (before after : BST 0 n) (clock : ℕ)
    (states : States n) (good : Chronology clock states) : Chronology clock (rebaseAll before after states) :=
  fun owner side => rebaseSide_chronology _ _ _ clock _ (good owner side)

/-- One paid port reserves a stage even when it is the global root and
therefore needs no entry. Existing entries are inherited unchanged. -/
theorem restorePort_chronology {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (clock : ℕ) (states : States n) (good : Chronology clock states)
    (time : ∀ owner, (makeEntry owner).joined=clock) :
    Chronology (clock+1) (restorePort snapshot tree names makeEntry record states).1 := by
  have oldLater := good.mono (Nat.le_succ clock)
  intro owner side
  unfold restorePort
  cases parent : canonicalParent snapshot tree record with
  | none => exact oldLater owner side
  | some receiver =>
    simp only [replaceSide]
    split_ifs
    · apply paidInsertion_chronology
      · exact oldLater _ _
      · rw [time]
        omega
    · exact oldLater owner side

theorem restorePorts_chronology {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (ports : List (External n)) (start stage : ℕ) (states : States n)
    (good : Chronology (start+stage) states)
    (time : ∀ stage record owner, (makeEntry stage record owner).joined=start+stage) :
    Chronology (start+stage+ports.length) (restorePorts snapshot tree names makeEntry ports stage states).1 := by
  induction ports generalizing stage states with
  | nil => simpa only [restorePorts,List.length_nil,Nat.add_zero] using good
  | cons record rest ih =>
    have next := restorePort_chronology snapshot tree (names stage) (makeEntry stage record) record
      (start+stage) states good (time stage record)
    have tail := ih (stage+1) _ (by simpa only [Nat.add_assoc] using next)
    simpa only [restorePorts,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

theorem administerJunction_chronology {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (families ids : NameSupply n) (node : AtNode n) (oldOwner newOwner : External n)
    (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (clock : ℕ) (states : States n) (good : Chronology clock states)
    (time : ∀ stage record owner, (makeEntry stage record owner).joined=clock+stage) :
    Chronology (clock+3)
      (administerJunction profile tree families ids node oldOwner newOwner bulkFresh paidNames makeEntry states).1 := by
  have prepared := prepareMoveJunction_chronology profile families ids node oldOwner newOwner bulkFresh clock states good
  have rebased := rebaseAll_chronology before after clock _ prepared
  have restored := restorePorts_chronology (Snapshot.ofTree after) tree paidNames makeEntry
    (junctionRecords (Snapshot.ofTree before) node) clock 0 _ (by simpa using rebased) time
  simpa only [administerJunction,junctionRecords,List.length_cons,List.length_nil,Nat.add_zero] using restored

theorem administerRankOnly_chronology {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (clock : ℕ) (states : States n) (good : Chronology clock states) :
    Chronology clock (administerRankOnly profile families ids states).1 := by
  apply rebaseAll_chronology
  exact prepareComparator_chronology profile families ids [] ∅ clock states good

theorem executeComparatorPlan_chronology {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : GreedyMerge.ComparatorOuter.RotationPlan before after tree a b) (families ids : NameSupply n)
    (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (clock : ℕ) (states : States n) (good : Chronology clock states)
    (time : ∀ stage record owner, (makeEntry stage record owner).joined=clock+stage) :
    Chronology (clock+3) (executeComparatorPlan profile tree plan families ids bulkFresh paidNames makeEntry states).1 := by
  cases plan with
  | quiet => exact (administerRankOnly_chronology profile families ids clock states good).mono (by omega)
  | junction certificate =>
      exact administerJunction_chronology profile tree families ids certificate.node _ _
        bulkFresh paidNames makeEntry clock states good time

/-- Every actual comparator rotation preserves inherited histories and
uses at most three new chronological paid stages, regardless of depth. -/
theorem administerActualComparator_chronology {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) (tree : BST 0 n)
    (families ids : NameSupply n) (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (clock : ℕ) (states : States n) (histories : Histories states) (beforeTime : BeforeTime clock states)
    (time : ∀ stage record owner, (makeEntry stage record owner).joined=clock+stage) :
    Histories (administerActualComparator rotation tree families ids bulkFresh paidNames makeEntry states).1 ∧
      BeforeTime (clock+3) (administerActualComparator rotation tree families ids bulkFresh paidNames makeEntry states).1 := by
  apply (chronology_iff ..).mp
  exact executeComparatorPlan_chronology _ _ _ families ids bulkFresh paidNames makeEntry clock states
    ((chronology_iff ..).mpr ⟨histories,beforeTime⟩) time

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.paidInsertion_chronology
#print axioms GreedyMerge.ActualLinks.moveOuter_chronology
#print axioms GreedyMerge.ActualLinks.restorePorts_chronology
#print axioms GreedyMerge.ActualLinks.administerActualComparator_chronology
