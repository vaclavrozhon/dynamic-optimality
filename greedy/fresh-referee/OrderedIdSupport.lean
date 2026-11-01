import ComparatorBirthJournal

/-!
Logical-instance support of concrete primitives. These theorems track both
frozen and persistent growing ids; a frozen grower retains its former id.
Freshness of the separately supplied names is not assumed for support.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open GreedyMerge.BirthJournal (cutBirthIds cut_output_supported)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

def liveIds (state : SideState) : List ℕ :=
  state.shrinking.map Frozen.id ++ state.grower.toList.map Grower.id

theorem conversion_id_support (owner family replacementId base : ℕ) (state : SideState)
    (id : ℕ) (member : id ∈ liveIds (convert owner family replacementId base state)) :
    id ∈ liveIds state ∨ id ∈ conversionIds replacementId state := by
  cases hg : state.grower with
  | none => left; simpa [convert,hg] using member
  | some grower =>
      by_cases empty : grower.members=[]
      · left; simpa [convert,hg,empty] using member
      · simp only [convert,hg,if_neg empty,liveIds,List.map_append,List.map_cons,List.map_nil,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false,freeze,emptyGrower,Option.toList_some] at member
        rcases member with (old | same) | same
        · left; exact List.mem_append_left _ old
        · left; simp [liveIds,hg,same]
        · right; simpa [conversionIds,hg,empty] using same

theorem eraseFrozenKey_id_support (key : ℕ) (state : SideState) :
    liveIds (eraseFrozenKey key state) = liveIds state := by
  simp [liveIds,eraseFrozenKey,List.map_map,Function.comp_def,eraseMember]

theorem cutState_id_support (side : Bool) (cut fresh : ℕ) (state : SideState)
    (id : ℕ) (member : id ∈ liveIds (cutState side cut fresh state)) :
    id ∈ liveIds state ∨ id ∈ cutBirthIds cut fresh state.shrinking := by
  rcases List.mem_append.mp member with frozen | growing
  · obtain ⟨piece,pieceMem,rfl⟩ := List.mem_map.mp frozen
    rcases cut_output_supported side cut fresh state.shrinking piece pieceMem with old | born
    · exact Or.inl (List.mem_append_left _ old)
    · exact Or.inr born
  · exact Or.inl (List.mem_append_right _ growing)

theorem installPaid_id_support (owner : ℕ) (side : Bool)
    (splitStart paidId paidFamily base : ℕ) (entry : Entry) (state : SideState)
    (id : ℕ) (member : id ∈ liveIds (installPaid owner side splitStart paidId paidFamily base entry state)) :
    id ∈ liveIds state ∨ id ∈ cutBirthIds entry.key splitStart state.shrinking ++ [paidId] := by
  rcases List.mem_append.mp member with frozen | growing
  · obtain ⟨piece,pieceMem,rfl⟩ := List.mem_map.mp frozen
    change piece ∈ (separateOuter side entry.key splitStart state).1 ++
      [singleton paidId paidFamily owner base entry] ++ (separateOuter side entry.key splitStart state).2 at pieceMem
    simp only [List.mem_append,List.mem_singleton] at pieceMem
    rcases pieceMem with (inside | paid) | outside
    · have cutMem := (List.mem_filter.mp inside).1
      rcases cut_output_supported side entry.key splitStart state.shrinking piece cutMem with old | born
      · exact Or.inl (List.mem_append_left _ old)
      · exact Or.inr (List.mem_append_left _ born)
    · subst piece
      right
      exact List.mem_append_right _ (by simp [singleton])
    · have cutMem := (List.mem_filter.mp outside).1
      rcases cut_output_supported side entry.key splitStart state.shrinking piece cutMem with old | born
      · exact Or.inl (List.mem_append_left _ old)
      · exact Or.inr (List.mem_append_left _ born)
  · exact Or.inl (List.mem_append_right _ growing)

theorem paidInsertion_id_support (owner : ℕ) (side : Bool)
    (replacementFamily replacementId splitStart paidId paidFamily base : ℕ)
    (entry : Entry) (state : SideState) (id : ℕ)
    (member : id ∈ liveIds (paidInsertion owner side replacementFamily replacementId splitStart
      paidId paidFamily base entry state)) :
    id ∈ liveIds state ∨
      id ∈ paidInsertionIds owner replacementFamily replacementId splitStart paidId base entry state := by
  rcases installPaid_id_support owner side splitStart paidId paidFamily base entry
    (convert owner replacementFamily replacementId base state) id member with converted | born
  · rcases conversion_id_support owner replacementFamily replacementId base state id converted with old | born
    · exact Or.inl old
    · right
      simp only [paidInsertionIds,List.mem_append]
      exact Or.inl (Or.inl born)
  · right
    simp only [paidInsertionIds,List.mem_append]
    rcases List.mem_append.mp born with cut | paid
    · exact Or.inl (Or.inr cut)
    · exact Or.inr paid

theorem rebaseSide_liveIds (beforeRank afterRank : ℕ → ℕ) (owner : ℕ) (state : SideState) :
    liveIds (rebaseSide beforeRank afterRank owner state) = liveIds state := by
  simp [liveIds,rebaseSide,List.map_map,Function.comp_def,rebaseFrozen,rebase]

def LiveId {n : ℕ} (states : HeapSides n) (id : ℕ) : Prop :=
  ∃ owner side, id ∈ liveIds (states owner side)

def SupportsIds {n : ℕ} (before after : HeapSides n) (born : List ℕ) : Prop :=
  ∀ id, LiveId after id → LiveId before id ∨ id ∈ born

theorem supportsIds_refl {n : ℕ} (states : HeapSides n) : SupportsIds states states [] := by
  intro id member
  exact Or.inl member

theorem supportsIds_trans {n : ℕ} {first second third : HeapSides n} {firstBorn secondBorn : List ℕ}
    (firstSupport : SupportsIds first second firstBorn) (secondSupport : SupportsIds second third secondBorn) :
    SupportsIds first third (firstBorn ++ secondBorn) := by
  intro id member
  rcases secondSupport id member with middle | born
  · rcases firstSupport id middle with old | born
    · exact Or.inl old
    · exact Or.inr (List.mem_append_left _ born)
  · exact Or.inr (List.mem_append_right _ born)

theorem restorePort_id_support {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n) (states : HeapSides n) :
    SupportsIds states (restorePort snapshot tree names makeEntry record states).1
      (restorePortIds snapshot tree names makeEntry record states) := by
  intro id member
  cases parent : canonicalParent snapshot tree record with
  | none => left; simpa [restorePort,parent] using member
  | some actualOwner =>
      obtain ⟨owner,side,member⟩ := member
      simp only [restorePort,parent,replaceSide] at member
      split_ifs at member with place
      · obtain ⟨ownerEq,sideEq⟩ := place
        subst owner
        subst side
        rcases paidInsertion_id_support actualOwner.val _ names.replacementFamily names.replacementId
          names.splitStart names.paidId names.paidFamily (snapshot.rank actualOwner) (makeEntry actualOwner)
          (states actualOwner _) id member with old | born
        · exact Or.inl ⟨actualOwner,_,old⟩
        · right; simpa only [restorePortIds,parent] using born
      · exact Or.inl ⟨owner,side,member⟩

theorem restorePorts_id_support {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (ports : List (External n)) (stage : ℕ) (states : HeapSides n) :
    SupportsIds states (restorePorts snapshot tree names makeEntry ports stage states).1
      (restorePortsIds snapshot tree names makeEntry ports stage states) := by
  induction ports generalizing stage states with
  | nil => exact supportsIds_refl states
  | cons record rest ih =>
      exact supportsIds_trans (restorePort_id_support snapshot tree (names stage) (makeEntry stage record) record states)
        (ih (stage+1) _)

theorem conversionIds_member (replacementId : ℕ) (state : SideState) (id : ℕ)
    (member : id ∈ conversionIds replacementId state) : id = replacementId := by
  cases hg : state.grower with
  | none => simp [conversionIds,hg] at member
  | some grower =>
      by_cases empty : grower.members=[] <;> simp [conversionIds,hg,empty] at member
      exact member

theorem mem_collectIds {α : Type*} (locations : Finset α) (journal : α → List ℕ) (id : ℕ) :
    id ∈ collectIds locations journal ↔ ∃ location ∈ locations, id ∈ journal location := by
  classical
  simp [collectIds]

theorem prepareAllGrowers_id_support {n : ℕ} (before after : BST 0 n)
    (families ids : External n → Bool → ℕ) (states : HeapSides n) :
    SupportsIds states (prepareAllGrowers before after families ids states)
      (prepareAllGrowersIds before after ids states) := by
  intro id ⟨owner,side,member⟩
  by_cases selected : GrowerMismatch before after owner (states owner side)
  · simp only [prepareAllGrowers,prepareGrower,if_pos selected] at member
    rcases conversion_id_support owner.val (families owner side) (ids owner side)
      (before.externalDepth owner.val) (states owner side) id member with old | born
    · exact Or.inl ⟨owner,side,old⟩
    · right
      apply (mem_collectIds _ _ id).mpr
      refine ⟨owner,Finset.mem_univ _,?_⟩
      cases side
      · exact List.mem_append_left _ (by simpa only [growerPreparationIds,if_pos selected] using born)
      · exact List.mem_append_right _ (by simpa only [growerPreparationIds,if_pos selected] using born)
  · left
    exact ⟨owner,side,by simpa only [prepareAllGrowers,prepareGrower,if_neg selected] using member⟩

theorem detachAll_id_support {n : ℕ} (before : BST 0 n) (key : ℕ)
    (families ids : External n → Bool → ℕ) (states : HeapSides n) :
    SupportsIds states (detachAll before key families ids states) (detachAllIds key ids states) := by
  intro id ⟨owner,side,member⟩
  change id ∈ liveIds (eraseFrozenKey key (sealPortSource owner.val (families owner side)
    (ids owner side) (before.externalDepth owner.val) key (states owner side))) at member
  rw [eraseFrozenKey_id_support] at member
  by_cases selected : growerHasKey key (states owner side)=true
  · simp only [sealPortSource,selected,↓reduceIte] at member
    rcases conversion_id_support owner.val (families owner side) (ids owner side)
      (before.externalDepth owner.val) (states owner side) id member with old | born
    · exact Or.inl ⟨owner,side,old⟩
    · right
      apply List.mem_map.mpr
      refine ⟨(owner,side),?_,(conversionIds_member _ _ _ born).symm⟩
      simpa only [Finset.mem_toList,portSources,Finset.mem_filter,Finset.mem_univ,true_and] using selected
  · left
    exact ⟨owner,side,by simpa only [sealPortSource,if_neg selected] using member⟩

theorem detachPorts_id_support {n : ℕ} (before : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n) :
    SupportsIds states (detachPorts before families ids ports stage states).1
      (detachPortsIds before families ids ports stage states) := by
  induction ports generalizing stage states with
  | nil => exact supportsIds_refl states
  | cons key rest ih =>
      exact supportsIds_trans (detachAll_id_support before key (families stage) (ids stage) states)
        (ih (stage+1) _)

theorem sealOwners_id_support {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (states : HeapSides n) :
    SupportsIds states (sealOwners before owners families ids states) (sealOwnersIds owners ids states) := by
  intro id ⟨owner,side,member⟩
  by_cases selected : owner ∈ owners
  · simp only [sealOwners,if_pos selected] at member
    rcases conversion_id_support owner.val (families owner side) (ids owner side)
      (before.externalDepth owner.val) (states owner side) id member with old | born
    · exact Or.inl ⟨owner,side,old⟩
    · right
      apply (mem_collectIds _ _ id).mpr
      refine ⟨owner,selected,?_⟩
      cases side
      · exact List.mem_append_left _ born
      · exact List.mem_append_right _ born
  · exact Or.inl ⟨owner,side,by simpa only [sealOwners,if_neg selected] using member⟩

theorem cutAllOwners_id_support {n : ℕ} (cut : ℕ) (allocate : External n → Bool → ℕ)
    (states : HeapSides n) :
    SupportsIds states (cutAllOwners cut allocate states) (cutAllOwnersIds cut allocate states) := by
  intro id ⟨owner,side,member⟩
  rcases cutState_id_support side cut (allocate owner side) (states owner side) id member with old | born
  · exact Or.inl ⟨owner,side,old⟩
  · right
    apply (mem_collectIds _ _ id).mpr
    refine ⟨owner,Finset.mem_univ _,?_⟩
    cases side
    · exact List.mem_append_left _ born
    · exact List.mem_append_right _ born

theorem prepareCuts_id_support {n : ℕ} (allocate : NameSupply n) (cuts : List (ℕ × ℕ))
    (stage : ℕ) (states : HeapSides n) :
    SupportsIds states (prepareCuts allocate cuts stage states).1
      (prepareCutsIds allocate cuts stage states) := by
  induction cuts generalizing stage states with
  | nil => exact supportsIds_refl states
  | cons entry rest ih =>
      exact supportsIds_trans (cutAllOwners_id_support entry.1 (allocate stage) states) (ih (stage+1) _)

theorem prepareComparator_id_support {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n) :
    SupportsIds states (prepareComparator profile families ids ports bulkOwners states).1
      (prepareComparatorIds profile families ids ports bulkOwners states) := by
  exact supportsIds_trans (supportsIds_trans (supportsIds_trans
    (prepareAllGrowers_id_support before after (families 0) (ids 0) states)
    (detachPorts_id_support before families ids ports 1 _))
    (sealOwners_id_support before bulkOwners (families (ports.length+1)) (ids (ports.length+1)) _))
    (prepareCuts_id_support ids profile.entries (ports.length+2) _)

theorem moveJunction_id_support {n : ℕ} (oldOwner newOwner : External n) (lo hi : ℕ)
    (fresh : Bool → ℕ) (states : HeapSides n) :
    SupportsIds states (moveJunction oldOwner newOwner lo hi fresh states)
      (junctionTransferIds oldOwner lo hi fresh states) := by
  intro id ⟨owner,side,member⟩
  have fromCut : ∀ piece ∈ cutList side (junctionCut side lo hi) (fresh side) (states oldOwner side).shrinking,
      piece.id ∈ (states oldOwner side).shrinking.map Frozen.id ∨
      piece.id ∈ junctionTransferIds oldOwner lo hi fresh states := by
    intro piece pieceMem
    rcases cut_output_supported side (junctionCut side lo hi) (fresh side)
      (states oldOwner side).shrinking piece pieceMem with old | born
    · exact Or.inl old
    · right
      cases side
      · exact List.mem_append_left _ born
      · exact List.mem_append_right _ born
  unfold moveJunction at member
  split_ifs at member with source receiver
  · rcases List.mem_append.mp member with frozen | growing
    · obtain ⟨piece,pieceMem,rfl⟩ := List.mem_map.mp frozen
      rcases fromCut piece (List.mem_filter.mp pieceMem).1 with old | born
      · exact Or.inl ⟨oldOwner,side,List.mem_append_left _ old⟩
      · exact Or.inr born
    · exact Or.inl ⟨oldOwner,side,List.mem_append_right _ growing⟩
  · rcases List.mem_append.mp member with frozen | growing
    · obtain ⟨piece,pieceMem,rfl⟩ := List.mem_map.mp frozen
      rcases List.mem_append.mp pieceMem with old | moved
      · exact Or.inl ⟨newOwner,side,List.mem_append_left _ (List.mem_map.mpr ⟨piece,old,rfl⟩)⟩
      · rcases fromCut piece (List.mem_filter.mp moved).1 with old | born
        · exact Or.inl ⟨oldOwner,side,List.mem_append_left _ old⟩
        · exact Or.inr born
    · exact Or.inl ⟨newOwner,side,List.mem_append_right _ growing⟩
  · exact Or.inl ⟨owner,side,member⟩

theorem rebaseAll_id_support {n : ℕ} (before after : BST 0 n) (states : HeapSides n) :
    SupportsIds states (rebaseAll before after states) [] := by
  intro id ⟨owner,side,member⟩
  exact Or.inl ⟨owner,side,by simpa only [rebaseAll,rebaseSide_liveIds] using member⟩

theorem administerJunction_id_support {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (families ids : NameSupply n) (node : AtNode n)
    (oldOwner newOwner : External n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (states : HeapSides n) :
    SupportsIds states
      (administerJunction profile tree families ids node oldOwner newOwner bulkFresh paidNames makeEntry states).1
      (administerJunctionIds profile tree families ids node oldOwner newOwner bulkFresh paidNames makeEntry states) := by
  have prepared := prepareComparator_id_support profile families ids (junctionPorts (Snapshot.ofTree before) node)
    {oldOwner,newOwner} states
  have moved := supportsIds_trans prepared
    (moveJunction_id_support oldOwner newOwner node.lower node.upper bulkFresh _)
  have rebased := supportsIds_trans moved (rebaseAll_id_support before after _)
  have restored := supportsIds_trans rebased (restorePorts_id_support (Snapshot.ofTree after) tree paidNames makeEntry
    (junctionRecords (Snapshot.ofTree before) node) 0 _)
  simpa only [List.append_nil,administerJunction,administerJunctionIds,prepareMoveJunction] using restored

#print axioms conversion_id_support
#print axioms paidInsertion_id_support
#print axioms restorePorts_id_support
#print axioms administerJunction_id_support

end GreedyMerge.OrderedBlocks
