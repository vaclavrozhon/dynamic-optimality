import FreshPaidInsertion

/-!
Fresh instance allocation and global identity preservation for actual bulk
outer transfer. The source cut retires only straddling instances; whole
pieces are then redistributed between the two locations without changing
any id. Persistent grower identities remain at their original locations.
-/
namespace GreedyMerge.FreshIds

open GreedyMerge.OrderedBlocks
open GreedyMerge.BirthJournal (cutBirthIds cut_output_supported)

def replaceTwo {slots : ℕ} (states : Fin slots → SideState) (source receiver : Fin slots)
    (sourceState receiverState : SideState) : Fin slots → SideState :=
  fun slot => if slot=source then sourceState else if slot=receiver then receiverState else states slot

theorem inventory_update {slots : ℕ} (states : Fin slots → SideState) (start next : ℕ)
    (inventory : Inventory states start) (slot : Fin slots) (replacement : SideState)
    (unique : (liveIds replacement).Nodup)
    (origin : ∀ id ∈ liveIds replacement,id ∈ liveIds (states slot) ∨ start ≤ id)
    (below : ∀ id ∈ liveIds replacement,id<next) (monotone : start≤next) :
    Inventory (Function.update states slot replacement) next := by
  refine ⟨?_,?_,?_⟩
  · intro current
    by_cases same : current=slot
    · subst current;simpa only [Function.update_self] using unique
    · simpa only [Function.update_of_ne same] using inventory.localUnique current
  · intro first second id firstMem secondMem
    by_cases firstEq : first=slot
    · subst first
      rw [Function.update_self] at firstMem
      by_cases secondEq : second=slot
      · exact secondEq.symm
      · rw [Function.update_of_ne secondEq] at secondMem
        rcases origin id firstMem with old | fresh
        · exact inventory.locations slot second id old secondMem
        · have bound := inventory.below second id secondMem;omega
    · rw [Function.update_of_ne firstEq] at firstMem
      by_cases secondEq : second=slot
      · subst second
        rw [Function.update_self] at secondMem
        rcases origin id secondMem with old | fresh
        · exact inventory.locations first slot id firstMem old
        · have bound := inventory.below first id firstMem;omega
      · rw [Function.update_of_ne secondEq] at secondMem
        exact inventory.locations first second id firstMem secondMem
  · intro current id member
    by_cases same : current=slot
    · subst current;rw [Function.update_self] at member;exact below id member
    · rw [Function.update_of_ne same] at member
      exact lt_of_lt_of_le (inventory.below current id member) monotone

/-- Any literal permutation of the combined ids of two distinct locations
preserves the complete global Inventory. -/
theorem replaceTwo_inventory {slots : ℕ} (states : Fin slots → SideState) (next : ℕ)
    (inventory : Inventory states next) (source receiver : Fin slots) (different : source≠receiver)
    (sourceState receiverState : SideState)
    (permutation : (liveIds sourceState ++ liveIds receiverState).Perm
      (liveIds (states source) ++ liveIds (states receiver))) :
    Inventory (replaceTwo states source receiver sourceState receiverState) next := by
  have oldUnique : (liveIds (states source) ++ liveIds (states receiver)).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨inventory.localUnique source,inventory.localUnique receiver,
      fun first firstMem second secondMem equal => different
        (inventory.locations source receiver first firstMem (by simpa only [←equal] using secondMem))⟩
  have newUnique := List.nodup_append.mp (permutation.nodup_iff.mpr oldUnique)
  have sourceOrigin : ∀ id ∈ liveIds sourceState,
      id ∈ liveIds (states source) ∨ id ∈ liveIds (states receiver) := by
    intro id member
    exact List.mem_append.mp (permutation.mem_iff.mp (List.mem_append_left _ member))
  have receiverOrigin : ∀ id ∈ liveIds receiverState,
      id ∈ liveIds (states source) ∨ id ∈ liveIds (states receiver) := by
    intro id member
    exact List.mem_append.mp (permutation.mem_iff.mp (List.mem_append_right _ member))
  refine ⟨?_,?_,?_⟩
  · intro slot
    unfold replaceTwo
    split_ifs
    · exact newUnique.1
    · exact newUnique.2.1
    · exact inventory.localUnique slot
  · intro first second id firstMem secondMem
    by_cases firstSource : first=source
    · subst first
      simp only [replaceTwo,↓reduceIte] at firstMem
      by_cases secondSource : second=source
      · exact secondSource.symm
      · by_cases secondReceiver : second=receiver
        · subst second
          simp only [replaceTwo,if_neg different.symm,↓reduceIte] at secondMem
          exact False.elim (newUnique.2.2 id firstMem id secondMem rfl)
        · simp only [replaceTwo,if_neg secondSource,if_neg secondReceiver] at secondMem
          rcases sourceOrigin id firstMem with oldSource | oldReceiver
          · exact inventory.locations source second id oldSource secondMem
          · exact False.elim (secondReceiver (inventory.locations receiver second id oldReceiver secondMem).symm)
    · by_cases firstReceiver : first=receiver
      · subst first
        simp only [replaceTwo,if_neg different.symm,↓reduceIte] at firstMem
        by_cases secondSource : second=source
        · subst second
          simp only [replaceTwo,↓reduceIte] at secondMem
          exact False.elim (newUnique.2.2 id secondMem id firstMem rfl)
        · by_cases secondReceiver : second=receiver
          · exact secondReceiver.symm
          · simp only [replaceTwo,if_neg secondSource,if_neg secondReceiver] at secondMem
            rcases receiverOrigin id firstMem with oldSource | oldReceiver
            · exact False.elim (secondSource (inventory.locations source second id oldSource secondMem).symm)
            · exact inventory.locations receiver second id oldReceiver secondMem
      · simp only [replaceTwo,if_neg firstSource,if_neg firstReceiver] at firstMem
        by_cases secondSource : second=source
        · subst second
          simp only [replaceTwo,↓reduceIte] at secondMem
          rcases sourceOrigin id secondMem with oldSource | oldReceiver
          · exact inventory.locations first source id firstMem oldSource
          · exact False.elim (firstReceiver (inventory.locations first receiver id firstMem oldReceiver))
        · by_cases secondReceiver : second=receiver
          · subst second
            simp only [replaceTwo,if_neg different.symm,↓reduceIte] at secondMem
            rcases receiverOrigin id secondMem with oldSource | oldReceiver
            · exact False.elim (firstSource (inventory.locations first source id firstMem oldSource))
            · exact inventory.locations first receiver id firstMem oldReceiver
          · simp only [replaceTwo,if_neg secondSource,if_neg secondReceiver] at secondMem
            exact inventory.locations first second id firstMem secondMem
  · intro slot id member
    unfold replaceTwo at member
    split_ifs at member
    · rcases sourceOrigin id member with old | old
      · exact inventory.below source id old
      · exact inventory.below receiver id old
    · rcases receiverOrigin id member with old | old
      · exact inventory.below source id old
      · exact inventory.below receiver id old
    · exact inventory.below slot id member

theorem moveOuter_liveIds_perm (side : Bool) (cut fresh : ℕ) (source receiver : SideState) :
    (liveIds (moveOuter side cut fresh source receiver).1 ++ liveIds (moveOuter side cut fresh source receiver).2).Perm
      (liveIds (cutState side cut fresh source) ++ liveIds receiver) := by
  let inside := (separateOuter side cut fresh source).1.map Frozen.id
  let outside := (separateOuter side cut fresh source).2.map Frozen.id
  let sourceGrower := source.grower.toList.map Grower.id
  let receiverBlocks := receiver.shrinking.map Frozen.id
  let receiverGrower := receiver.grower.toList.map Grower.id
  have partition : (inside ++ outside).Perm ((cutList side cut fresh source.shrinking).map Frozen.id) := by
    simpa only [inside,outside,separateOuter,List.map_append] using
      (List.filter_append_perm (blockInside side cut) (cutList side cut fresh source.shrinking)).map Frozen.id
  have commute : ((sourceGrower ++ receiverBlocks) ++ outside).Perm (outside ++ (sourceGrower ++ receiverBlocks)) :=
    List.perm_append_comm
  have swap := (commute.append_left inside).append_right receiverGrower
  have finish := ((partition.append_right sourceGrower).append_right receiverBlocks).append_right receiverGrower
  have result : (inside ++ sourceGrower ++ receiverBlocks ++ outside ++ receiverGrower).Perm
      ((cutList side cut fresh source.shrinking).map Frozen.id ++ sourceGrower ++ receiverBlocks ++ receiverGrower) :=
    (by simpa only [List.append_assoc] using swap.trans (by simpa only [List.append_assoc] using finish))
  simpa only [liveIds,moveOuter,transfer,cutState,List.map_append,inside,outside,sourceGrower,receiverBlocks,receiverGrower,
    List.append_assoc] using result

noncomputable def freshOuterMove {slots : ℕ} (source receiver : Fin slots) (side : Bool) (cut start : ℕ)
    (states : Fin slots → SideState) : (Fin slots → SideState) × ℕ :=
  let moved := moveOuter side cut start (states source) (states receiver)
  (replaceTwo states source receiver moved.1 moved.2,start+2*(states source).shrinking.length)

theorem freshOuterMove_inventory {slots : ℕ} (source receiver : Fin slots) (different : source≠receiver)
    (side : Bool) (cut start : ℕ) (states : Fin slots → SideState) (inventory : Inventory states start) :
    Inventory (freshOuterMove source receiver side cut start states).1
      (freshOuterMove source receiver side cut start states).2 := by
  let sourceCut := cutState side cut start (states source)
  let cutStates := Function.update states source sourceCut
  let next := start+2*(states source).shrinking.length
  have sourceUnique := cutState_ids_unique side cut start (states source) (inventory.localUnique source) (inventory.below source)
  have sourceBelow := cutState_ids_below side cut start (states source) (inventory.below source)
  have sourceOrigin : ∀ id ∈ liveIds sourceCut,id ∈ liveIds (states source) ∨ start ≤ id := by
    intro id member
    rcases cutState_id_support side cut start (states source) id member with old | born
    · exact Or.inl old
    · exact Or.inr (BirthJournal.cutBirthIds_range cut start (states source).shrinking id born).1
  have cutInventory : Inventory cutStates next := inventory_update states start next inventory source sourceCut
    sourceUnique sourceOrigin sourceBelow (Nat.le_add_right _ _)
  have perm := moveOuter_liveIds_perm side cut start (states source) (states receiver)
  have moved := replaceTwo_inventory cutStates next cutInventory source receiver different
    (moveOuter side cut start (states source) (states receiver)).1
    (moveOuter side cut start (states source) (states receiver)).2
    (by simpa only [cutStates,Function.update_self,Function.update_of_ne different.symm] using perm)
  have equal : replaceTwo cutStates source receiver
      (moveOuter side cut start (states source) (states receiver)).1
      (moveOuter side cut start (states source) (states receiver)).2 =
      (freshOuterMove source receiver side cut start states).1 := by
    funext slot
    dsimp only [freshOuterMove]
    unfold replaceTwo
    split_ifs with isSource isReceiver
    · rfl
    · rfl
    · exact Function.update_of_ne isSource sourceCut states
  simpa only [equal,freshOuterMove,next] using moved

/-- Exact location-sensitive provenance. Source survivors use only old
source ids or actual cut births; receiver newcomers have precisely that
same provenance, while old receiver instances are retained. -/
theorem moveOuter_id_origin (side : Bool) (cut fresh : ℕ) (source receiver : SideState) (id : ℕ) :
    (id ∈ liveIds (moveOuter side cut fresh source receiver).1 →
      id ∈ liveIds source ∨ id ∈ cutBirthIds cut fresh source.shrinking) ∧
    (id ∈ liveIds (moveOuter side cut fresh source receiver).2 →
      id ∈ liveIds receiver ∨ id ∈ liveIds source ∨ id ∈ cutBirthIds cut fresh source.shrinking) := by
  constructor
  · intro member
    rcases List.mem_append.mp member with frozen | growing
    · obtain ⟨piece,pieceMem,rfl⟩ := List.mem_map.mp frozen
      rcases cut_output_supported side cut fresh source.shrinking piece (List.mem_filter.mp pieceMem).1 with old | born
      · exact Or.inl (List.mem_append_left _ old)
      · exact Or.inr born
    · exact Or.inl (List.mem_append_right _ growing)
  · intro member
    rcases List.mem_append.mp member with frozen | growing
    · obtain ⟨piece,pieceMem,rfl⟩ := List.mem_map.mp frozen
      rcases List.mem_append.mp pieceMem with old | moved
      · exact Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨piece,old,rfl⟩))
      · right
        rcases cut_output_supported side cut fresh source.shrinking piece (List.mem_filter.mp moved).1 with old | born
        · exact Or.inl (List.mem_append_left _ old)
        · exact Or.inr born
    · exact Or.inl (List.mem_append_right _ growing)

noncomputable def freshOuterJournal {slots : ℕ} (source : Fin slots) (cut start : ℕ)
    (states : Fin slots → SideState) : List ℕ := cutBirthIds cut start (states source).shrinking

theorem freshOuterJournal_spec {slots : ℕ} (source receiver : Fin slots) (side : Bool)
    (cut start : ℕ) (states : Fin slots → SideState) (inventory : Inventory states start) :
    (freshOuterJournal source cut start states).Nodup ∧
    (freshOuterJournal source cut start states).length=cutListBirths cut (states source).shrinking ∧
    (∀ id ∈ freshOuterJournal source cut start states,
      start ≤ id ∧ id < (freshOuterMove source receiver side cut start states).2) := by
  refine ⟨BirthJournal.cutBirthIds_nodup side cut start _
    (List.nodup_append.mp (inventory.localUnique source)).1 ?_,BirthJournal.cutBirthIds_length _ _ _,?_⟩
  · intro block member
    exact inventory.below source block.id (List.mem_append_left _ (List.mem_map.mpr ⟨block,member,rfl⟩))
  · intro id member
    exact BirthJournal.cutBirthIds_range cut start (states source).shrinking id member

theorem freshOuterMove_id_support {slots : ℕ} (source receiver : Fin slots) (side : Bool)
    (cut start : ℕ) (states : Fin slots → SideState) (slot : Fin slots) (id : ℕ)
    (member : id ∈ liveIds ((freshOuterMove source receiver side cut start states).1 slot)) :
    (∃ oldSlot, id ∈ liveIds (states oldSlot)) ∨ id ∈ freshOuterJournal source cut start states := by
  dsimp only [freshOuterMove] at member
  unfold replaceTwo at member
  split_ifs at member
  · rcases (moveOuter_id_origin side cut start (states source) (states receiver) id).1 member with old | born
    · exact Or.inl ⟨source,old⟩
    · exact Or.inr born
  · rcases (moveOuter_id_origin side cut start (states source) (states receiver) id).2 member with old | old | born
    · exact Or.inl ⟨receiver,old⟩
    · exact Or.inl ⟨source,old⟩
    · exact Or.inr born
  · exact Or.inl ⟨slot,member⟩

#print axioms replaceTwo_inventory
#print axioms moveOuter_liveIds_perm
#print axioms freshOuterMove_inventory
#print axioms moveOuter_id_origin
#print axioms freshOuterJournal_spec
#print axioms freshOuterMove_id_support

end GreedyMerge.FreshIds
