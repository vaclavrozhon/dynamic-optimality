import FreshInventory

/-!
Concrete paid-insertion name allocation. Conversion gets the current
counter, every old frozen position reserves its two possible split names,
and the paid singleton follows that whole interval. Only actually used
names enter paidInsertionIds; reservations never count as births.
-/
namespace GreedyMerge.FreshIds

open GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.BirthJournal (cutBirthIds cutBirthIds_range)

theorem installPaid_liveIds_perm (owner : ℕ) (side : Bool)
    (splitStart paidId paidFamily base : ℕ) (entry : Entry) (state : SideState) :
    (liveIds (installPaid owner side splitStart paidId paidFamily base entry state)).Perm
      (liveIds (cutState side entry.key splitStart state) ++ [paidId]) := by
  let inside := (separateOuter side entry.key splitStart state).1.map Frozen.id
  let outside := (separateOuter side entry.key splitStart state).2.map Frozen.id
  let growing := state.grower.toList.map Grower.id
  have partition : (inside ++ outside).Perm ((cutList side entry.key splitStart state.shrinking).map Frozen.id) := by
    simpa only [List.map_append,inside,outside,separateOuter] using
      (List.filter_append_perm (blockInside side entry.key)
        (cutList side entry.key splitStart state.shrinking)).map Frozen.id
  have swap : (inside ++ [paidId] ++ outside ++ growing).Perm ((inside ++ outside) ++ growing ++ [paidId]) := by
    have commute : ([paidId] ++ (outside ++ growing)).Perm ((outside ++ growing) ++ [paidId]) := List.perm_append_comm
    simpa only [List.append_assoc] using commute.append_left inside
  have finish := (partition.append_right growing).append_right [paidId]
  have result := swap.trans finish
  simpa only [liveIds,installPaid,List.map_append,List.map_cons,List.map_nil,OrderedBlocks.singleton,inside,outside,growing,
    cutState] using result

theorem cutState_ids_below (side : Bool) (cut fresh : ℕ) (state : SideState)
    (below : ∀ id ∈ liveIds state, id<fresh) :
    ∀ id ∈ liveIds (cutState side cut fresh state), id < fresh+2*state.shrinking.length := by
  intro id member
  rcases List.mem_append.mp member with frozen | growing
  · obtain ⟨piece,pieceMem,rfl⟩ := List.mem_map.mp frozen
    rcases cutList_id_origin side cut fresh state.shrinking piece pieceMem with old | newRange
    · obtain ⟨old,oldMem,equal⟩ := old
      have bound := below old.id (List.mem_append_left _ (List.mem_map.mpr ⟨old,oldMem,rfl⟩))
      omega
    · exact newRange.2
  · have bound := below id (List.mem_append_right _ growing)
    omega

theorem conversion_ids_below (owner base start : ℕ) (state : SideState)
    (below : ∀ id ∈ liveIds state,id<start) :
    ∀ id ∈ liveIds (convert owner start start base state),id<start+1 := by
  intro id member
  rcases conversion_id_support owner start start base state id member with old | born
  · have bound := below id old
    omega
  · have equal := conversionIds_member start state id born
    omega

noncomputable def freshPaidNames (owner base start : ℕ) (state : SideState) : PaidNames :=
  let converted := convert owner start start base state
  let paid := start+1+2*converted.shrinking.length
  ⟨start,start,start+1,paid,paid⟩

noncomputable def freshPaidInsertion (owner : ℕ) (side : Bool) (base start : ℕ)
    (entry : Entry) (state : SideState) : SideState × ℕ :=
  let names := freshPaidNames owner base start state
  (paidInsertion owner side names.replacementFamily names.replacementId names.splitStart names.paidId names.paidFamily
    base entry state,names.paidId+1)

theorem freshPaidInsertion_local {owner base start : ℕ} (side : Bool) (entry : Entry) (state : SideState)
    (unique : (liveIds state).Nodup) (below : ∀ id ∈ liveIds state,id<start) :
    let result := freshPaidInsertion owner side base start entry state
    (liveIds result.1).Nodup ∧ (∀ id ∈ liveIds result.1,id<result.2) ∧ start≤result.2 := by
  let converted := convert owner start start base state
  let paid := start+1+2*converted.shrinking.length
  have convertedUnique : (liveIds converted).Nodup := conversion_ids_unique owner start start base state unique
    (by intro member;have bound := below start member;omega)
  have convertedBelow : ∀ id ∈ liveIds converted,id<start+1 := conversion_ids_below owner base start state below
  have cutUnique := cutState_ids_unique side entry.key (start+1) converted convertedUnique convertedBelow
  have cutBelow := cutState_ids_below side entry.key (start+1) converted convertedBelow
  have perm := installPaid_liveIds_perm owner side (start+1) paid paid base entry converted
  have targetUnique : (liveIds (cutState side entry.key (start+1) converted) ++ [paid]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨cutUnique,by simp,?_⟩
    intro first firstMem second secondMem equal
    have same := List.mem_singleton.mp secondMem
    have bound := cutBelow first firstMem
    change first < paid at bound
    omega
  refine ⟨perm.nodup_iff.mpr targetUnique,?_,?_⟩
  · intro id member
    have places := perm.mem_iff.mp member
    rcases List.mem_append.mp places with old | singleton
    · have bound := cutBelow id old
      change id < paid+1
      change id < paid at bound
      omega
    · have equal := List.mem_singleton.mp singleton
      change id < paid+1
      omega
  · change start≤paid+1
    dsimp [paid]
    omega

/-- Every new local id is either an old local id or falls in this insertion's
single reserved interval. This is sufficient for a global one-slot update. -/
theorem freshPaidInsertion_origin (owner : ℕ) (side : Bool) (base start : ℕ)
    (entry : Entry) (state : SideState) (id : ℕ)
    (member : id ∈ liveIds (freshPaidInsertion owner side base start entry state).1) :
    id ∈ liveIds state ∨ start ≤ id := by
  let names := freshPaidNames owner base start state
  rcases paidInsertion_id_support owner side names.replacementFamily names.replacementId names.splitStart
    names.paidId names.paidFamily base entry state id member with old | born
  · exact Or.inl old
  · right
    simp only [paidInsertionIds,List.mem_append,List.mem_singleton] at born
    rcases born with (conversion | cut) | paid
    · have equal := conversionIds_member _ _ _ conversion
      change id=start at equal
      omega
    · have range := (cutBirthIds_range entry.key names.splitStart _ id cut).1
      change start+1 ≤ id at range
      omega
    · change id=start+1+2*(convert owner start start base state).shrinking.length at paid
      omega

noncomputable def freshPaidSlot {slots : ℕ} (slot : Fin slots) (owner base : ℕ) (side : Bool)
    (start : ℕ) (entry : Entry) (states : Fin slots → SideState) : (Fin slots → SideState) × ℕ :=
  let result := freshPaidInsertion owner side base start entry (states slot)
  (Function.update states slot result.1,result.2)

theorem freshPaidSlot_inventory {slots : ℕ} (slot : Fin slots) (owner base : ℕ) (side : Bool)
    (start : ℕ) (entry : Entry) (states : Fin slots → SideState) (inventory : Inventory states start) :
    Inventory (freshPaidSlot slot owner base side start entry states).1
      (freshPaidSlot slot owner base side start entry states).2 := by
  let result := freshPaidInsertion owner side base start entry (states slot)
  have localSpec := freshPaidInsertion_local (owner:=owner) (base:=base) side entry (states slot) (inventory.localUnique slot) (inventory.below slot)
  have origin := freshPaidInsertion_origin owner side base start entry (states slot)
  change Inventory (Function.update states slot result.1) result.2
  refine ⟨?_,?_,?_⟩
  · intro current
    by_cases same : current=slot
    · subst current
      simpa only [Function.update_self] using localSpec.1
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
        · have oldBound := inventory.below second id secondMem
          omega
    · rw [Function.update_of_ne firstEq] at firstMem
      by_cases secondEq : second=slot
      · subst second
        rw [Function.update_self] at secondMem
        rcases origin id secondMem with old | fresh
        · exact inventory.locations first slot id firstMem old
        · have oldBound := inventory.below first id firstMem
          omega
      · rw [Function.update_of_ne secondEq] at secondMem
        exact inventory.locations first second id firstMem secondMem
  · intro current id member
    by_cases same : current=slot
    · subst current
      rw [Function.update_self] at member
      exact localSpec.2.1 id member
    · rw [Function.update_of_ne same] at member
      exact lt_of_lt_of_le (inventory.below current id member) localSpec.2.2

/-- Exact actual-birth list for the concrete reserved names. -/
noncomputable def freshPaidJournal (owner base start : ℕ) (entry : Entry) (state : SideState) : List ℕ :=
  let names := freshPaidNames owner base start state
  paidInsertionIds owner names.replacementFamily names.replacementId names.splitStart names.paidId base entry state

theorem freshPaidJournal_range (owner base start : ℕ) (side : Bool) (entry : Entry) (state : SideState)
    (id : ℕ) (member : id ∈ freshPaidJournal owner base start entry state) :
    start ≤ id ∧ id < (freshPaidInsertion owner side base start entry state).2 := by
  let converted := convert owner start start base state
  let paid := start+1+2*converted.shrinking.length
  change id ∈ conversionIds start state ++ cutBirthIds entry.key (start+1) converted.shrinking ++ [paid] at member
  change start ≤ id ∧ id < paid+1
  rcases List.mem_append.mp member with other | singleton
  · rcases List.mem_append.mp other with conversion | cut
    · have equal := conversionIds_member start state id conversion
      dsimp [paid]
      omega
    · have range := cutBirthIds_range entry.key (start+1) converted.shrinking id cut
      change start+1 ≤ id ∧ id < paid at range
      omega
  · have equal := List.mem_singleton.mp singleton
    dsimp [paid]
    omega

theorem freshPaidJournal_nodup (owner base start : ℕ) (side : Bool) (entry : Entry) (state : SideState)
    (unique : (liveIds state).Nodup) (below : ∀ id ∈ liveIds state,id<start) :
    (freshPaidJournal owner base start entry state).Nodup := by
  let converted := convert owner start start base state
  let paid := start+1+2*converted.shrinking.length
  have convertedUnique : (liveIds converted).Nodup := conversion_ids_unique owner start start base state unique
    (by intro member;have bound := below start member;omega)
  have convertedBelow : ∀ id ∈ liveIds converted,id<start+1 := conversion_ids_below owner base start state below
  have cutUnique := BirthJournal.cutBirthIds_nodup side entry.key (start+1) converted.shrinking
    (List.nodup_append.mp convertedUnique).1 (fun block member =>
      convertedBelow block.id (List.mem_append_left _ (List.mem_map.mpr ⟨block,member,rfl⟩)))
  have conversionUnique : (conversionIds start state).Nodup := by
    cases grower : state.grower with
    | none => simp [conversionIds,grower]
    | some old => by_cases empty : old.members=[] <;> simp [conversionIds,grower,empty]
  have prefixUnique : (conversionIds start state ++ cutBirthIds entry.key (start+1) converted.shrinking).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨conversionUnique,cutUnique,?_⟩
    intro first firstMem second secondMem equal
    have same := conversionIds_member start state first firstMem
    have range := cutBirthIds_range entry.key (start+1) converted.shrinking second secondMem
    omega
  change (conversionIds start state ++ cutBirthIds entry.key (start+1) converted.shrinking ++ [paid]).Nodup
  apply List.nodup_append.mpr
  refine ⟨prefixUnique,by simp,?_⟩
  intro first firstMem second secondMem equal
  have same := List.mem_singleton.mp secondMem
  rcases List.mem_append.mp firstMem with conversion | cut
  · have firstSame := conversionIds_member start state first conversion
    dsimp [paid] at same
    omega
  · have range := cutBirthIds_range entry.key (start+1) converted.shrinking first cut
    change start+1 ≤ first ∧ first < paid at range
    omega

#print axioms installPaid_liveIds_perm
#print axioms freshPaidInsertion_local
#print axioms freshPaidSlot_inventory
#print axioms freshPaidJournal_range
#print axioms freshPaidJournal_nodup

end GreedyMerge.FreshIds
