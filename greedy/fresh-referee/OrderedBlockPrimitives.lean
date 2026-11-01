import Mathlib
import OffsetAndSingleton

/-!
Concrete list semantics for ordered side blocks. The members list is in
geometric inner-to-outer order; its Entry records carry immutable joined
timestamps and label snapshots. Chronological order can agree with or oppose
this geometric list order. No operation rewrites or sorts joined timestamps. A SideState structurally consists of a shrinking prefix and
one optional outer grower. Splits/whole transfers do not accept a grower.
The numerical base may be administratively rebased; it is not a history
snapshot. This module does not assume a macro-level execution certificate.
-/

namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)

structure Frozen where
  id : ℕ
  family : ℕ
  creator : ℕ
  base : ℕ
  members : List Entry

structure Grower where
  id : ℕ
  family : ℕ
  creator : ℕ
  members : List Entry

structure SideState where
  shrinking : List Frozen
  grower : Option Grower

def growerEntries : Option Grower → List Entry
  | none => []
  | some g => g.members

def frozenEntries (blocks : List Frozen) : List Entry := blocks.flatMap Frozen.members

def entries (state : SideState) : List Entry :=
  frozenEntries state.shrinking ++ growerEntries state.grower

def outward (goLeft : Bool) (first second : Entry) : Prop :=
  if goLeft then second.key < first.key else first.key < second.key

def onSide (owner : ℕ) (goLeft : Bool) (entry : Entry) : Prop :=
  if goLeft then entry.key < owner else owner < entry.key

/-- Pairwise order of the flattened side list enforces both no duplicates
and contiguous block intervals. The only grower is structurally outermost. -/
def Valid (owner : ℕ) (goLeft : Bool) (state : SideState) : Prop :=
  (entries state).Pairwise (outward goLeft) ∧
  (∀ e ∈ entries state, onSide owner goLeft e) ∧
  (∀ g, state.grower=some g → g.creator=owner)

def freeze (id : ℕ) (base : ℕ) (grower : Grower) : Frozen :=
  ⟨id,grower.family,grower.creator,base,grower.members⟩

def emptyGrower (owner family id : ℕ) : Grower := ⟨id,family,owner,[]⟩

/-- Conversion seals the old grower with its unchanged instance id and
installs one new empty grower. The supplied id names only that replacement;
the family allocator is independent of the logical-instance allocator. -/
def convert (owner freshFamily id : ℕ) (base : ℕ) (state : SideState) : SideState :=
  match state.grower with
  | none => state
  | some g => if g.members=[] then state
      else ⟨state.shrinking ++ [freeze g.id base g],some (emptyGrower owner freshFamily id)⟩

def conversionBirths (state : SideState) : ℕ :=
  match state.grower with
  | none => 0
  | some grower => if grower.members=[] then 0 else 1

def splitLeft (block : Frozen) (k : ℕ) : Frozen :=
  { block with members := block.members.take k }

def splitRight (newId : ℕ) (block : Frozen) (k : ℕ) : Frozen :=
  { block with id := newId, members := block.members.drop k }

/-- A logical split retires the input instance and gives both output
fragments fresh ids. Physical list length increases by one, but the birth
ledger counts both output instances, consistently with the PDF. -/
def splitFresh (leftId rightId : ℕ) (block : Frozen) (k : ℕ) : List Frozen :=
  [{ splitLeft block k with id := leftId }, splitRight rightId block k]

def splitFreshBirths : ℕ := 2

@[simp] theorem splitFresh_births : splitFreshBirths = 2 := rfl

def eraseMember (key : ℕ) (block : Frozen) : Frozen :=
  { block with members := block.members.filter (fun entry => entry.key != key) }

def rebase (base : ℕ) (block : Frozen) : Frozen := { block with base := base }

def singleton (id family creator : ℕ) (base : ℕ) (entry : Entry) : Frozen :=
  ⟨id,family,creator,base,[entry]⟩

@[simp] theorem frozenEntries_append (first second : List Frozen) :
    frozenEntries (first++second)=frozenEntries first++frozenEntries second := by
  simp [frozenEntries]

@[simp] theorem frozenEntries_singleton (block : Frozen) : frozenEntries [block]=block.members := by
  simp [frozenEntries]

@[simp] theorem conversion_entries (owner freshFamily id : ℕ) (base : ℕ) (state : SideState) :
    entries (convert owner freshFamily id base state)=entries state := by
  cases hg : state.grower with
  | none =>simp [convert,hg]
  | some grower =>
      by_cases he : grower.members=[]
      · simp [convert,hg,he]
      · simp [convert,hg,he,entries,growerEntries,freeze,emptyGrower,List.append_assoc]

theorem conversion_valid (owner freshFamily id : ℕ) (base : ℕ)
    (goLeft : Bool) (state : SideState) (h : Valid owner goLeft state) :
    Valid owner goLeft (convert owner freshFamily id base state) := by
  refine ⟨by simpa using h.1,by simpa using h.2.1,?_⟩
  intro grower hsome
  cases hg : state.grower with
  | none =>simpa [convert,hg] using h.2.2 grower (by simpa [convert,hg] using hsome)
  | some old =>
      by_cases he : old.members=[]
      · exact h.2.2 grower (by simpa [convert,hg,he] using hsome)
      · have heq : emptyGrower owner freshFamily id=grower := by simpa [convert,hg,he] using hsome
        rw [←heq];rfl

theorem conversion_preserves_old_instance (owner freshFamily freshId : ℕ) (base : ℕ)
    (state : SideState) (old : Grower) (same : state.grower = some old)
    (nonempty : old.members ≠ []) :
    (convert owner freshFamily freshId base state).shrinking =
      state.shrinking ++ [freeze old.id base old] ∧
    (convert owner freshFamily freshId base state).grower =
      some (emptyGrower owner freshFamily freshId) := by
  simp [convert, same, nonempty]

theorem conversion_births_exact (owner freshFamily id : ℕ) (base : ℕ) (state : SideState) :
    (convert owner freshFamily id base state).shrinking.length =
      state.shrinking.length + conversionBirths state := by
  cases hg : state.grower with
  | none =>simp [convert,conversionBirths,hg]
  | some grower =>
      by_cases he : grower.members=[] <;> simp [convert,conversionBirths,hg,he]

theorem frozen_split_histories (block : Frozen) (k newId : ℕ) :
    (splitLeft block k).members ++ (splitRight newId block k).members=block.members ∧
    (splitLeft block k).family=block.family ∧ (splitRight newId block k).family=block.family ∧
    (splitLeft block k).creator=block.creator ∧ (splitRight newId block k).creator=block.creator ∧
    (splitLeft block k).base=block.base ∧ (splitRight newId block k).base=block.base := by
  simp [splitLeft,splitRight]

theorem split_entries (pre post : List Frozen) (focus : Frozen)
    (grower : Option Grower) (k newId : ℕ) :
    entries ⟨pre++[splitLeft focus k,splitRight newId focus k]++post,grower⟩ =
      entries ⟨pre++[focus]++post,grower⟩ := by
  simp [entries,frozenEntries,splitLeft,splitRight,List.append_assoc]
  simp only [←List.append_assoc]
  rw [List.take_append_drop]

theorem split_valid (owner : ℕ) (goLeft : Bool) (pre post : List Frozen) (focus : Frozen)
    (grower : Option Grower) (k newId : ℕ)
    (h : Valid owner goLeft ⟨pre++[focus]++post,grower⟩) :
    Valid owner goLeft ⟨pre++[splitLeft focus k,splitRight newId focus k]++post,grower⟩ := by
  simpa only [Valid,split_entries] using h

theorem split_live_count_exact (pre post : List Frozen) (focus : Frozen) (k newId : ℕ) :
    (pre++[splitLeft focus k,splitRight newId focus k]++post).length =
      (pre++[focus]++post).length + 1 := by
  simp;omega

theorem splitFresh_histories (leftId rightId : ℕ) (block : Frozen) (k : ℕ) :
    frozenEntries (splitFresh leftId rightId block k) = block.members := by
  simp [splitFresh, frozenEntries, splitLeft, splitRight]

theorem splitFresh_entries (leftId rightId : ℕ) (pre post : List Frozen)
    (focus : Frozen) (grower : Option Grower) (k : ℕ) :
    entries ⟨pre ++ splitFresh leftId rightId focus k ++ post, grower⟩ =
      entries ⟨pre ++ [focus] ++ post, grower⟩ := by
  simp only [entries, frozenEntries_append, splitFresh_histories, frozenEntries_singleton]

theorem splitFresh_valid (owner leftId rightId : ℕ) (goLeft : Bool)
    (pre post : List Frozen) (focus : Frozen) (grower : Option Grower) (k : ℕ)
    (valid : Valid owner goLeft ⟨pre ++ [focus] ++ post, grower⟩) :
    Valid owner goLeft ⟨pre ++ splitFresh leftId rightId focus k ++ post, grower⟩ := by
  simpa only [Valid, splitFresh_entries] using valid

/-- Rebase changes no membership history and no family/creator identity. -/
theorem rebase_history (base : ℕ) (block : Frozen) :
    (rebase base block).members=block.members ∧
    (rebase base block).family=block.family ∧ (rebase base block).creator=block.creator ∧
    (rebase base block).id=block.id := by
  simp [rebase]

theorem erase_entries_sublist (pre post : List Frozen) (focus : Frozen)
    (grower : Option Grower) (key : ℕ) :
    (entries ⟨pre++[eraseMember key focus]++post,grower⟩).Sublist
      (entries ⟨pre++[focus]++post,grower⟩) := by
  have h : (focus.members.filter (fun entry => entry.key != key)).Sublist focus.members := List.filter_sublist
  simpa [entries,frozenEntries,eraseMember,List.append_assoc] using
    (h.append_left (frozenEntries pre)).append_right (frozenEntries post++growerEntries grower)

theorem erase_valid (owner : ℕ) (goLeft : Bool) (pre post : List Frozen) (focus : Frozen)
    (grower : Option Grower) (key : ℕ)
    (h : Valid owner goLeft ⟨pre++[focus]++post,grower⟩) :
    Valid owner goLeft ⟨pre++[eraseMember key focus]++post,grower⟩ := by
  have hs := erase_entries_sublist pre post focus grower key
  exact ⟨h.1.sublist hs,fun entry hentry => h.2.1 entry (hs.subset hentry),h.2.2⟩

/-- A whole transfer can only consume Frozen blocks. The source suffix
and receiving prefix are given in their current inner-to-outer order. -/
def transfer (sourcePrefix moved receiverPrefix : List Frozen)
    (sourceGrower receiverGrower : Option Grower) : SideState × SideState :=
  (⟨sourcePrefix,sourceGrower⟩,⟨receiverPrefix++moved,receiverGrower⟩)

theorem transfer_exact_histories (sourcePrefix moved receiverPrefix : List Frozen)
    (sourceGrower receiverGrower : Option Grower) :
    (frozenEntries sourcePrefix ++ frozenEntries (receiverPrefix++moved)).Perm
      (frozenEntries (sourcePrefix++moved) ++ frozenEntries receiverPrefix) := by
  simp only [frozenEntries_append]
  have hswap : (frozenEntries receiverPrefix++frozenEntries moved).Perm
      (frozenEntries moved++frozenEntries receiverPrefix) := List.perm_append_comm
  simpa only [List.append_assoc] using
    (List.Perm.refl (frozenEntries sourcePrefix)).append hswap

theorem transfer_births_zero (sourcePrefix moved receiverPrefix : List Frozen) :
    sourcePrefix.length+(receiverPrefix++moved).length =
      (sourcePrefix++moved).length+receiverPrefix.length := by
  simp;omega

/-- These local order premises are exactly the outer-segment geometry
proved in ComparatorOuterSegments. Growers are empty before the splice. -/
theorem transfer_valid (sourceOwner receiverOwner : ℕ) (goLeft : Bool)
    (sourcePrefix moved receiverPrefix : List Frozen)
    (sourceGrower receiverGrower : Option Grower)
    (sourceEmpty : growerEntries sourceGrower=[])
    (receiverEmpty : growerEntries receiverGrower=[])
    (sourceValid : Valid sourceOwner goLeft ⟨sourcePrefix++moved,sourceGrower⟩)
    (receiverValid : Valid receiverOwner goLeft ⟨receiverPrefix,receiverGrower⟩)
    (movedSide : ∀ entry ∈ frozenEntries moved, onSide receiverOwner goLeft entry)
    (outer : ∀ inside ∈ frozenEntries receiverPrefix, ∀ outside ∈ frozenEntries moved,
      outward goLeft inside outside) :
    Valid sourceOwner goLeft (transfer sourcePrefix moved receiverPrefix sourceGrower receiverGrower).1 ∧
    Valid receiverOwner goLeft (transfer sourcePrefix moved receiverPrefix sourceGrower receiverGrower).2 := by
  have sourceEntries : entries ⟨sourcePrefix++moved,sourceGrower⟩ =
      frozenEntries sourcePrefix++frozenEntries moved := by simp [entries,sourceEmpty]
  have receiverEntries : entries ⟨receiverPrefix,receiverGrower⟩ = frozenEntries receiverPrefix := by
    simp [entries,receiverEmpty]
  have hsourceOrder := sourceValid.1
  rw [sourceEntries,List.pairwise_append] at hsourceOrder
  constructor
  · refine ⟨?_,?_,sourceValid.2.2⟩
    · simpa [transfer,entries,sourceEmpty] using hsourceOrder.1
    · intro entry hentry
      apply sourceValid.2.1 entry
      have he : entry ∈ frozenEntries sourcePrefix := by simpa [transfer,entries,sourceEmpty] using hentry
      rw [sourceEntries]
      exact List.mem_append_left _ he
  · refine ⟨?_,?_,receiverValid.2.2⟩
    · have hp := List.pairwise_append.mpr ⟨by simpa [receiverEntries] using receiverValid.1,hsourceOrder.2.1,outer⟩
      simpa [transfer,entries,receiverEmpty] using hp
    · intro entry hentry
      have he : entry ∈ frozenEntries receiverPrefix++frozenEntries moved := by
        simpa [transfer,entries,receiverEmpty] using hentry
      rcases List.mem_append.mp he with h | h
      · exact receiverValid.2.1 entry (by simpa [receiverEntries] using h)
      · exact movedSide entry h

def grow (entry : Entry) (grower : Grower) : Grower :=
  { grower with members := grower.members++[entry] }

theorem grow_entries (shrinking : List Frozen) (grower : Grower) (entry : Entry) :
    entries ⟨shrinking,some (grow entry grower)⟩ = entries ⟨shrinking,some grower⟩++[entry] := by
  simp [entries,grow,growerEntries,List.append_assoc]

/-- A real inner-to-outer link extends only the outer grower, preserving
its creator/family and all previous immutable entry records. -/
theorem grow_valid (owner : ℕ) (goLeft : Bool) (shrinking : List Frozen)
    (grower : Grower) (entry : Entry)
    (h : Valid owner goLeft ⟨shrinking,some grower⟩)
    (entrySide : onSide owner goLeft entry)
    (outer : ∀ old ∈ entries ⟨shrinking,some grower⟩, outward goLeft old entry) :
    Valid owner goLeft ⟨shrinking,some (grow entry grower)⟩ := by
  refine ⟨?_,?_,?_⟩
  · rw [grow_entries]
    apply List.pairwise_append.mpr
    exact ⟨h.1,by simp,by simpa using outer⟩
  · intro old hmem
    rw [grow_entries] at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact h.2.1 old hmem
    · have heq : old=entry := by simpa using hmem
      simpa [heq] using entrySide
  · intro newGrower heq
    have hh : grow entry grower=newGrower := Option.some.inj heq
    rw [←hh]
    exact h.2.2 grower rfl

def paidInsert (pre post : List Frozen) (focus : Frozen) (grower : Option Grower)
    (k splitId paidId family creator : ℕ) (base : ℕ) (entry : Entry) : SideState :=
  ⟨pre++[splitLeft focus k,singleton paidId family creator base entry,
      splitRight splitId focus k]++post,grower⟩

theorem paid_insert_entries (pre post : List Frozen) (focus : Frozen) (grower : Option Grower)
    (k splitId paidId family creator : ℕ) (base : ℕ) (entry : Entry) :
    entries (paidInsert pre post focus grower k splitId paidId family creator base entry) =
      (frozenEntries pre++focus.members.take k) ++ entry::
        (focus.members.drop k++frozenEntries post++growerEntries grower) := by
  simp [paidInsert,entries,frozenEntries,splitLeft,splitRight,singleton,List.append_assoc]

/-- An arbitrary-position paid singleton preserves the outer grower.
Only one existing shrinking block is split and no histories are merged. -/
theorem paid_insert_valid (owner : ℕ) (goLeft : Bool)
    (pre post : List Frozen) (focus : Frozen) (grower : Option Grower)
    (k splitId paidId family creator : ℕ) (base : ℕ) (entry : Entry)
    (h : Valid owner goLeft ⟨pre++[focus]++post,grower⟩)
    (entrySide : onSide owner goLeft entry)
    (leftOrder : ∀ old ∈ frozenEntries pre++focus.members.take k, outward goLeft old entry)
    (rightOrder : ∀ old ∈ focus.members.drop k++frozenEntries post++growerEntries grower,
      outward goLeft entry old) :
    Valid owner goLeft (paidInsert pre post focus grower k splitId paidId family creator base entry) := by
  let beforeEntries := frozenEntries pre++focus.members.take k
  let afterEntries := focus.members.drop k++frozenEntries post++growerEntries grower
  have oldEntries : entries ⟨pre++[focus]++post,grower⟩=beforeEntries++afterEntries := by
    dsimp [beforeEntries,afterEntries]
    simp [entries,frozenEntries,List.append_assoc]
    simp only [←List.append_assoc]
    rw [List.take_append_drop]
  have horder := h.1
  rw [oldEntries,List.pairwise_append] at horder
  have newEntries : entries (paidInsert pre post focus grower k splitId paidId family creator base entry)=
      beforeEntries++entry::afterEntries := paid_insert_entries ..
  refine ⟨?_,?_,h.2.2⟩
  · rw [newEntries]
    apply List.pairwise_append.mpr
    refine ⟨horder.1,List.pairwise_cons.mpr ⟨rightOrder,horder.2.1⟩,?_⟩
    intro old hold other hother
    rcases List.mem_cons.mp hother with rfl | hother
    · exact leftOrder old hold
    · exact horder.2.2 old hold other hother
  · intro old hmem
    rw [newEntries] at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · apply h.2.1 old
      rw [oldEntries]
      exact List.mem_append_left _ hmem
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact entrySide
      · apply h.2.1 old
        rw [oldEntries]
        exact List.mem_append_right _ hmem

theorem paid_insert_live_count_exact (pre post : List Frozen) (focus : Frozen) (grower : Option Grower)
    (k splitId paidId family creator : ℕ) (base : ℕ) (entry : Entry) :
    (paidInsert pre post focus grower k splitId paidId family creator base entry).shrinking.length =
      (pre++[focus]++post).length+2 := by
  simp [paidInsert];omega

structure OwnerState where
  leftSide : SideState
  rightSide : SideState
  temporary : Option Grower

def growerCount (state : OwnerState) : ℕ :=
  (if state.leftSide.grower.isSome then 1 else 0) +
  (if state.rightSide.grower.isSome then 1 else 0) +
  (if state.temporary.isSome then 1 else 0)

/-- Two persistent side growers and at most one temporary paid grower.
The bound is enforced by the concrete representation, not a trace axiom. -/
theorem grower_count_le_three (state : OwnerState) : growerCount state≤3 := by
  unfold growerCount
  split_ifs <;> omega

def beginPaid (owner family id : ℕ) (entry : Entry) (state : OwnerState) : OwnerState :=
  { state with temporary := some ⟨id,family,owner,[entry]⟩ }

def finishPaid (state : OwnerState) : OwnerState := { state with temporary := none }

theorem temporary_paid_freezes_to_singleton (owner family id : ℕ) (base : ℕ) (entry : Entry) :
    freeze id base ⟨id,family,owner,[entry]⟩=singleton id family owner base entry := rfl

/-- A descendant block retains the creator, family, and exact immutable
entry records of one previous block; numerical bases and instance ids
are deliberately excluded from historical identity. -/
def Descends (after before : Frozen) : Prop :=
  after.family=before.family ∧ after.creator=before.creator ∧ after.members.Sublist before.members

theorem descends_refl (block : Frozen) : Descends block block :=
  ⟨rfl,rfl,List.Sublist.refl _⟩

theorem descends_trans {after middle before : Frozen}
    (first : Descends after middle) (second : Descends middle before) : Descends after before :=
  ⟨first.1.trans second.1,first.2.1.trans second.2.1,first.2.2.trans second.2.2⟩

theorem split_descends (block : Frozen) (k id : ℕ) :
    Descends (splitLeft block k) block ∧ Descends (splitRight id block k) block := by
  exact ⟨⟨rfl,rfl,List.take_sublist k block.members⟩,⟨rfl,rfl,List.drop_sublist k block.members⟩⟩

theorem erase_descends (block : Frozen) (key : ℕ) : Descends (eraseMember key block) block := by
  exact ⟨rfl,rfl,List.filter_sublist⟩

theorem rebase_descends (block : Frozen) (base : ℕ) : Descends (rebase base block) block :=
  ⟨rfl,rfl,List.Sublist.refl _⟩

/-- Chronological order is separate from geometric outward order.
The same member list may have joined timestamps increasing or decreasing;
this orientation belongs to the inherited family history. -/
def HistMonotone (timeIncreasesOutward : Bool) (members : List Entry) : Prop :=
  members.Pairwise (fun first second => if timeIncreasesOutward then
    first.joined < second.joined else second.joined < first.joined)

theorem descends_preserves_history_orientation {after before : Frozen}
    (descendant : Descends after before) (orientation : Bool)
    (history : HistMonotone orientation before.members) :
    HistMonotone orientation after.members := history.sublist descendant.2.2

/-- Both newly born logical split instances preserve the exact original
history records; reusing no old lifetime is consistent with the paper count. -/
theorem splitFresh_descends (leftId rightId : ℕ) (block : Frozen) (k : ℕ) :
    ∀ piece ∈ splitFresh leftId rightId block k, Descends piece block := by
  intro piece member
  simp only [splitFresh, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨rfl, rfl, List.take_sublist k block.members⟩
  · exact ⟨rfl, rfl, List.drop_sublist k block.members⟩

#print axioms conversion_valid
#print axioms split_valid
#print axioms erase_valid
#print axioms transfer_valid
#print axioms grow_valid
#print axioms paid_insert_valid
#print axioms grower_count_le_three
#print axioms splitFresh_descends
#print axioms descends_preserves_history_orientation

end GreedyMerge.OrderedBlocks
