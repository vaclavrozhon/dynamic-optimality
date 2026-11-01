import Splay.Lazy.Trace

namespace Splay.Lazy

private theorem map_modify_compatible {α β : Type*}
    (project : α → β) (update : α → α) (projectedUpdate : β → β)
    (compatible : ∀ value, project (update value) = projectedUpdate (project value))
    (values : List α) (index : ℕ) :
    (values.modify index update).map project =
      (values.map project).modify index projectedUpdate := by
  induction values generalizing index with
  | nil =>
      cases index <;> rfl
  | cons head tail ih =>
      cases index with
      | zero =>
          simp [compatible]
      | succ index =>
          simp [ih]

private theorem modify_id {α : Type*} (values : List α) (index : ℕ) :
    values.modify index (fun value => value) = values := by
  induction values generalizing index with
  | nil =>
      cases index <;> rfl
  | cons head tail ih =>
      cases index with
      | zero =>
          rfl
      | succ index =>
          simp [ih]

namespace IsSegment

theorem nil {α : Type*} (whole : List α) :
    IsSegment [] whole := by
  exact ⟨[], whole, by simp⟩

theorem take {α : Type*} {inside whole : List α}
    (segment : IsSegment inside whole) (count : ℕ) :
    IsSegment (inside.take count) whole := by
  obtain ⟨front, back, rfl⟩ := segment
  refine ⟨front, inside.drop count ++ back, ?_⟩
  simpa only [List.append_assoc] using
    congrArg (fun middle => front ++ middle ++ back)
      (List.take_append_drop count inside).symm

theorem drop {α : Type*} {inside whole : List α}
    (segment : IsSegment inside whole) (count : ℕ) :
    IsSegment (inside.drop count) whole := by
  obtain ⟨front, back, rfl⟩ := segment
  refine ⟨front ++ inside.take count, back, ?_⟩
  simpa only [List.append_assoc] using
    congrArg (fun middle => front ++ middle ++ back)
      (List.take_append_drop count inside).symm

end IsSegment

namespace Block

/-- Change only metadata erased by the abstract interface. -/
def withPlacement {n : ℕ} (block : Block n)
    (owner : Element n) (side : Side) (intervalGap : ℤ) : Block n :=
  { block with
    owner := owner
    side := side
    intervalGap := intervalGap }

@[simp]
theorem toInterface_withPlacement {n : ℕ} (block : Block n)
    (owner : Element n) (side : Side) (intervalGap : ℤ) :
    (block.withPlacement owner side intervalGap).toInterface =
      block.toInterface :=
  rfl

/-- Empty growing interval created for an owner and a side. -/
def emptyGrowing {n : ℕ} (owner : Element n) (side : Side) : Block n where
  creator := owner
  owner := owner
  side := side
  passCount := 0
  mode := .growing
  elements := []
  intervalGap := 0

theorem emptyGrowing_structurallyValid {n : ℕ}
    (view : HeapView n) (assigned : List (Element n))
    (owner : Element n) (side : Side) :
    (emptyGrowing owner side).StructurallyValid view assigned := by
  refine ⟨IsSegment.nil _, ?_, ?_⟩
  · intro _
    rfl
  · simp [GapValid, emptyGrowing]

/-- Prepend one newly attached element to a growing interval. -/
def inserted {n : ℕ} (block : Block n) (element : Element n) : Block n :=
  { block with elements := element :: block.elements }

@[simp]
theorem inserted_toInterface {n : ℕ} (block : Block n)
    (element : Element n) :
    (block.inserted element).toInterface =
      { block.toInterface with elements := element :: block.elements } :=
  rfl

theorem inserted_structurallyValid {n : ℕ}
    {view : HeapView n} {beforeAssigned afterAssigned : List (Element n)}
    {block : Block n} (valid : block.StructurallyValid view beforeAssigned)
    (growing : block.mode = .growing) (element : Element n)
    (elementGap : 0 ≤ view.rawGap element)
    (afterSegment :
      IsSegment (block.inserted element).elements
        (view.attachedTopDown afterAssigned block.owner block.side)) :
    (block.inserted element).StructurallyValid view afterAssigned := by
  refine ⟨afterSegment, ?_, ?_⟩
  · intro _
    exact valid.owner_eq_creator_of_growing growing
  · simp only [GapValid, inserted, growing]
    constructor
    · exact valid.growing_intervalGap_eq_zero growing
    · intro member hMember
      simp only [List.mem_cons] at hMember
      rcases hMember with rfl | hMember
      · exact elementGap
      · have hGap := valid.2.2
        simp only [GapValid, growing] at hGap
        exact hGap.2 member hMember

/--
Remove one element from a shrinking interval and store its recomputed signed
minimum gap. The extra gap parameter is necessary because erasing the old
minimizer can change the interval minimum.
-/
def deleted {n : ℕ} (block : Block n) (element : Element n)
    (intervalGap : ℤ) : Block n :=
  { block with
    elements := block.elements.erase element
    intervalGap := intervalGap }

@[simp]
theorem deleted_toInterface {n : ℕ} (block : Block n)
    (element : Element n) (intervalGap : ℤ) :
    (block.deleted element intervalGap).toInterface =
      { block.toInterface with elements := block.elements.erase element } :=
  rfl

theorem deleted_structurallyValid {n : ℕ}
    {view : HeapView n} {afterAssigned : List (Element n)}
    {block : Block n} (shrinking : block.mode = .shrinking)
    (element : Element n) (intervalGap : ℤ)
    (afterSegment :
      IsSegment (block.deleted element intervalGap).elements
        (view.attachedTopDown afterAssigned block.owner block.side))
    (gapValid : (block.deleted element intervalGap).GapValid view) :
    (block.deleted element intervalGap).StructurallyValid
      view afterAssigned := by
  refine ⟨afterSegment, ?_, gapValid⟩
  intro hGrowing
  simp [deleted, shrinking] at hGrowing

/-- Rich counterpart of converting a growing interval to shrinking. -/
def converted {n : ℕ} (block : Block n) (intervalGap : ℤ) : Block n :=
  { block with mode := .shrinking, intervalGap := intervalGap }

@[simp]
theorem converted_toInterface {n : ℕ} (block : Block n)
    (intervalGap : ℤ) :
    (block.converted intervalGap).toInterface =
      { block.toInterface with mode := .shrinking } :=
  rfl

theorem converted_structurallyValid {n : ℕ}
    {view : HeapView n} {assigned : List (Element n)}
    {block : Block n} {intervalGap : ℤ}
    (segment :
      IsSegment block.elements
        (view.attachedTopDown assigned block.owner block.side))
    (gapValid : (block.converted intervalGap).GapValid view) :
    (block.converted intervalGap).StructurallyValid view assigned := by
  refine ⟨segment, ?_, gapValid⟩
  intro hGrowing
  simp [converted] at hGrowing

/-- Empty source block retained by the abstract split operation. -/
def emptiedAfterSplit {n : ℕ} (block : Block n) : Block n :=
  { block with elements := [], intervalGap := 0 }

/-- Prefix block produced by a split, with its recomputed signed minimum. -/
def splitPrefix {n : ℕ} (block : Block n) (count : ℕ)
    (intervalGap : ℤ) : Block n :=
  { block with
    elements := block.elements.take count
    intervalGap := intervalGap }

/-- Suffix block produced by a split, with its recomputed signed minimum. -/
def splitSuffix {n : ℕ} (block : Block n) (count : ℕ)
    (intervalGap : ℤ) : Block n :=
  { block with
    elements := block.elements.drop count
    intervalGap := intervalGap }

@[simp]
theorem emptiedAfterSplit_toInterface {n : ℕ} (block : Block n) :
    block.emptiedAfterSplit.toInterface =
      { block.toInterface with elements := [] } :=
  rfl

@[simp]
theorem splitPrefix_toInterface {n : ℕ} (block : Block n)
    (count : ℕ) (intervalGap : ℤ) :
    (block.splitPrefix count intervalGap).toInterface =
      { block.toInterface with elements := block.elements.take count } :=
  rfl

@[simp]
theorem splitSuffix_toInterface {n : ℕ} (block : Block n)
    (count : ℕ) (intervalGap : ℤ) :
    (block.splitSuffix count intervalGap).toInterface =
      { block.toInterface with elements := block.elements.drop count } :=
  rfl

theorem emptiedAfterSplit_structurallyValid {n : ℕ}
    {view : HeapView n} {assigned : List (Element n)}
    {block : Block n} (shrinking : block.mode = .shrinking) :
    block.emptiedAfterSplit.StructurallyValid view assigned := by
  refine ⟨IsSegment.nil _, ?_, ?_⟩
  · intro hGrowing
    simp [emptiedAfterSplit, shrinking] at hGrowing
  · simp [GapValid, emptiedAfterSplit, shrinking]

theorem splitPrefix_structurallyValid {n : ℕ}
    {view : HeapView n} {assigned : List (Element n)}
    {block : Block n} (valid : block.StructurallyValid view assigned)
    (shrinking : block.mode = .shrinking) (count : ℕ) (intervalGap : ℤ)
    (gapValid : (block.splitPrefix count intervalGap).GapValid view) :
    (block.splitPrefix count intervalGap).StructurallyValid view assigned := by
  refine ⟨valid.1.take count, ?_, gapValid⟩
  intro hGrowing
  simp [splitPrefix, shrinking] at hGrowing

theorem splitSuffix_structurallyValid {n : ℕ}
    {view : HeapView n} {assigned : List (Element n)}
    {block : Block n} (valid : block.StructurallyValid view assigned)
    (shrinking : block.mode = .shrinking) (count : ℕ) (intervalGap : ℤ)
    (gapValid : (block.splitSuffix count intervalGap).GapValid view) :
    (block.splitSuffix count intervalGap).StructurallyValid view assigned := by
  refine ⟨valid.1.drop count, ?_, gapValid⟩
  intro hGrowing
  simp [splitSuffix, shrinking] at hGrowing

/-- Generic constructor for a valid nonempty shrinking interval. -/
theorem structurallyValid_shrinking {n : ℕ}
    {view : HeapView n} {assigned : List (Element n)} {block : Block n}
    (shrinking : block.mode = .shrinking)
    (nonempty : block.elements ≠ [])
    (segment :
      IsSegment block.elements
        (view.attachedTopDown assigned block.owner block.side))
    (minimum :
      Analysis.IsIntervalGap block.elements.toFinset view.rawGap
        block.intervalGap) :
    block.StructurallyValid view assigned := by
  refine ⟨segment, ?_, ?_⟩
  · intro hGrowing
    simp [shrinking] at hGrowing
  · simp only [GapValid, shrinking]
    exact Or.inr ⟨nonempty, minimum⟩

/-- Generic constructor for a valid empty shrinking administrative block. -/
theorem structurallyValid_empty_shrinking {n : ℕ}
    {view : HeapView n} {assigned : List (Element n)} {block : Block n}
    (shrinking : block.mode = .shrinking)
    (empty : block.elements = [])
    (zeroGap : block.intervalGap = 0) :
    block.StructurallyValid view assigned := by
  refine ⟨?_, ?_, ?_⟩
  · rw [empty]
    exact IsSegment.nil _
  · intro hGrowing
    simp [shrinking] at hGrowing
  · simp only [GapValid, shrinking]
    exact Or.inl ⟨empty, zeroGap⟩

/-- Generic constructor for a valid growing interval. -/
theorem structurallyValid_growing {n : ℕ}
    {view : HeapView n} {assigned : List (Element n)} {block : Block n}
    (growing : block.mode = .growing)
    (owner_eq : block.owner = block.creator)
    (segment :
      IsSegment block.elements
        (view.attachedTopDown assigned block.owner block.side))
    (zeroGap : block.intervalGap = 0)
    (raw_nonnegative :
      ∀ element ∈ block.elements, 0 ≤ view.rawGap element) :
    block.StructurallyValid view assigned := by
  refine ⟨segment, fun _ => owner_eq, ?_⟩
  simp only [GapValid, growing]
  exact ⟨zeroGap, raw_nonnegative⟩

/--
Structural validity depends only on which elements are assigned, not on the
order in which the global block list enumerates them.
-/
theorem structurallyValid_assigned_congr {n : ℕ}
    {view : HeapView n}
    {beforeAssigned afterAssigned : List (Element n)}
    {block : Block n}
    (valid : block.StructurallyValid view beforeAssigned)
    (membership :
      ∀ element, element ∈ beforeAssigned ↔ element ∈ afterAssigned) :
    block.StructurallyValid view afterAssigned := by
  have hAttached :
      view.attachedTopDown beforeAssigned block.owner block.side =
        view.attachedTopDown afterAssigned block.owner block.side := by
    unfold HeapView.attachedTopDown
    apply List.filter_congr
    intro element _
    exact decide_eq_decide.mpr (membership element)
  exact ⟨by simpa only [hAttached] using valid.1, valid.2⟩

/--
The signed-gap claim needed by the junction procedure: a singleton shrinking
interval is valid even if its sole raw gap is negative.
-/
theorem singleton_shrinking_gapValid {n : ℕ}
    (view : HeapView n) (block : Block n)
    (shrinking : block.mode = .shrinking)
    (element : Element n)
    (elements_eq : block.elements = [element])
    (gap_eq : block.intervalGap = view.rawGap element) :
    block.GapValid view := by
  simp only [GapValid, shrinking]
  right
  constructor
  · simp [elements_eq]
  · unfold Analysis.IsIntervalGap
    constructor
    · refine ⟨element, ?_, ?_⟩
      · simp [elements_eq]
      · exact gap_eq.symm
    · intro member hMember
      have hMemberEq : member = element := by
        simpa [elements_eq] using hMember
      subst member
      exact gap_eq.le

/--
Uniformly shifting all raw gaps in a nonempty shrinking interval, together
with its stored interval gap, preserves gap validity exactly.
-/
theorem shrinking_gapValid_of_uniform_shift {n : ℕ}
    {beforeView afterView : HeapView n} {beforeBlock afterBlock : Block n}
    {shift : ℤ}
    (beforeShrinking : beforeBlock.mode = .shrinking)
    (beforeValid : beforeBlock.GapValid beforeView)
    (sameMode : afterBlock.mode = beforeBlock.mode)
    (sameElements : afterBlock.elements = beforeBlock.elements)
    (nonempty : beforeBlock.elements ≠ [])
    (gapShift :
      afterBlock.intervalGap = beforeBlock.intervalGap + shift)
    (rawShift :
      ∀ element ∈ beforeBlock.elements,
        afterView.rawGap element = beforeView.rawGap element + shift) :
    afterBlock.GapValid afterView := by
  have hBeforeCases :
      (beforeBlock.elements = [] ∧ beforeBlock.intervalGap = 0) ∨
        (beforeBlock.elements ≠ [] ∧
          Analysis.IsIntervalGap beforeBlock.elements.toFinset
            beforeView.rawGap beforeBlock.intervalGap) := by
    simpa only [GapValid, beforeShrinking] using beforeValid
  have hBefore : beforeBlock.elements ≠ [] ∧
      Analysis.IsIntervalGap beforeBlock.elements.toFinset beforeView.rawGap
        beforeBlock.intervalGap := by
    rcases hBeforeCases with hEmpty | hNonempty
    · exact False.elim (nonempty hEmpty.1)
    · exact hNonempty
  have hShifted := hBefore.2.add_shift shift
  simp only [GapValid, sameMode, beforeShrinking]
  right
  constructor
  · simpa [sameElements] using nonempty
  · rw [sameElements, gapShift]
    unfold Analysis.IsIntervalGap at hShifted ⊢
    constructor
    · obtain ⟨minimizer, hMember, hAttains⟩ := hShifted.1
      refine ⟨minimizer, ?_, ?_⟩
      · simpa using hMember
      · rw [rawShift minimizer (by simpa using hMember)]
        simpa using hAttains
    · intro element hMember
      rw [rawShift element (by simpa using hMember)]
      exact hShifted.2 element (by simpa using hMember)

/--
The shrinking source after one pass. Losers are removed, the pass counter is
incremented, and the signed minimum is recomputed for the remaining segment.
-/
def afterPassSource {n : ℕ} (block : Block n)
    (matching : List (Interface.Pairing n)) (intervalGap : ℤ) : Block n :=
  { block with
    passCount := block.passCount + 1
    elements := Interface.removeLosers block.elements matching
    intervalGap := intervalGap }

@[simp]
theorem afterPassSource_toInterface {n : ℕ} (block : Block n)
    (matching : List (Interface.Pairing n)) (intervalGap : ℤ) :
    (block.afterPassSource matching intervalGap).toInterface =
      { block.toInterface with
        passCount := block.passCount + 1
        elements := Interface.removeLosers block.elements matching } :=
  rfl

theorem afterPassSource_structurallyValid {n : ℕ}
    {view : HeapView n} {afterAssigned : List (Element n)}
    {block : Block n} (shrinking : block.mode = .shrinking)
    (matching : List (Interface.Pairing n)) (intervalGap : ℤ)
    (afterSegment :
      IsSegment (block.afterPassSource matching intervalGap).elements
        (view.attachedTopDown afterAssigned block.owner block.side))
    (gapValid :
      (block.afterPassSource matching intervalGap).GapValid view) :
    (block.afterPassSource matching intervalGap).StructurallyValid
      view afterAssigned := by
  refine ⟨afterSegment, ?_, gapValid⟩
  intro hGrowing
  simp [afterPassSource, shrinking] at hGrowing

/-- The signed minimum stored by a shrinking pass source never needs to be
provided by a scheduler: it can be recomputed from the post-pass payload in
any target heap view. -/
theorem exists_afterPassSource_gapValid {n : ℕ}
    (view : HeapView n) (block : Block n)
    (shrinking : block.mode = .shrinking)
    (matching : List (Interface.Pairing n)) :
    ∃ intervalGap,
      (block.afterPassSource matching intervalGap).GapValid view := by
  let payload := Interface.removeLosers block.elements matching
  by_cases empty : payload = []
  · refine ⟨0, ?_⟩
    simp [GapValid, afterPassSource, shrinking, payload, empty]
  · obtain ⟨intervalGap, minimum⟩ :=
      exists_intervalGap view payload empty
    refine ⟨intervalGap, ?_⟩
    simpa [GapValid, afterPassSource, shrinking, payload, empty] using minimum

/-- Rich counterpart of prepending every pass loser at its destination. -/
def insertAtDestinations {n : ℕ} (blocks : List (Block n))
    (matching : List (Interface.Pairing n)) : List (Block n) :=
  matching.foldl
    (fun current pairing =>
      current.modify pairing.destination fun destination =>
        destination.inserted pairing.loser)
    blocks

@[simp]
theorem length_insertAtDestinations {n : ℕ} (blocks : List (Block n))
    (matching : List (Interface.Pairing n)) :
    (insertAtDestinations blocks matching).length = blocks.length := by
  induction matching generalizing blocks with
  | nil => rfl
  | cons pairing matching ih =>
      exact (ih (blocks.modify pairing.destination fun destination =>
        destination.inserted pairing.loser)).trans (List.length_modify ..)

/-- Updating destinations distinct from a queried block preserves that
block's exact stable lookup. -/
theorem getElem?_insertAtDestinations_of_ne {n : ℕ}
    (blocks : List (Block n)) (matching : List (Interface.Pairing n))
    (queried : Interface.BlockId)
    (destinationsNe : ∀ pairing ∈ matching,
      pairing.destination ≠ queried) :
    (insertAtDestinations blocks matching)[queried]? = blocks[queried]? := by
  induction matching generalizing blocks with
  | nil => rfl
  | cons pairing matching ih =>
      rw [show insertAtDestinations blocks (pairing :: matching) =
        insertAtDestinations
          (blocks.modify pairing.destination fun destination =>
            destination.inserted pairing.loser) matching by rfl]
      rw [ih]
      · rw [List.getElem?_modify]
        simp [destinationsNe pairing (by simp)]
      · intro later laterMember
        exact destinationsNe later (by simp [laterMember])

/-- With duplicate-free destination IDs, a selected destination is modified
exactly once and contains precisely its selected loser at the front. -/
theorem getElem?_insertAtDestinations_of_mem {n : ℕ}
    (blocks : List (Block n)) (matching : List (Interface.Pairing n))
    (destinationsNodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    (selected : Interface.Pairing n) (selectedMember : selected ∈ matching)
    (destination : Block n)
    (found : blocks[selected.destination]? = some destination) :
    (insertAtDestinations blocks matching)[selected.destination]? =
      some (destination.inserted selected.loser) := by
  induction matching generalizing blocks with
  | nil => simp at selectedMember
  | cons pairing matching ih =>
      have nodupFacts := List.nodup_cons.mp (by
        simpa only [List.map_cons] using destinationsNodup)
      simp only [List.mem_cons] at selectedMember
      rcases selectedMember with rfl | selectedTail
      · rw [show insertAtDestinations blocks (selected :: matching) =
          insertAtDestinations
            (blocks.modify selected.destination fun current =>
              current.inserted selected.loser) matching by rfl]
        rw [getElem?_insertAtDestinations_of_ne]
        · rw [List.getElem?_modify]
          simp [found]
        · intro later laterMember equal
          exact nodupFacts.1
            (List.mem_map.mpr ⟨later, laterMember, equal⟩)
      · rw [show insertAtDestinations blocks (pairing :: matching) =
          insertAtDestinations
            (blocks.modify pairing.destination fun current =>
              current.inserted pairing.loser) matching by rfl]
        apply ih (blocks := blocks.modify pairing.destination fun current =>
          current.inserted pairing.loser) nodupFacts.2 selectedTail
        rw [List.getElem?_modify]
        have different : selected.destination ≠ pairing.destination := by
          intro equal
          exact nodupFacts.1
            (List.mem_map.mpr ⟨selected, selectedTail, equal⟩)
        simp [different.symm, found]

theorem map_insertAtDestinations {n : ℕ} (blocks : List (Block n))
    (matching : List (Interface.Pairing n)) :
    (insertAtDestinations blocks matching).map Block.toInterface =
      Interface.insertAtDestinations (blocks.map Block.toInterface)
        matching := by
  unfold insertAtDestinations Interface.insertAtDestinations
  induction matching generalizing blocks with
  | nil =>
      rfl
  | cons pairing matching ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rw [map_modify_compatible Block.toInterface
        (fun destination => destination.inserted pairing.loser)
        (fun destination : Interface.Block n =>
          { destination with
            elements := pairing.loser :: destination.elements })
        (fun destination =>
          destination.inserted_toInterface pairing.loser)
        blocks pairing.destination]

/-- Exact rich block-list effect of a pass. -/
def passBlocks {n : ℕ} (blocks : List (Block n))
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n)) (sourceIntervalGap : ℤ) :
    List (Block n) :=
  let sourceAfter :=
    source.afterPassSource matching sourceIntervalGap
  let sourceUpdated := blocks.modify sourceId fun _ => sourceAfter
  insertAtDestinations sourceUpdated matching

@[simp]
theorem length_passBlocks {n : ℕ} (blocks : List (Block n))
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n)) (sourceIntervalGap : ℤ) :
    (passBlocks blocks sourceId source matching sourceIntervalGap).length =
      blocks.length := by
  simp [passBlocks]

/-- A selected pass destination is the old rich destination with exactly its
selected loser prepended. -/
theorem passBlocks_destination_getElem? {n : ℕ}
    (blocks : List (Block n)) (sourceId : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ)
    (destinationsNodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    (selected : Interface.Pairing n) (selectedMember : selected ∈ matching)
    (destination : Block n)
    (found : blocks[selected.destination]? = some destination)
    (destinationNeSource : selected.destination ≠ sourceId) :
    (passBlocks blocks sourceId source matching sourceIntervalGap)[
        selected.destination]? =
      some (destination.inserted selected.loser) := by
  unfold passBlocks
  apply getElem?_insertAtDestinations_of_mem _ matching destinationsNodup
    selected selectedMember destination
  rw [List.getElem?_modify]
  simp [destinationNeSource.symm, found]

/-- A block which is neither the pass source nor a destination is unchanged
at its stable identifier. -/
theorem passBlocks_getElem?_of_ne {n : ℕ}
    (blocks : List (Block n)) (sourceId queried : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) (queriedNeSource : queried ≠ sourceId)
    (queriedNeDestinations : ∀ pairing ∈ matching,
      pairing.destination ≠ queried) :
    (passBlocks blocks sourceId source matching sourceIntervalGap)[queried]? =
      blocks[queried]? := by
  unfold passBlocks
  rw [getElem?_insertAtDestinations_of_ne]
  · rw [List.getElem?_modify]
    simp [queriedNeSource.symm]
  · exact queriedNeDestinations

/-- A non-source block keeps all placement and creator metadata through a
pass; it may only acquire one selected loser at the front of its payload. -/
theorem passBlocks_preserves_metadata_of_ne_source {n : ℕ}
    (blocks : List (Block n)) (sourceId queried : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ)
    (destinationsNodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    {block : Block n} (found : blocks[queried]? = some block)
    (queriedNeSource : queried ≠ sourceId) :
    ∃ afterBlock,
      (passBlocks blocks sourceId source matching sourceIntervalGap)[queried]? =
          some afterBlock ∧
        afterBlock.mode = block.mode ∧
        afterBlock.creator = block.creator ∧
        afterBlock.owner = block.owner ∧
        afterBlock.side = block.side := by
  by_cases selected : ∃ pairing ∈ matching, pairing.destination = queried
  · obtain ⟨pairing, pairingMember, destinationEq⟩ := selected
    refine ⟨block.inserted pairing.loser, ?_, rfl, rfl, rfl, rfl⟩
    rw [← destinationEq]
    exact passBlocks_destination_getElem? blocks sourceId source matching
      sourceIntervalGap destinationsNodup pairing pairingMember block
      (by simpa only [destinationEq] using found)
      (destinationEq.trans_ne queriedNeSource)
  · refine ⟨block, ?_, rfl, rfl, rfl, rfl⟩
    rw [passBlocks_getElem?_of_ne blocks sourceId queried source matching
      sourceIntervalGap queriedNeSource]
    · exact found
    · intro pairing pairingMember equal
      exact selected ⟨pairing, pairingMember, equal⟩

/-- The shrinking source remains at its stable identifier after a pass;
destinations are required to be different from that identifier. -/
theorem passBlocks_source_getElem? {n : ℕ}
    (blocks : List (Block n)) (sourceId : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ)
    (found : blocks[sourceId]? = some source)
    (destinationsNe : ∀ pairing ∈ matching,
      pairing.destination ≠ sourceId) :
    (passBlocks blocks sourceId source matching
      sourceIntervalGap)[sourceId]? =
      some (source.afterPassSource matching sourceIntervalGap) := by
  unfold passBlocks
  rw [getElem?_insertAtDestinations_of_ne]
  · rw [List.getElem?_modify]
    simp [found]
  · exact destinationsNe

theorem map_passBlocks {n : ℕ} (blocks : List (Block n))
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n)) (sourceIntervalGap : ℤ) :
    (passBlocks blocks sourceId source matching sourceIntervalGap).map
        Block.toInterface =
      Interface.passBlocks (blocks.map Block.toInterface) sourceId
        source.toInterface matching := by
  unfold passBlocks Interface.passBlocks
  rw [map_insertAtDestinations]
  have hModify :=
    map_modify_compatible Block.toInterface
      (fun _ => source.afterPassSource matching sourceIntervalGap)
      (fun _ : Interface.Block n =>
        { source.toInterface with
          passCount := source.passCount + 1
          elements := Interface.removeLosers source.elements matching })
      (fun _ =>
        source.afterPassSource_toInterface matching sourceIntervalGap)
      blocks sourceId
  rw [hModify]
  rfl

/--
Move a rich interval without changing any interface-visible field. The caller
supplies the common signed gap shift forced by the change of heap parent.
-/
def transferred {n : ℕ} (block : Block n)
    (owner : Element n) (side : Side) (shift : ℤ) : Block n :=
  block.withPlacement owner side (block.intervalGap + shift)

@[simp]
theorem transferred_toInterface {n : ℕ} (block : Block n)
    (owner : Element n) (side : Side) (shift : ℤ) :
    (block.transferred owner side shift).toInterface =
      block.toInterface :=
  rfl

/--
Exact specification of a lazy-interval transfer.

The interface-visible identity, pass state, and membership do not change.
Only current placement changes, and every member's signed raw gap changes by
one common shift which is also applied to the interval gap.
-/
structure IsTransfer {n : ℕ}
    (beforeView afterView : HeapView n)
    (beforeBlock afterBlock : Block n) where
  shift : ℤ
  shrinking : beforeBlock.mode = .shrinking
  creator_eq : afterBlock.creator = beforeBlock.creator
  passCount_eq : afterBlock.passCount = beforeBlock.passCount
  mode_eq : afterBlock.mode = beforeBlock.mode
  elements_eq : afterBlock.elements = beforeBlock.elements
  intervalGap_eq :
    afterBlock.intervalGap = beforeBlock.intervalGap + shift
  rawGap_eq :
    ∀ element ∈ beforeBlock.elements,
      afterView.rawGap element = beforeView.rawGap element + shift

def transferred_isTransfer {n : ℕ}
    (beforeView afterView : HeapView n) (block : Block n)
    (owner : Element n) (side : Side) (shift : ℤ)
    (shrinking : block.mode = .shrinking)
    (rawGap_eq :
      ∀ element ∈ block.elements,
        afterView.rawGap element = beforeView.rawGap element + shift) :
    IsTransfer beforeView afterView block
      (block.transferred owner side shift) where
  shift := shift
  shrinking := shrinking
  creator_eq := rfl
  passCount_eq := rfl
  mode_eq := rfl
  elements_eq := rfl
  intervalGap_eq := rfl
  rawGap_eq := rawGap_eq

namespace IsTransfer

theorem toInterface_eq {n : ℕ}
    {beforeView afterView : HeapView n}
    {beforeBlock afterBlock : Block n}
    (transfer : IsTransfer beforeView afterView beforeBlock afterBlock) :
    afterBlock.toInterface = beforeBlock.toInterface := by
  rcases beforeBlock with
    ⟨beforeCreator, beforeOwner, beforeSide, beforePass,
      beforeMode, beforeElements, beforeGap⟩
  rcases afterBlock with
    ⟨afterCreator, afterOwner, afterSide, afterPass,
      afterMode, afterElements, afterGap⟩
  have hCreator : afterCreator = beforeCreator := transfer.creator_eq
  have hPass : afterPass = beforePass := transfer.passCount_eq
  have hMode : afterMode = beforeMode := transfer.mode_eq
  have hElements : afterElements = beforeElements := transfer.elements_eq
  subst afterCreator
  subst afterPass
  subst afterMode
  subst afterElements
  rfl

theorem contractedGap_eq {n : ℕ}
    {beforeView afterView : HeapView n}
    {beforeBlock afterBlock : Block n}
    (transfer : IsTransfer beforeView afterView beforeBlock afterBlock)
    {element : Element n} (member : element ∈ beforeBlock.elements) :
    Analysis.transientContractedGap
        (afterView.rawGap element) afterBlock.intervalGap =
      Analysis.transientContractedGap
        (beforeView.rawGap element) beforeBlock.intervalGap := by
  rw [transfer.rawGap_eq element member, transfer.intervalGap_eq]
  exact Analysis.transientContractedGap_add_shift _ _ _

theorem after_structurallyValid {n : ℕ}
    {beforeView afterView : HeapView n}
    {beforeAssigned afterAssigned : List (Element n)}
    {beforeBlock afterBlock : Block n}
    (transfer : IsTransfer beforeView afterView beforeBlock afterBlock)
    (beforeValid :
      beforeBlock.StructurallyValid beforeView beforeAssigned)
    (nonempty : beforeBlock.elements ≠ [])
    (afterSegment :
      IsSegment afterBlock.elements
        (afterView.attachedTopDown afterAssigned
          afterBlock.owner afterBlock.side)) :
    afterBlock.StructurallyValid afterView afterAssigned := by
  have afterShrinking : afterBlock.mode = .shrinking := by
    rw [transfer.mode_eq, transfer.shrinking]
  apply structurallyValid_shrinking afterShrinking
  · rw [transfer.elements_eq]
    exact nonempty
  · exact afterSegment
  · have hGap :=
      shrinking_gapValid_of_uniform_shift
        transfer.shrinking beforeValid.2.2 transfer.mode_eq
        transfer.elements_eq nonempty transfer.intervalGap_eq
        transfer.rawGap_eq
    simp only [GapValid, afterShrinking] at hGap
    rcases hGap with hEmpty | hNonempty
    · exfalso
      apply nonempty
      rw [← transfer.elements_eq]
      exact hEmpty.1
    · exact hNonempty.2

end IsTransfer

end Block

namespace State

/-- Apply one rich insertion to a growing interval. -/
def insert {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (element : Element n) : State n :=
  { state with
    blocks :=
      state.blocks.modify blockId fun block =>
        block.inserted element }

theorem insert_toInterface {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (element : Element n) :
    (state.insert blockId element).toInterface =
      { state.toInterface with
        blocks :=
          state.toInterface.blocks.modify blockId fun block =>
            { block with elements := element :: block.elements } } := by
  cases state with
  | mk view blocks value =>
      simp only [State.insert, State.toInterface]
      rw [map_modify_compatible Block.toInterface
        (fun block => block.inserted element)
        (fun block : Interface.Block n =>
          { block with elements := element :: block.elements })
        (fun block => block.inserted_toInterface element)
        blocks blockId]

theorem insert_effect {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (element : Element n)
    (found : state.toInterface.block? blockId = some block.toInterface)
    (growing : block.mode = .growing)
    (unassigned : element ∉ state.toInterface.allElements)
    (value_order :
      state.toInterface.value block.creator + 1 ≤
        state.toInterface.value element) :
    Interface.Effect params state.toInterface (.insert blockId element)
      (state.insert blockId element).toInterface := by
  apply Interface.Effect.insert found growing unassigned value_order
  · have hProjection := insert_toInterface state blockId element
    exact congrArg Interface.State.blocks hProjection
  · rfl

/--
Apply one rich deletion from a shrinking interval. The new signed interval gap
is supplied explicitly because the erased element may have attained the old
minimum.
-/
def delete {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (element : Element n)
    (intervalGap : ℤ) : State n :=
  { state with
    blocks :=
      state.blocks.modify blockId fun block =>
        block.deleted element intervalGap }

theorem delete_toInterface {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (element : Element n)
    (intervalGap : ℤ) :
    (state.delete blockId element intervalGap).toInterface =
      { state.toInterface with
        blocks :=
          state.toInterface.blocks.modify blockId fun block =>
            { block with elements := block.elements.erase element } } := by
  cases state with
  | mk view blocks value =>
      simp only [State.delete, State.toInterface]
      rw [map_modify_compatible Block.toInterface
        (fun block => block.deleted element intervalGap)
        (fun block : Interface.Block n =>
          { block with elements := block.elements.erase element })
        (fun block => block.deleted_toInterface element intervalGap)
        blocks blockId]

theorem delete_effect {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (element : Element n) (intervalGap : ℤ)
    (found : state.toInterface.block? blockId = some block.toInterface)
    (shrinking : block.mode = .shrinking)
    (present : element ∈ block.elements) :
    Interface.Effect params state.toInterface (.delete blockId element)
      (state.delete blockId element intervalGap).toInterface := by
  apply Interface.Effect.delete found shrinking present
  · have hProjection :=
      delete_toInterface state blockId element intervalGap
    exact congrArg Interface.State.blocks hProjection
  · rfl

/-- Apply one rich pass, including all destination insertions. -/
def pass {n : ℕ} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n)) (sourceIntervalGap : ℤ) :
    State n :=
  { state with
    blocks :=
      Block.passBlocks state.blocks sourceId source matching
        sourceIntervalGap }

theorem pass_toInterface {n : ℕ} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n)) (sourceIntervalGap : ℤ) :
    (state.pass sourceId source matching sourceIntervalGap).toInterface =
      { state.toInterface with
        blocks :=
          Interface.passBlocks state.toInterface.blocks sourceId
            source.toInterface matching } := by
  cases state with
  | mk view blocks value =>
      simp only [State.pass, State.toInterface]
      rw [Block.map_passBlocks]

theorem pass_effect {n : ℕ} {params : Interface.Parameters}
    (state : State n) (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n)) (sourceIntervalGap : ℤ)
    (found :
      state.toInterface.block? sourceId = some source.toInterface)
    (validMatching :
      Interface.MatchingValid params state.toInterface sourceId
        source.toInterface matching) :
    Interface.Effect params state.toInterface (.pass sourceId matching)
      (state.pass sourceId source matching sourceIntervalGap).toInterface := by
  apply Interface.Effect.pass found validMatching
  · have hProjection :=
      pass_toInterface state sourceId source matching sourceIntervalGap
    exact congrArg Interface.State.blocks hProjection
  · rfl

/-- Apply one rich pass while simultaneously installing the heap view after
the represented pair-ups.

The abstract interface intentionally erases heap parents, so this has exactly
the same visible effect as `State.pass`.  The richer operation is needed by
the splay realization: a pair-up both moves its loser to the winner's growing
interval and changes that loser's heap parent. -/
def passAtView {n : ℕ} (state : State n) (afterView : HeapView n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n)) (sourceIntervalGap : ℤ) :
    State n :=
  { state.pass sourceId source matching sourceIntervalGap with
    view := afterView }

@[simp]
theorem passAtView_view {n : ℕ} (state : State n)
    (afterView : HeapView n) (sourceId : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) :
    (state.passAtView afterView sourceId source matching
      sourceIntervalGap).view = afterView :=
  rfl

@[simp]
theorem passAtView_blocks {n : ℕ} (state : State n)
    (afterView : HeapView n) (sourceId : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) :
    (state.passAtView afterView sourceId source matching
      sourceIntervalGap).blocks =
        (state.pass sourceId source matching sourceIntervalGap).blocks :=
  rfl

@[simp]
theorem passAtView_value {n : ℕ} (state : State n)
    (afterView : HeapView n) (sourceId : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) :
    (state.passAtView afterView sourceId source matching
      sourceIntervalGap).value = state.value :=
  rfl

@[simp]
theorem passAtView_toInterface {n : ℕ} (state : State n)
    (afterView : HeapView n) (sourceId : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) :
    (state.passAtView afterView sourceId source matching
      sourceIntervalGap).toInterface =
        (state.pass sourceId source matching sourceIntervalGap).toInterface :=
  rfl

@[simp]
theorem passAtView_allElements {n : ℕ} (state : State n)
    (afterView : HeapView n) (sourceId : Interface.BlockId)
    (source : Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) :
    (state.passAtView afterView sourceId source matching
      sourceIntervalGap).allElements =
        (state.pass sourceId source matching sourceIntervalGap).allElements :=
  rfl

/-- Changing the rich heap view is invisible to the abstract `Pass` effect. -/
theorem passAtView_effect {n : ℕ} {params : Interface.Parameters}
    (state : State n) (afterView : HeapView n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n)) (sourceIntervalGap : ℤ)
    (found :
      state.toInterface.block? sourceId = some source.toInterface)
    (validMatching :
      Interface.MatchingValid params state.toInterface sourceId
        source.toInterface matching) :
    Interface.Effect params state.toInterface (.pass sourceId matching)
      (state.passAtView afterView sourceId source matching
        sourceIntervalGap).toInterface := by
  simpa only [passAtView_toInterface] using
    state.pass_effect sourceId source matching sourceIntervalGap found
      validMatching

/--
Interface-invisible state-level interval transfer. The heap view and rich
placement change together; creator, pass state, mode, and membership are
preserved exactly.
-/
def transfer {n : ℕ} (state : State n) (afterView : HeapView n)
    (blockId : Interface.BlockId) (owner : Element n) (side : Side)
    (shift : ℤ) : State n :=
  { state with
    view := afterView
    blocks :=
      state.blocks.modify blockId fun block =>
        block.transferred owner side shift }

@[simp]
theorem transfer_toInterface {n : ℕ} (state : State n)
    (afterView : HeapView n) (blockId : Interface.BlockId)
    (owner : Element n) (side : Side) (shift : ℤ) :
    (state.transfer afterView blockId owner side shift).toInterface =
      state.toInterface := by
  cases state with
  | mk view blocks value =>
      simp only [State.transfer, State.toInterface]
      rw [map_modify_compatible Block.toInterface
        (fun block => block.transferred owner side shift)
        (fun block : Interface.Block n => block)
        (fun block => block.transferred_toInterface owner side shift)
        blocks blockId]
      congr 1
      exact modify_id (blocks.map Block.toInterface) blockId

/-- Apply a rich conversion at one stable block identifier. -/
def convert {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (intervalGap : ℤ) : State n :=
  { state with
    blocks :=
      state.blocks.modify blockId fun block =>
        block.converted intervalGap }

theorem convert_toInterface {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (intervalGap : ℤ) :
    (state.convert blockId intervalGap).toInterface =
      { state.toInterface with
        blocks :=
          state.toInterface.blocks.modify blockId fun block =>
            { block with mode := .shrinking } } := by
  cases state with
  | mk view blocks value =>
      simp only [State.convert, State.toInterface]
      rw [map_modify_compatible Block.toInterface
        (fun block => block.converted intervalGap)
        (fun block : Interface.Block n => { block with mode := .shrinking })
        (fun block => block.converted_toInterface intervalGap)
        blocks blockId]

theorem convert_effect {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (intervalGap : ℤ)
    (found : state.toInterface.block? blockId = some block.toInterface)
    (growing : block.mode = .growing) :
    Interface.Effect params state.toInterface (.convert blockId)
      (state.convert blockId intervalGap).toInterface := by
  apply Interface.Effect.convert found growing
  · have hProjection := convert_toInterface state blockId intervalGap
    exact congrArg Interface.State.blocks hProjection
  · rfl

/-- Append a rich empty growing interval. -/
def create {n : ℕ} (state : State n)
    (creator : Element n) (side : Side) : State n :=
  { state with blocks := state.blocks ++ [Block.emptyGrowing creator side] }

theorem create_toInterface {n : ℕ} (state : State n)
    (creator : Element n) (side : Side) :
    (state.create creator side).toInterface =
      { state.toInterface with
        blocks :=
          state.toInterface.blocks ++
            [{ creator := creator
               passCount := 0
               mode := .growing
               elements := [] }] } := by
  cases state with
  | mk view blocks value =>
      simp [State.create, State.toInterface, Block.emptyGrowing,
        Block.toInterface]

theorem create_effect {n : ℕ} {params : Interface.Parameters}
    (state : State n) (creator : Element n) (side : Side)
    (room :
      state.toInterface.growingCount creator < params.growingLimit) :
    Interface.Effect params state.toInterface (.create creator)
      (state.create creator side).toInterface := by
  apply Interface.Effect.create room
  · have hProjection := create_toInterface state creator side
    exact congrArg Interface.State.blocks hProjection
  · rfl

@[simp]
theorem create_allElements {n : ℕ} (state : State n)
    (creator : Element n) (side : Side) :
    (state.create creator side).allElements = state.allElements := by
  simp [State.create, State.allElements, Block.emptyGrowing]

theorem create_interfaceValid {n : ℕ}
    {params : Interface.Parameters}
    (state : State n) (creator : Element n) (side : Side)
    (valid : state.Valid params)
    (room :
      state.toInterface.growingCount creator < params.growingLimit) :
    (state.create creator side).toInterface.Valid params := by
  have beforeValid := valid.1
  rw [create_toInterface]
  constructor
  · simpa [Interface.State.allElements] using beforeValid.1
  constructor
  · exact beforeValid.2.1
  · intro queried
    by_cases hCreator : creator = queried
    · subst queried
      have hRoom :
          state.toInterface.growingCount creator + 1 ≤
            params.growingLimit :=
        Nat.succ_le_iff.mpr room
      simpa [Interface.State.growingCount] using hRoom
    · have hOld := beforeValid.2.2 queried
      simpa [Interface.State.growingCount, hCreator] using hOld

/--
Creating an empty growing interval preserves the complete rich transient
invariant; no extra structural side condition is needed.
-/
theorem create_valid {n : ℕ} {params : Interface.Parameters}
    (state : State n) (creator : Element n) (side : Side)
    (valid : state.Valid params)
    (room :
      state.toInterface.growingCount creator < params.growingLimit) :
    (state.create creator side).Valid params := by
  refine ⟨create_interfaceValid state creator side valid room, ?_⟩
  intro block hBlock
  simp only [State.create, List.mem_append, List.mem_singleton] at hBlock
  change
    block.StructurallyValid state.view
      (state.create creator side).allElements
  rw [create_allElements]
  rcases hBlock with hOld | rfl
  · exact valid.2 block hOld
  · exact
      Block.emptyGrowing_structurallyValid
        state.view state.allElements creator side

/-- Rich block-list effect of the abstract split operation. -/
def splitBlocks {n : ℕ} (blocks : List (Block n))
    (sourceId : Interface.BlockId) (source : Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ) : List (Block n) :=
  let oldEmptied :=
    blocks.modify sourceId fun current => current.emptiedAfterSplit
  oldEmptied ++
    [source.splitPrefix prefixLength prefixGap,
      source.splitSuffix prefixLength suffixGap]

/-- Apply a rich split without changing the heap view or interface values. -/
def split {n : ℕ} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ) : State n :=
  { state with
    blocks :=
      splitBlocks state.blocks sourceId source prefixLength
        prefixGap suffixGap }

theorem map_splitBlocks {n : ℕ} (blocks : List (Block n))
    (sourceId : Interface.BlockId) (source : Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ) :
    (splitBlocks blocks sourceId source prefixLength prefixGap suffixGap).map
        Block.toInterface =
      Interface.splitBlocks (blocks.map Block.toInterface) sourceId
        source.toInterface prefixLength := by
  unfold splitBlocks Interface.splitBlocks
  rw [List.map_append]
  have hModify :=
    map_modify_compatible Block.toInterface Block.emptiedAfterSplit
      (fun current : Interface.Block n => { current with elements := [] })
      (fun current => current.emptiedAfterSplit_toInterface)
      blocks sourceId
  rw [hModify]
  rfl

theorem split_toInterface {n : ℕ} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ) :
    (state.split sourceId source prefixLength prefixGap suffixGap).toInterface =
      { state.toInterface with
        blocks :=
          Interface.splitBlocks state.toInterface.blocks sourceId
            source.toInterface prefixLength } := by
  cases state with
  | mk view blocks value =>
      simp only [State.split, State.toInterface]
      rw [map_splitBlocks]

theorem split_effect {n : ℕ} {params : Interface.Parameters}
    (state : State n) (sourceId : Interface.BlockId) (source : Block n)
    (prefixLength : ℕ) (prefixGap suffixGap : ℤ)
    (found :
      state.toInterface.block? sourceId = some source.toInterface)
    (shrinking : source.mode = .shrinking)
    (prefix_le : prefixLength ≤ source.elements.length) :
    Interface.Effect params state.toInterface
      (.split sourceId prefixLength)
      (state.split sourceId source prefixLength prefixGap suffixGap).toInterface := by
  apply Interface.Effect.split found shrinking prefix_le
  · have hProjection :=
      split_toInterface state sourceId source prefixLength prefixGap suffixGap
    exact congrArg Interface.State.blocks hProjection
  · rfl

end State

namespace Step

/-- Build a visible rich step from endpoint validity and the exact effect. -/
theorem operation {n : ℕ} {params : Interface.Parameters}
    {before after : State n} {operation : Interface.Operation n}
    (beforeValid : before.Valid params)
    (afterValid : after.Valid params)
    (effect :
      Interface.Effect params before.toInterface operation after.toInterface) :
    Step params before (.operation operation) after :=
  ⟨beforeValid, afterValid, effect⟩

/-- Build an interface-invisible rich step. -/
theorem silent {n : ℕ} {params : Interface.Parameters}
    {before after : State n}
    (beforeValid : before.Valid params)
    (afterValid : after.Valid params)
    (projection_eq : before.toInterface = after.toInterface) :
    Step params before .silent after :=
  ⟨beforeValid, afterValid, projection_eq⟩

end Step

end Splay.Lazy
