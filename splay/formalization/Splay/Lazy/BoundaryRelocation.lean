import Splay.Lazy.InsertionNormalization

namespace Splay.Lazy

/-- A boundary delete/reparent/insert execution with the original block IDs.
All counts refer to this same rich trace. -/
structure BoundaryRelocation {n : ℕ} (params : Interface.Parameters)
    (initial : State n) (sourceId destinationId : Interface.BlockId)
    (element : Element n) (afterView : HeapView n) where
  source : Block n
  sourceFound : initial.blocks[sourceId]? = some source
  sourceShrinking : source.mode = .shrinking
  destination : Block n
  destinationFound : initial.blocks[destinationId]? = some destination
  destinationGrowing : destination.mode = .growing
  elementMem : element ∈ source.elements
  intervalGap : ℤ
  final : State n
  events : List (Event n)
  trace : Trace params initial events final
  view_eq : final.view = afterView
  root_eq : final.view.root = initial.view.root
  rank_eq : final.view.rank = initial.view.rank
  assigned_iff : ∀ queried, queried ∈ final.allElements ↔ queried ∈ initial.allElements
  unpaired : ∀ queried, queried ≠ element →
    final.view.parent queried = initial.view.parent queried ∧
      final.view.side queried = initial.view.side queried
  destinationFirst : ∃ suffix, final.view.topDown destination.owner destination.side =
    element :: destination.elements ++ suffix
  blocks_eq : final.blocks =
    ((initial.delete sourceId element intervalGap).insert destinationId element).blocks
  values : final.ValuesRealizeGaps
  inserts : Interface.totalInserts (eraseOperations events) = 1
  increases : Interface.totalIncreases (eraseOperations events) ≤ 4 * params.valueBound
  events_eq :
    let detached := initial.delete sourceId element intervalGap
    let target := fun queried => Analysis.transientContractedGap (initial.view.rawGap queried) intervalGap
    let normalized := detached.adjustValues target (source.elements.erase element)
    events = [.operation (.delete sourceId element)] ++
      detached.adjustValuesEvents target (source.elements.erase element) ++ [.silent] ++
      (normalized.replaceView afterView).normalizedInsertEvents destinationId destination element

namespace State

/-- Relocate one shrinking-source element to the outermost growing position.
Only the detached element changes parent, and no interval is created. -/
theorem exists_boundaryRelocation {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    {sourceId destinationId : Interface.BlockId} {source destination : Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking)
    (destinationFound : state.blocks[destinationId]? = some destination)
    (destinationGrowing : destination.mode = .growing)
    (element : Element n) (member : element ∈ source.elements)
    (afterView : HeapView n) (ranks : afterView.rank = state.view.rank)
    (root : afterView.root = state.view.root)
    (unchanged : ∀ queried, queried ≠ element →
      afterView.parent queried = state.view.parent queried ∧
        afterView.side queried = state.view.side queried)
    (elementGap : 0 ≤ afterView.rawGap element)
    (bounded : Analysis.transientContractedGap (afterView.rawGap element) 0 ≤ params.valueBound)
    (first : ∃ suffix, afterView.topDown destination.owner destination.side =
      element :: destination.elements ++ suffix) :
    Nonempty (BoundaryRelocation params state sourceId destinationId element afterView) := by
  have different : destinationId ≠ sourceId := by
    intro equal
    rw [equal, sourceFound] at destinationFound
    have blocksEq := Option.some.inj destinationFound
    rw [blocksEq, destinationGrowing] at sourceShrinking
    contradiction
  obtain ⟨intervalGap, deletion, deletedValues, deletionInserts, deletionIncreases, _valueLe⟩ :=
    exists_normalizedDeletion valid values sourceFound sourceShrinking element member
  let detached := state.delete sourceId element intervalGap
  let target := fun queried => Analysis.transientContractedGap (state.view.rawGap queried) intervalGap
  let survivors := source.elements.erase element
  let normalized := detached.adjustValues target survivors
  let deleteEvents := [.operation (.delete sourceId element)] ++ detached.adjustValuesEvents target survivors
  have normalizedBlocks : normalized.blocks = detached.blocks := by simp [normalized]
  have normalizedView : normalized.view = state.view := by simp [normalized, detached, State.delete]
  have normalizedAssigned : normalized.allElements = state.allElements.erase element := by
    change normalized.blocks.flatMap Block.elements = _
    rw [normalizedBlocks]
    exact delete_allElements sourceId source element intervalGap sourceFound member valid.allElements_nodup
  have unassigned : element ∉ normalized.allElements := by
    rw [normalizedAssigned]
    exact valid.allElements_nodup.not_mem_erase
  have normalizedValid : normalized.Valid params := deletion.final_valid
  have afterRanks : afterView.rank = normalized.view.rank := by rw [normalizedView]; exact ranks
  have agreement : ∀ queried ∈ normalized.allElements,
      afterView.parent queried = normalized.view.parent queried ∧
        afterView.side queried = normalized.view.side queried := by
    intro queried assigned
    have notElement : queried ≠ element := by
      intro equal
      subst queried
      exact unassigned assigned
    rw [normalizedView]
    exact unchanged queried notElement
  let rebased := normalized.replaceView afterView
  have reparent := replaceView_step normalizedValid afterView afterRanks agreement
  have rebasedValues : rebased.ValuesRealizeGaps :=
    replaceView_valuesRealizeGaps deletedValues afterView afterRanks
      (by rw [normalizedView]; exact root) agreement
  have rebasedFound : rebased.blocks[destinationId]? = some destination := by
    change normalized.blocks[destinationId]? = some destination
    rw [normalizedBlocks]
    change (state.blocks.modify sourceId fun b => b.deleted element intervalGap)[destinationId]? = _
    rw [List.getElem?_modify]
    simp [Ne.symm different, destinationFound]
  have rebasedUnassigned : element ∉ rebased.allElements := unassigned
  obtain ⟨insertion, finalValues, insertionCount, insertionCost⟩ :=
    normalizedInsert_trace reparent.after_valid rebasedValues rebasedFound destinationGrowing
      element rebasedUnassigned elementGap bounded first
  let final := (rebased.adjustValue element
    (Analysis.transientContractedGap (afterView.rawGap element) 0)).insert destinationId element
  let events := deleteEvents ++ [.silent] ++ rebased.normalizedInsertEvents destinationId destination element
  have wholeTrace : Trace params state events final := by
    simpa only [events, deleteEvents, detached, target, survivors,
      final, rebased, replaceView, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
        (deletion.append (Trace.cons reparent insertion))
  have finalBlocks : final.blocks = ((state.delete sourceId element intervalGap).insert destinationId element).blocks := by
    simp only [final, State.insert, adjustValue_blocks]
    change normalized.blocks.modify destinationId (fun b => b.inserted element) = _
    rw [normalizedBlocks]
  have finalView : final.view = afterView := by
    simp [final, State.insert, rebased, replaceView]
  have assignedIff : ∀ queried, queried ∈ final.allElements ↔ queried ∈ state.allElements := by
    intro queried
    let prepared := rebased.adjustValue element (Analysis.transientContractedGap (afterView.rawGap element) 0)
    have preparedFound : prepared.blocks[destinationId]? = some destination := by
      simpa [prepared] using rebasedFound
    rw [Canonical.mem_insert_allElements_iff prepared destinationId destination element queried preparedFound]
    simp only [State.allElements, prepared, adjustValue_blocks]
    change (queried = element ∨ queried ∈ normalized.allElements) ↔ queried ∈ state.allElements
    rw [normalizedAssigned]
    constructor
    · rintro (rfl | survives)
      · exact State.mem_allElements_iff.mpr ⟨source, List.mem_of_getElem? sourceFound, member⟩
      · exact List.mem_of_mem_erase survives
    · intro assigned
      by_cases equal : queried = element
      · exact Or.inl equal
      · exact Or.inr ((List.mem_erase_of_ne equal).mpr assigned)
  refine ⟨{
    source, sourceFound, sourceShrinking, destination, destinationFound, destinationGrowing,
    elementMem := member, intervalGap, final, events, trace := wholeTrace,
    view_eq := finalView,
    root_eq := (congrArg HeapView.root finalView).trans root,
    rank_eq := (congrArg HeapView.rank finalView).trans ranks,
    assigned_iff := assignedIff,
    unpaired := by intro queried different; rw [finalView]; exact unchanged queried different,
    destinationFirst := by rw [finalView]; exact first,
    blocks_eq := finalBlocks,
    values := finalValues,
    inserts := ?_, increases := ?_, events_eq := rfl
  }⟩
  · have deletionCount : Interface.totalInserts (eraseOperations deleteEvents) = 0 := deletionInserts
    simp only [events, eraseOperations_append, Interface.totalInserts_append]
    rw [deletionCount, show Interface.totalInserts (eraseOperations [.silent]) = 0 from rfl,
      Nat.zero_add]
    exact insertionCount
  · have deletionCost : Interface.totalIncreases (eraseOperations deleteEvents) = 0 := deletionIncreases
    simp only [events, eraseOperations_append, Interface.totalIncreases_append]
    rw [deletionCost, show Interface.totalIncreases (eraseOperations [.silent]) = 0 from rfl,
      Nat.zero_add]
    exact insertionCost

end State
end Splay.Lazy
