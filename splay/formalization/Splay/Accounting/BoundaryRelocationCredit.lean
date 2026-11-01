import Splay.Accounting.ArticleBoundaryRelocationFootprint
import Splay.Accounting.BoundaryCreditHistory
import Splay.Lazy.CanonicalBlockCount

namespace Splay.Lazy

/-- A surviving shrinking residence lies in its unique original block.
This transports size bounds even when earlier pairings removed other elements. -/
theorem State.ShrinkingRefinement.elements_sublist_of_common_element
    {n : ℕ} {params : Interface.Parameters} {active : Element n → Prop}
    {before after : State n} (refinement : State.ShrinkingRefinement active before after)
    (valid : before.Valid params) {oldId nextId : Interface.BlockId} {old next : Block n}
    {element : Element n} (oldFound : before.blocks[oldId]? = some old)
    (oldMember : element ∈ old.elements) (nextFound : after.blocks[nextId]? = some next)
    (shrinking : next.mode = .shrinking) (nextMember : element ∈ next.elements) :
    next.elements.Sublist old.elements := by
  obtain ⟨origin, originFound, _, _, _, _, sublist, _⟩ := refinement nextId next nextFound shrinking
  have ids := valid.blockId_eq_of_element_mem originFound (sublist.subset nextMember) oldFound oldMember
  rw [ids, oldFound] at originFound
  have equal := Option.some.inj originFound
  simpa only [equal] using sublist

theorem BoundaryRelocation.boundaryCredit_drop {n cutoff : ℕ} {params : Interface.Parameters}
    {initial : State n} {sourceId destinationId : Interface.BlockId}
    {element : Element n} {view : HeapView n}
    (relocation : BoundaryRelocation params initial sourceId destinationId element view) :
    Interface.boundaryCredit cutoff relocation.final.toInterface +
      (if relocation.source.elements.length ≤ 12 then 1 else 0) ≤
        Interface.boundaryCredit cutoff initial.toInterface := by
  obtain ⟨charge, history⟩ := Interface.BoundaryCreditHistory.lift relocation.trace.toInterface cutoff
  have bound := history.credit_bound
  have growth := relocation.trace.blocks_length_eq
  rw [relocation.blocks_length_eq] at growth
  have growthZero : Interface.totalBlockGrowth (eraseOperations relocation.events) = 0 := by omega
  rw [growthZero, Nat.mul_zero, Nat.add_zero] at bound
  have shape : ∃ suffix, eraseOperations relocation.events = Interface.Operation.delete sourceId element :: suffix := by
    rw [relocation.events_eq]
    simp only [eraseOperations_append, eraseOperations, Event.operations, List.flatMap_cons,
      List.flatMap_nil, List.singleton_append, List.cons_append, List.nil_append]
    exact ⟨_, rfl⟩
  obtain ⟨suffix, shape⟩ := shape
  rw [shape] at history
  have found : initial.toInterface.block? sourceId = some relocation.source.toInterface := by
    unfold Interface.State.block? State.toInterface
    simpa using congrArg (Option.map Block.toInterface) relocation.sourceFound
  cases history with
  | cons head tail =>
    simp only [Interface.boundaryOperationCharge, found] at bound
    change Interface.boundaryCredit cutoff relocation.final.toInterface +
      ((if relocation.source.elements.length ≤ 12 then 1 else 0) + _) ≤
        Interface.boundaryCredit cutoff initial.toInterface at bound
    omega

end Splay.Lazy
