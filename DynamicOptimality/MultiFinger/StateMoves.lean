import DynamicOptimality.MultiFinger.State
import DynamicOptimality.MultiFinger.PhysicalEndpoint

/-! # Amortized physical realization of source endpoint changes

Only the small changed region is exposed in the actual top BST. Its new
canonical deque representation persists, while the top shape may change.
The bound includes both kinds of potential and composes without resets.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR SearchRotation

theorem State.endpoint {before after : Hand Nat} (state : State before)
    (edit : Hand.EndpointEdit before after) (ordered : before.source.Ordered)
    {capacity : Nat} (fits : state.actual.skeleton.size ≤ capacity) :
    ∃ next : State after, ∃ count : Nat,
      Rotations state.tree next.tree count ∧
      count+next.credit ≤ state.credit+14+32*(1+Nat.log 2 (capacity+4)) := by
  obtain ⟨canonical,queue,rawCount,valid,region,queuePaid⟩ := edit.realize state.representation
  obtain ⟨actual,count,equivalent,run,topPaid⟩ :=
    region.realize state.equivalent.symm (state.ordered ordered) fits
  let next : State after := ⟨canonical,queue,valid,actual,equivalent.symm⟩
  refine ⟨next,count,run,?_⟩
  change count+(2*ChaCha.Paper20261030.SplayAuxiliary.potential actual.skeleton+queue) ≤
    (2*ChaCha.Paper20261030.SplayAuxiliary.potential state.actual.skeleton+state.queueCredit)+
      14+32*(1+Nat.log 2 (capacity+4))
  omega

theorem State.endpoints {before after : Hand Nat} {changes : Nat} (state : State before)
    (edits : Hand.EndpointEdits before after changes) (ordered : before.source.Ordered)
    {capacity : Nat} (fits : 5*(before.core.size+changes) ≤ capacity) :
    ∃ next : State after, ∃ count : Nat,
      Rotations state.tree next.tree count ∧
      count+next.credit ≤ state.credit+changes*(14+32*(1+Nat.log 2 (capacity+4))) := by
  induction edits generalizing capacity with
  | refl hand => exact ⟨state,0,.refl state.tree,by simp⟩
  | @step before middle after changes edit rest ih =>
    have firstFits : state.actual.skeleton.size ≤ capacity := by
      have markers := state.size
      omega
    obtain ⟨middleState,firstCost,firstRun,firstPaid⟩ := state.endpoint edit ordered firstFits
    have middleOrdered : middle.source.Ordered := edit.source_eq ▸ ordered
    have middleFits : 5*(middle.core.size+changes) ≤ capacity := by
      have core := edit.core_sizes
      omega
    obtain ⟨last,lastCost,lastRun,lastPaid⟩ := ih middleState middleOrdered middleFits
    refine ⟨last,firstCost+lastCost,firstRun.append lastRun,?_⟩
    nlinarith

end DynamicOptimality.MultiFinger
