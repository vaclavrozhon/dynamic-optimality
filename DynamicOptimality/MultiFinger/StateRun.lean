import DynamicOptimality.MultiFinger.StateInitialization
import DynamicOptimality.MultiFinger.StateMoves
import DynamicOptimality.MultiFinger.HandMoves
import DynamicOptimality.MultiFinger.RawTrace

/-! # Simulating the complete persistent-finger chronology

Each actual adjacent-edge movement changes at most two source endpoints.
Each request splays its occupied retained key. All intermediate physical
trees, top shapes, and tendon queues continue into the next operation.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR SearchRotation

def topCapacity (fingers : Nat) : Nat := 10*(fingers+2)

def operationAllowance (fingers : Nat) : Nat :=
  28+64*(1+Nat.log 2 (topCapacity fingers+4))

theorem State.move {reference : RawTree Nat} {fingers : Nat}
    {before after : Configuration reference fingers} (state : State before.hand)
    (step : Step before after) (ordered : reference.Ordered) (live : before.Live) :
    ∃ next : State after.hand, ∃ rotations : Nat,
      Rotations state.tree next.tree rotations ∧
      rotations+next.credit ≤ state.credit+operationAllowance fingers := by
  have distinct : reference.inorder.Nodup := ordered.imp (fun less => ne_of_lt less)
  obtain ⟨changes,small,edits⟩ := step.hand_endpointEdits distinct live
  change Hand.EndpointEdits before.hand after.hand changes at edits
  have capacity : 5*(before.hand.core.size+changes) ≤ topCapacity fingers := by
    have core := before.hand_size distinct
    unfold topCapacity
    omega
  have sourceOrdered : before.hand.source.Ordered := by rw [before.hand_source]; exact ordered
  obtain ⟨next,rotations,run,paid⟩ := state.endpoints edits sourceOrdered capacity
  have limit := Nat.mul_le_mul_right (14+32*(1+Nat.log 2 (topCapacity fingers+4))) small
  refine ⟨next,rotations,run,?_⟩
  unfold operationAllowance
  omega

theorem State.service {reference : RawTree Nat} {fingers : Nat}
    {source : Configuration reference fingers} (state : State source.hand)
    (ordered : reference.Ordered) (index : Fin fingers) (key : Nat)
    (found : (source.finger index).focus.rootKey = some key) :
    ∃ next : State source.hand, ∃ rotations : Nat,
      Rotations state.tree next.tree rotations ∧ next.tree.rootKey = some key ∧
      rotations+1+next.credit ≤ state.credit+operationAllowance fingers := by
  have distinct : reference.inorder.Nodup := ordered.imp (fun less => ne_of_lt less)
  have capacity : state.actual.skeleton.size ≤ topCapacity fingers := by
    have core := source.hand_size distinct
    have top := state.size
    unfold topCapacity
    omega
  have sourceOrdered : source.hand.source.Ordered := by rw [source.hand_source]; exact ordered
  obtain ⟨next,rotations,run,root,paid⟩ := state.expose key
    (source.hand_finger index found) sourceOrdered capacity
  have logBound : Nat.log 2 (topCapacity fingers) ≤ Nat.log 2 (topCapacity fingers+4) :=
    Nat.log_mono_right (by omega)
  refine ⟨next,rotations,run,root,?_⟩
  unfold operationAllowance
  omega

theorem Execution.simulate {reference : RawTree Nat} {fingers : Nat}
    {before after : Configuration reference fingers} {word : List Nat} {cost : Nat}
    (run : Execution before word after cost) (ordered : reference.Ordered)
    (live : before.Live) (state : State before.hand) :
    ∃ final : State after.hand, ∃ total : Nat,
      RawTrace state.tree word final.tree total ∧
      total+final.credit ≤ state.credit+cost*operationAllowance fingers := by
  induction run with
  | done source => exact ⟨state,0,.done state.tree,by simp⟩
  | @move before middle after word cost step rest ih =>
    obtain ⟨next,rotations,moves,moveBound⟩ := state.move step ordered live
    obtain ⟨final,total,trace,tailBound⟩ := ih (step.live live) next
    refine ⟨final,rotations+total,.rotate moves trace,?_⟩
    nlinarith
  | @serve before after word cost index key found rest ih =>
    obtain ⟨next,rotations,moves,root,serviceBound⟩ := state.service ordered index key found
    obtain ⟨final,total,trace,tailBound⟩ := ih live next
    refine ⟨final,rotations+(total+1),.rotate moves (.serve key root trace),?_⟩
    nlinarith

end DynamicOptimality.MultiFinger
