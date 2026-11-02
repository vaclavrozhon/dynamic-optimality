import DynamicOptimality.MultiFinger.PhysicalHand
import DynamicOptimality.MultiFinger.RegionExecution
import DynamicOptimality.MultiFinger.TopAccess

/-! # Persistent physical states for a source hand

The canonical representation keeps the concrete tendon deques. The actual
BST may have an arbitrary splayed top shape, but has exactly the same
marker word and the same ordered list of physical hanging subtrees.
Its potential combines the queue credit with twice the top-tree rank sum.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation
open ChaCha.Paper20261030.SplayAuxiliary (potential potential_le)

structure State (hand : Hand Nat) where
  canonical : MarkedTree Nat
  queueCredit : Nat
  representation : PhysicalHand.Realizes hand canonical queueCredit
  actual : MarkedTree Nat
  equivalent : DataEquivalent actual canonical

namespace State

variable {hand : Hand Nat}

def tree (state : State hand) : RawTree Nat := state.actual.erase

def credit (state : State hand) : Nat :=
  2*potential state.actual.skeleton+state.queueCredit

theorem word (state : State hand) : state.tree.inorder = hand.source.inorder :=
  state.equivalent.erase_word.trans state.representation.word

theorem size (state : State hand) : state.actual.skeleton.size ≤ 5*hand.core.size := by
  rw [state.equivalent.skeleton_size]
  exact state.representation.size

theorem ordered (state : State hand) (sourceOrdered : hand.source.Ordered) : state.tree.Ordered := by
  change state.tree.inorder.Pairwise (· < ·)
  rw [state.word]
  exact sourceOrdered

theorem core_mem (state : State hand) {key : Nat} (member : key ∈ hand.core.inorder) :
    key ∈ state.actual.skeleton.inorder := by
  rw [state.equivalent.1]
  exact state.representation.core_mem member

theorem initialization (hand : Hand Nat) :
    ∃ state : State hand, state.credit ≤
      10*hand.core.size*Nat.log 2 (5*hand.core.size)+4*hand.source.size := by
  obtain ⟨canonical,queue,representation,queueBound⟩ := PhysicalHand.initialization hand
  let state : State hand := ⟨canonical,queue,representation,canonical,.refl canonical⟩
  have markers := representation.size
  have top := potential_le canonical.skeleton (5*hand.core.size) markers
  have scaled := Nat.mul_le_mul_right (Nat.log 2 (5*hand.core.size)) markers
  have frames := PhysicalHand.framesCount_le hand
  refine ⟨state,?_⟩
  change 2*potential canonical.skeleton+queue ≤ _
  nlinarith

/-- A service exposes its actual retained key. All queue states and all
physical holes are retained, including after earlier top splays. -/
theorem expose (state : State hand) (key : Nat) (present : key ∈ hand.core.inorder)
    (sourceOrdered : hand.source.Ordered) {capacity : Nat}
    (fits : state.actual.skeleton.size ≤ capacity) :
    ∃ after : State hand, ∃ rotations : Nat,
      Rotations state.tree after.tree rotations ∧ after.tree.rootKey = some key ∧
      rotations+1+after.credit ≤ state.credit+6*Nat.log 2 capacity+2 := by
  have actualOrdered := state.ordered sourceOrdered
  have distinct : state.actual.erase.inorder.Nodup := actualOrdered.imp (fun less => ne_of_lt less)
  obtain ⟨actual,rotations,splay,holes,root,physicalRoot,moves,paid⟩ :=
    Top.expose state.actual key (Top.skeleton_nodup distinct) (state.core_mem present) fits
  have same : DataEquivalent actual state.canonical :=
    ⟨splay.inorder_eq.symm.trans state.equivalent.1,holes.trans state.equivalent.2⟩
  let after : State hand := ⟨state.canonical,state.queueCredit,state.representation,actual,same⟩
  refine ⟨after,rotations,moves,physicalRoot,?_⟩
  change rotations+1+(2*potential actual.skeleton+state.queueCredit) ≤
    (2*potential state.actual.skeleton+state.queueCredit)+6*Nat.log 2 capacity+2
  omega

end State
end DynamicOptimality.MultiFinger
