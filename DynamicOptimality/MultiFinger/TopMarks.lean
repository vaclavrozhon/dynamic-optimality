import DynamicOptimality.MultiFinger.TopAccess

/-! # Promoting and demoting existing physical keys

A promotion marks the root of an existing gap. It adds one top-skeleton
key without changing the physical tree. At depth `d`, at most `d` old
ancestor ranks increase, each by at most the rank of the whole skeleton.
Demoting a marked leaf reverses the operation and never increases the
potential. Original BST keys are never inserted or deleted.
-/

namespace DynamicOptimality.MultiFinger.Top

open ChaCha.MTR
open Pointer (MarkedTree)
open ChaCha.Paper20261030.SplayAuxiliary (potential rank rank_mono)

variable {α : Type*}

def contextDepth : MarkedTree.Context α → Nat
  | .top => 0
  | .left _ _ inside => contextDepth inside+1
  | .right _ _ inside => contextDepth inside+1

theorem context_size_difference (context : MarkedTree.Context α)
    (before after : MarkedTree α) :
    (context.plug after).skeleton.size+before.skeleton.size =
      (context.plug before).skeleton.size+after.skeleton.size := by
  induction context with
  | top => simp only [MarkedTree.Context.plug]; omega
  | left parent right inside ih =>
      simp only [MarkedTree.Context.plug,MarkedTree.skeleton,Tree.size]
      omega
  | right left parent inside ih =>
      simp only [MarkedTree.Context.plug,MarkedTree.skeleton,Tree.size]
      omega

/-- A local potential allowance lifts through a context with one logarithm
per ancestor. No property of the opaque physical gaps is assumed. -/
theorem context_potential_change (context : MarkedTree.Context α)
    (before after : MarkedTree α) {credit capacity : Nat}
    (localBound : potential after.skeleton ≤ potential before.skeleton+credit)
    (fits : (context.plug after).skeleton.size ≤ capacity) :
    potential (context.plug after).skeleton ≤
      potential (context.plug before).skeleton+credit+contextDepth context*Nat.log 2 capacity := by
  induction context with
  | top => simpa [MarkedTree.Context.plug,contextDepth] using localBound
  | left parent right inside ih =>
      have inner := ih (by simp only [MarkedTree.Context.plug,MarkedTree.skeleton,Tree.size] at fits; omega)
      have rootBound : rank (ChaCha.MTR.Tree.node (inside.plug after).skeleton parent right.skeleton) ≤
          Nat.log 2 capacity := Nat.log_mono_right fits
      simp only [MarkedTree.Context.plug,MarkedTree.skeleton,potential,contextDepth,Nat.add_mul]
      omega
  | right left parent inside ih =>
      have inner := ih (by simp only [MarkedTree.Context.plug,MarkedTree.skeleton,Tree.size] at fits; omega)
      have rootBound : rank (ChaCha.MTR.Tree.node left.skeleton parent (inside.plug after).skeleton) ≤
          Nat.log 2 capacity := Nat.log_mono_right fits
      simp only [MarkedTree.Context.plug,MarkedTree.skeleton,potential,contextDepth,Nat.add_mul]
      omega

theorem context_potential_mono (context : MarkedTree.Context α)
    (before after : MarkedTree α)
    (smaller : after.skeleton.size ≤ before.skeleton.size)
    (cheaper : potential after.skeleton ≤ potential before.skeleton) :
    potential (context.plug after).skeleton ≤ potential (context.plug before).skeleton := by
  induction context with
  | top => exact cheaper
  | left parent right inside ih =>
      have sizes := context_size_difference inside before after
      have ranks := rank_mono (a := ChaCha.MTR.Tree.node (inside.plug after).skeleton parent right.skeleton)
        (b := ChaCha.MTR.Tree.node (inside.plug before).skeleton parent right.skeleton)
        (by simp only [Tree.size]; omega)
      simp only [MarkedTree.Context.plug,MarkedTree.skeleton,potential]
      omega
  | right left parent inside ih =>
      have sizes := context_size_difference inside before after
      have ranks := rank_mono (a := ChaCha.MTR.Tree.node left.skeleton parent (inside.plug after).skeleton)
        (b := ChaCha.MTR.Tree.node left.skeleton parent (inside.plug before).skeleton)
        (by simp only [Tree.size]; omega)
      simp only [MarkedTree.Context.plug,MarkedTree.skeleton,potential]
      omega

theorem promote (context : MarkedTree.Context α) (left right : RawTree α) (key : α)
    {capacity : Nat}
    (fits : (context.plug (.node (.hole left) key (.hole right))).skeleton.size ≤ capacity) :
    let before := context.plug (.hole (.node left key right))
    let after := context.plug (.node (.hole left) key (.hole right))
    after.erase = before.erase ∧ after.skeleton.size = before.skeleton.size+1 ∧
      2*potential after.skeleton ≤
        2*potential before.skeleton+2*contextDepth context*Nat.log 2 capacity := by
  dsimp only
  refine ⟨context.erase_congr rfl,?_,?_⟩
  · have sizes := context_size_difference context (.hole (.node left key right))
      (.node (.hole left) key (.hole right))
    simp only [MarkedTree.skeleton,Tree.size] at sizes
    omega
  · have bound := context_potential_change context (.hole (.node left key right))
      (.node (.hole left) key (.hole right)) (credit := 0) (by simp [potential,rank,MarkedTree.skeleton,Tree.size]) fits
    simp only [Nat.mul_assoc]
    omega

theorem demote (context : MarkedTree.Context α) (left right : RawTree α) (key : α) :
    let before := context.plug (.node (.hole left) key (.hole right))
    let after := context.plug (.hole (.node left key right))
    after.erase = before.erase ∧ after.skeleton.size+1 = before.skeleton.size ∧
      potential after.skeleton ≤ potential before.skeleton := by
  dsimp only
  refine ⟨context.erase_congr rfl,?_,?_⟩
  · have sizes := context_size_difference context (.hole (.node left key right))
      (.node (.hole left) key (.hole right))
    simp only [MarkedTree.skeleton,Tree.size] at sizes
    omega
  · exact context_potential_mono context _ _ (by simp [MarkedTree.skeleton,Tree.size])
      (by simp [MarkedTree.skeleton,potential,rank,Tree.size])

end DynamicOptimality.MultiFinger.Top
