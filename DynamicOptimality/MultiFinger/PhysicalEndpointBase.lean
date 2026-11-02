import DynamicOptimality.MultiFinger.PhysicalHand
import DynamicOptimality.MultiFinger.HandEndpoint
import DynamicOptimality.MultiFinger.TendonDemote

/-! Physical implementation of one source endpoint edit.
The output carries the persistent queue inventory. A single bounded
marker region accounts for all physical changes, independently of the
source depth at which the edit occurs. -/

namespace DynamicOptimality.MultiFinger.PhysicalHand

open ChaCha.MTR
open Pointer (MarkedTree)
open TendonContents

variable {α : Type*}

def Implemented (before after : Hand α) : Prop :=
  ∀ (physical : MarkedTree α) (credit : Nat), Realizes before physical credit →
    ∃ next : MarkedTree α, ∃ nextCredit count : Nat,
      Realizes after next nextCredit ∧ RegionStep physical next count ∧
      count+nextCredit ≤ credit+14

theorem Realizes.node_nil {left right : Hand α} {key : α}
    {physical : MarkedTree α} {credit : Nat}
    (valid : Realizes (.node [] left key right) physical credit) :
    ∃ (a b : MarkedTree α) (lp rp : Nat), Realizes left a lp ∧ Realizes right b rp ∧
      physical = .node a key b ∧ credit = lp+rp := by
  cases valid with
  | node tendon valid leftRep rightRep =>
      have empty := Tendon.eq_empty valid
      subst tendon
      exact ⟨_,_,_,_,leftRep,rightRep,rfl,by simp⟩

theorem Implemented.left {before after : Hand α} (implementation : Implemented before after)
    (frames : List (Pointer.Frame α)) (key : α) (right : Hand α) :
    Implemented (.node frames before key right) (.node frames after key right) := by
  intro physical credit valid
  cases valid with
  | @node _ _ _ _ a b lp rp tendon valid leftRep rightRep =>
      obtain ⟨next,nextCredit,count,nextRep,step,paid⟩ := implementation a lp leftRep
      exact ⟨tendon.marked (.node next key b),nextCredit+rp+tendon.potential,count,
        .node tendon valid nextRep rightRep,(step.left key b).tendon tendon,by omega⟩

theorem Implemented.right {before after : Hand α} (implementation : Implemented before after)
    (frames : List (Pointer.Frame α)) (left : Hand α) (key : α) :
    Implemented (.node frames left key before) (.node frames left key after) := by
  intro physical credit valid
  cases valid with
  | @node _ _ _ _ a b lp rp tendon valid leftRep rightRep =>
      obtain ⟨next,nextCredit,count,nextRep,step,paid⟩ := implementation b rp rightRep
      exact ⟨tendon.marked (.node a key next),lp+nextCredit+tendon.potential,count,
        .node tendon valid leftRep nextRep,(step.right a key).tendon tendon,by omega⟩

theorem small_region (before after : MarkedTree α) {count : Nat}
    (oldSize : before.skeleton.size ≤ 3) (newSize : after.skeleton.size ≤ 3)
    (actual : SearchRotation.Rotations before.erase after.erase count) :
    RegionStep before after count := by
  let frame : RegionFrame α := ⟨[],[],[],[],rfl,rfl⟩
  exact ⟨frame,before,after,by simp [RegionFrame.Contains,frame],
    by simp [RegionFrame.Contains,frame],oldSize,newSize,actual⟩

theorem stump_promote (left right : RawTree α) (key : α) :
    Implemented (.stump (.node left key right)) (.node [] (.stump left) key (.stump right)) := by
  intro physical credit valid
  cases valid
  refine ⟨.node (.hole left) key (.hole right),0,0,?_,?_,by omega⟩
  · exact .node emptyTendon emptyTendon_valid (.stump left) (.stump right)
  · exact small_region _ _ (by simp [MarkedTree.skeleton,Tree.size])
      (by simp [MarkedTree.skeleton,Tree.size]) (.refl _)

theorem stump_demote (left right : RawTree α) (key : α) :
    Implemented (.node [] (.stump left) key (.stump right)) (.stump (.node left key right)) := by
  intro physical credit valid
  obtain ⟨a,b,lp,rp,leftRep,rightRep,rfl,rfl⟩ := valid.node_nil
  cases leftRep
  cases rightRep
  refine ⟨.hole (.node left key right),0,0,.stump _,?_,by omega⟩
  exact small_region _ _ (by simp [MarkedTree.skeleton,Tree.size])
    (by simp [MarkedTree.skeleton,Tree.size]) (.refl _)

end DynamicOptimality.MultiFinger.PhysicalHand
