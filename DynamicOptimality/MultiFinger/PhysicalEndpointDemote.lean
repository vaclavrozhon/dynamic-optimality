import DynamicOptimality.MultiFinger.PhysicalEndpointPromote

namespace DynamicOptimality.MultiFinger.PhysicalHand

open ChaCha.MTR
open Pointer (MarkedTree)
open TendonContents

variable {α : Type*}

theorem outer_right_demote (frames : List (Pointer.Frame α)) (left right : Hand α)
    (key parent : α) (gap : RawTree α) :
    Implemented (.node [] (.stump gap) parent (.node frames left key right))
      (.node (frames++[.right gap parent]) left key right) := by
  intro physical credit valid
  obtain ⟨a,b,lp,rp,leftRep,rightRep,rfl,rfl⟩ := valid.node_nil
  cases leftRep
  cases rightRep with
  | @node _ _ _ _ a b lp rp tendon tendonValid childLeft childRight =>
      obtain ⟨after,count,afterValid,step,paid⟩ := tendon.outer_right_push gap parent tendonValid (.node a key b)
      exact ⟨after.marked (.node a key b),lp+rp+after.potential,count,
        .node after afterValid childLeft childRight,step,by omega⟩

theorem outer_left_demote (frames : List (Pointer.Frame α)) (left right : Hand α)
    (key parent : α) (gap : RawTree α) :
    Implemented (.node [] (.node frames left key right) parent (.stump gap))
      (.node (frames++[.left parent gap]) left key right) := by
  intro physical credit valid
  obtain ⟨a,b,lp,rp,leftRep,rightRep,rfl,rfl⟩ := valid.node_nil
  cases rightRep
  cases leftRep with
  | @node _ _ _ _ a b lp rp tendon tendonValid childLeft childRight =>
      obtain ⟨after,count,afterValid,step,paid⟩ := tendon.outer_left_push gap parent tendonValid (.node a key b)
      exact ⟨after.marked (.node a key b),lp+rp+after.potential,count,
        .node after afterValid childLeft childRight,step,by omega⟩

theorem inner_left_demote (frames : List (Pointer.Frame α)) (left right : Hand α)
    (key parent : α) (gap : RawTree α) :
    Implemented (.node frames (.node [] left key right) parent (.stump gap))
      (.node (.left parent gap::frames) left key right) := by
  intro physical credit valid
  cases valid with
  | @node _ _ _ _ a b lp rp tendon tendonValid childLeft childRight =>
      cases childRight
      obtain ⟨ia,ib,ilp,irp,innerLeft,innerRight,rfl,rfl⟩ := childLeft.node_nil
      obtain ⟨after,count,afterValid,step,paid⟩ := tendon.inner_left_push gap parent tendonValid (.node ia key ib)
      exact ⟨after.marked (.node ia key ib),ilp+irp+after.potential,count,
        .node after afterValid innerLeft innerRight,step,by omega⟩

theorem inner_right_demote (frames : List (Pointer.Frame α)) (left right : Hand α)
    (key parent : α) (gap : RawTree α) :
    Implemented (.node frames (.stump gap) parent (.node [] left key right))
      (.node (.right gap parent::frames) left key right) := by
  intro physical credit valid
  cases valid with
  | @node _ _ _ _ a b lp rp tendon tendonValid childLeft childRight =>
      cases childLeft
      obtain ⟨ia,ib,ilp,irp,innerLeft,innerRight,rfl,rfl⟩ := childRight.node_nil
      obtain ⟨after,count,afterValid,step,paid⟩ := tendon.inner_right_push gap parent tendonValid (.node ia key ib)
      exact ⟨after.marked (.node ia key ib),ilp+irp+after.potential,count,
        .node after afterValid innerLeft innerRight,step,by omega⟩

end DynamicOptimality.MultiFinger.PhysicalHand
