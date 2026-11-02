import DynamicOptimality.MultiFinger.PhysicalEndpointBase

namespace DynamicOptimality.MultiFinger.PhysicalHand

open ChaCha.MTR
open Pointer (MarkedTree)
open TendonContents

variable {α : Type*}

theorem outer_right_promote (frames : List (Pointer.Frame α)) (left right : Hand α)
    (key parent : α) (gap : RawTree α) :
    Implemented (.node (frames++[.right gap parent]) left key right)
      (.node [] (.stump gap) parent (.node frames left key right)) := by
  intro physical credit valid
  cases valid with
  | @node _ _ _ _ a b lp rp tendon valid leftRep rightRep =>
      obtain ⟨after,count,afterValid,step,paid⟩ := tendon.outer_right_pop gap parent valid (.node a key b)
      refine ⟨.node (.hole gap) parent (after.marked (.node a key b)),lp+rp+after.potential,count,?_,step,by omega⟩
      simpa only [emptyTendon_marked,emptyTendon_potential,Nat.zero_add,Nat.add_zero] using
        Realizes.node emptyTendon emptyTendon_valid (.stump gap) (.node after afterValid leftRep rightRep)

theorem outer_left_promote (frames : List (Pointer.Frame α)) (left right : Hand α)
    (key parent : α) (gap : RawTree α) :
    Implemented (.node (frames++[.left parent gap]) left key right)
      (.node [] (.node frames left key right) parent (.stump gap)) := by
  intro physical credit valid
  cases valid with
  | @node _ _ _ _ a b lp rp tendon valid leftRep rightRep =>
      obtain ⟨after,count,afterValid,step,paid⟩ := tendon.outer_left_pop gap parent valid (.node a key b)
      refine ⟨.node (after.marked (.node a key b)) parent (.hole gap),lp+rp+after.potential,count,?_,step,by omega⟩
      simpa only [emptyTendon_marked,emptyTendon_potential,Nat.zero_add,Nat.add_zero] using
        Realizes.node emptyTendon emptyTendon_valid (.node after afterValid leftRep rightRep) (.stump gap)

theorem inner_left_promote (frames : List (Pointer.Frame α)) (left right : Hand α)
    (key parent : α) (gap : RawTree α) :
    Implemented (.node (.left parent gap::frames) left key right)
      (.node frames (.node [] left key right) parent (.stump gap)) := by
  intro physical credit valid
  cases valid with
  | @node _ _ _ _ a b lp rp tendon valid leftRep rightRep =>
      obtain ⟨after,count,afterValid,step,paid⟩ := tendon.inner_left_pop gap parent valid (.node a key b)
      refine ⟨after.marked (.node (.node a key b) parent (.hole gap)),lp+rp+after.potential,count,?_,step,by omega⟩
      simpa only [emptyTendon_marked,emptyTendon_potential,Nat.zero_add,Nat.add_zero] using
        Realizes.node after afterValid (.node emptyTendon emptyTendon_valid leftRep rightRep) (.stump gap)

theorem inner_right_promote (frames : List (Pointer.Frame α)) (left right : Hand α)
    (key parent : α) (gap : RawTree α) :
    Implemented (.node (.right gap parent::frames) left key right)
      (.node frames (.stump gap) parent (.node [] left key right)) := by
  intro physical credit valid
  cases valid with
  | @node _ _ _ _ a b lp rp tendon valid leftRep rightRep =>
      obtain ⟨after,count,afterValid,step,paid⟩ := tendon.inner_right_pop gap parent valid (.node a key b)
      refine ⟨after.marked (.node (.hole gap) parent (.node a key b)),lp+rp+after.potential,count,?_,step,by omega⟩
      simpa only [emptyTendon_marked,emptyTendon_potential,Nat.zero_add,Nat.add_zero] using
        Realizes.node after afterValid (.stump gap) (.node emptyTendon emptyTendon_valid leftRep rightRep)

end DynamicOptimality.MultiFinger.PhysicalHand
