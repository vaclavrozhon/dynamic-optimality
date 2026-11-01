import TangoSquared.Monotonicity
import TangoSquared.CyclicRuns
import TangoSquared.PrefixOrder

/-! Actual cyclic versions of the primary and secondary sequence statistics. -/

namespace TangoSquared
open Primary

def cyclicAlternations {α : Type*} [DecidableEq α] : List α → Nat
  | [] => 0
  | a :: as => changesFrom (as.getLastD a) (a :: as)

theorem alternations_le_cyclic {α : Type*} [DecidableEq α] (xs : List α) :
    alternations xs ≤ cyclicAlternations xs := by
  cases xs with
  | nil => rfl
  | cons a as => simp [cyclicAlternations, alternations]

def cyclicRL (xs : List Bool) : Nat := rlFrom (xs.getLastD false) xs

theorem rlCount_le_cyclic (xs : List Bool) : rlCount xs ≤ cyclicRL xs := by
  unfold rlCount cyclicRL
  cases xs.getLastD false with
  | false => rfl
  | true => exact rlFrom_false_le_true xs

def cyclicTransitionWord {α C F : Type*} [DecidableEq C] [DecidableEq F]
    (coarse : α → C) (fine : α → F) : List α → List Bool
  | [] => []
  | a :: as => transitionsFrom coarse fine (as.getLastD a) (a :: as)

def cyclicDemands {α C F : Type*} [DecidableEq C] [DecidableEq F]
    (coarse : α → C) (fine : α → F) (xs : List α) : Nat :=
  cyclicRL (cyclicTransitionWord coarse fine xs)

theorem demands_le_cyclic {α C F : Type*} [DecidableEq C] [DecidableEq F]
    (coarse : α → C) (fine : α → F) (xs : List α) :
    demands coarse fine xs ≤ cyclicDemands coarse fine xs := by
  apply le_trans _ (rlCount_le_cyclic _)
  apply rlCount_sublist
  cases xs with
  | nil => exact List.Sublist.refl _
  | cons a as => exact List.sublist_append_right _ _

def cyclicPrimary (H : Nat) (xs : List Key) : Nat :=
  ∑ u ∈ owners H, cyclicAlternations (xs.filterMap (branch u))

def Gadget.cyclicCount (q : Gadget) (xs : List Key) : Nat :=
  cyclicDemands q.coarse q.fine (ownerWord q.owner xs)

def cyclicSecondary (H : Nat) (xs : List Key) : Nat :=
  ∑ q ∈ gadgets H, q.cyclicCount xs

theorem primary_le_cyclic (H : Nat) (xs : List Key) :
    primaryCount H xs ≤ cyclicPrimary H xs :=
  Finset.sum_le_sum fun _ _ => alternations_le_cyclic _

theorem secondary_le_cyclic (H : Nat) (xs : List Key) :
    secondaryDemands H xs ≤ cyclicSecondary H xs :=
  Finset.sum_le_sum fun q _ => demands_le_cyclic q.coarse q.fine _

end TangoSquared
