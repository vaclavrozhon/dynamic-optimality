import TangoSquared.Paper20261030.AdjacentExposure
import TangoSquared.Paper20261030.ComponentPortWords

/-! Exact words and port positions of a split above a numeric separator.
These identify the physical suffix used in the prepared head exchange. -/

namespace TangoSquared.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α : Type*} {β : Nat → Type*}

theorem cutRight_word_filter (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (lo : Nat) (found : searchResult lo c.core = true) :
    (cutRight c lo found).core.toListModel = c.core.toListModel.filter (fun e => decide (lo < e.1)) := by
  have low : ((cutLeft c lo found).core.toListModel.filter (fun e => decide (lo < e.1))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he pred
    have bound := split_left_key lo c.core c.balanced found ordered he
    have high : lo < e.1 := of_decide_eq_true pred
    omega
  have high : ((cutRight c lo found).core.toListModel.filter (fun e => decide (lo < e.1))) =
      (cutRight c lo found).core.toListModel := by
    apply List.filter_eq_self.mpr
    intro e he
    exact decide_eq_true (split_right_key lo c.core c.balanced found ordered he)
  rw [← splitAt_toList lo c.core c.balanced found]
  change _ = ((cutLeft c lo found).core.toListModel ++
    ⟨lo,(splitAt lo c.core c.balanced found).value⟩ :: (cutRight c lo found).core.toListModel).filter _
  simp only [List.filter_append,List.filter_cons,lt_self_iff_false,decide_false,
    Bool.false_eq_true,if_false,low,high,List.nil_append]

theorem cutRight_portWord_drop (c : AuxiliaryComponent α Nat β) (lo : Nat)
    (found : searchResult lo c.core = true) :
    (cutRight c lo found).portWord = c.portWord.drop ((cutLeft c lo found).core.size + 1) := by
  rw [cut_portWord c lo found,← portWord_length (cutLeft c lo found),List.drop_left]

theorem gapIndex_successor_split (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (lo : Nat) (found : searchResult lo c.core = true) :
    gapIndex (lo+1) c.core = (cutLeft c lo found).core.size + 1 := by
  have rightZero : gapIndex (lo+1) (cutRight c lo found).core = 0 := by
    rw [gapIndex_count (lo+1) (cutRight c lo found).core (cutRight c lo found).balanced
      (cutRight_ordered c ordered lo found)]
    have empty : ((cutRight c lo found).core.toListModel.filter (fun e => decide (e.1 < lo+1))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he pred
      have bound := split_right_key lo c.core c.balanced found ordered he
      have low : e.1 < lo+1 := of_decide_eq_true pred
      omega
    rw [empty]
    rfl
  rw [gapIndex_above_split c ordered lo (lo+1) (by omega) found,rightZero,Nat.add_zero]

theorem cutLeft_portWord_take (c : AuxiliaryComponent α Nat β) (lo : Nat)
    (found : searchResult lo c.core = true) :
    (cutLeft c lo found).portWord = c.portWord.take ((cutLeft c lo found).core.size + 1) := by
  rw [cut_portWord c lo found,← portWord_length (cutLeft c lo found),List.take_left]

end TangoSquared.Paper20261030.AuxiliaryComponent
