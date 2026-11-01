import TangoSquared.Paper20261030.SplitPortSlices
import TangoSquared.Paper20261030.AuxiliaryPortSearch
import TangoSquared.Paper20261030.MarkedCut

/-!
# Exposing the actual gap between consecutive separators

Two balanced splits expose consecutive keys without touching any port
interior. The intervening logical core is empty, so its physical tree is
exactly the original gap reached by a search for the larger key. The
one-boundary case applies when no separator is smaller than the query.
-/

namespace TangoSquared.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata BoundaryObservations

variable {α : Type*} {β : Nat → Type*}

theorem split_pivot_mem (c : AuxiliaryComponent α Nat β) (key : Nat)
    (found : searchResult key c.core = true) :
    (⟨key,(splitAt key c.core c.balanced found).value⟩ : Sigma β) ∈ c.core.toListModel := by
  rw [← splitAt_toList key c.core c.balanced found]
  simp [SplitResult.impl,bin,toListModel_inner]

theorem higher_found_right (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (lo hi : Nat) (less : lo < hi) (fl : searchResult lo c.core = true)
    (fh : searchResult hi c.core = true) : searchResult hi (cutRight c lo fl).core = true := by
  let pivot : Sigma β := ⟨hi,(splitAt hi c.core c.balanced fh).value⟩
  have mem := split_pivot_mem c hi fh
  rw [← splitAt_toList lo c.core c.balanced fl] at mem
  simp only [SplitResult.impl,bin,toListModel_inner,List.mem_append,List.mem_cons] at mem
  have rightMem : pivot ∈ (cutRight c lo fl).core.toListModel := by
    rcases mem with left | equal | right
    · have low := split_left_key lo c.core c.balanced fl ordered left
      simp only at low
      omega
    · have keys := congrArg Sigma.fst equal
      simp only at keys
      omega
    · exact right
  rw [searchResult_eq_contains,contains_eq_containsKey (cutRight_ordered c ordered lo fl)]
  exact Std.Internal.List.containsKey_of_mem rightMem

theorem gapIndex_at_split (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (key : Nat) (found : searchResult key c.core = true) :
    gapIndex key c.core = (cutLeft c key found).core.size := by
  rw [gapIndex_count key c.core c.balanced ordered,← splitAt_toList key c.core c.balanced found]
  have low : ((cutLeft c key found).core.toListModel.filter (fun e => decide (e.1 < key))) =
      (cutLeft c key found).core.toListModel := by
    apply List.filter_eq_self.mpr
    intro e he
    exact decide_eq_true (split_left_key key c.core c.balanced found ordered he)
  have high : ((cutRight c key found).core.toListModel.filter (fun e => decide (e.1 < key))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hp
    have bound := split_right_key key c.core c.balanced found ordered he
    have pred : e.1 < key := of_decide_eq_true hp
    omega
  change (((cutLeft c key found).core.toListModel ++
    ⟨key,(splitAt key c.core c.balanced found).value⟩ :: (cutRight c key found).core.toListModel).filter
      (fun e => decide (e.1 < key))).length = _
  simp only [List.filter_append,List.filter_cons,lt_self_iff_false,decide_false,
    Bool.false_eq_true,if_false,low,high,List.append_nil]
  exact (size_eq_length _ (cutLeft c key found).balanced).symm

theorem gapIndex_above_split (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (lo query : Nat) (less : lo < query) (found : searchResult lo c.core = true) :
    gapIndex query c.core = (cutLeft c lo found).core.size + 1 +
      gapIndex query (cutRight c lo found).core := by
  rw [gapIndex_count query c.core c.balanced ordered,
    gapIndex_count query (cutRight c lo found).core (cutRight c lo found).balanced
      (cutRight_ordered c ordered lo found),← splitAt_toList lo c.core c.balanced found]
  have low : ((cutLeft c lo found).core.toListModel.filter (fun e => decide (e.1 < query))) =
      (cutLeft c lo found).core.toListModel := by
    apply List.filter_eq_self.mpr
    intro e he
    have bound := split_left_key lo c.core c.balanced found ordered he
    exact decide_eq_true (by omega)
  change (((cutLeft c lo found).core.toListModel ++
    ⟨lo,(splitAt lo c.core c.balanced found).value⟩ :: (cutRight c lo found).core.toListModel).filter
      (fun e => decide (e.1 < query))).length = _
  simp only [List.filter_append,List.filter_cons,decide_eq_true less,if_true,low,
    List.length_append,List.length_cons,size_eq_length _ (cutLeft c lo found).balanced]
  omega

theorem adjacent_middle_empty (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (lo : Nat) (fl : searchResult lo c.core = true)
    (fh : searchResult (lo+1) (cutRight c lo fl).core = true) :
    (cutLeft (cutRight c lo fl) (lo+1) fh).core = .leaf := by
  let right := cutRight c lo fl
  have empty : (cutLeft right (lo+1) fh).core.toListModel = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    have high := split_left_key (lo+1) right.core right.balanced fh
      (cutRight_ordered c ordered lo fl) he
    have mem : e ∈ right.core.toListModel := by
      rw [← splitAt_toList (lo+1) right.core right.balanced fh]
      exact List.mem_append_left _ he
    have low := split_right_key lo c.core c.balanced fl ordered mem
    omega
  generalize hcore : (cutLeft right (lo+1) fh).core = core at empty ⊢
  cases core with
  | leaf => rfl
  | inner sz key value l r => simp [toListModel_inner] at empty

theorem adjacent_middle_port (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (lo : Nat) (fl : searchResult lo c.core = true)
    (fh : searchResult (lo+1) (cutRight c lo fl).core = true) :
    (cutLeft (cutRight c lo fl) (lo+1) fh).tree = c.ports (gapIndex (lo+1) c.core) := by
  have empty := adjacent_middle_empty c ordered lo fl fh
  have rank := gapIndex_above_split c ordered lo (lo+1) (by omega) fl
  rw [gapIndex_at_split (cutRight c lo fl) (cutRight_ordered c ordered lo fl) (lo+1) fh,
    empty,size_leaf,Nat.add_zero] at rank
  rw [rank]
  unfold tree
  rw [empty]
  simp only [recordTree,GapSource.encode,cutLeft,cutRight,Nat.add_zero]

theorem adjacent_expose_charged (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (lo : Nat) (fl : searchResult lo c.core = true)
    (fh : searchResult (lo+1) (cutRight c lo fl).core = true) :
    SourcePointer.Rearranges c.tree
      (.fork (c.core.size,⟨lo,(splitAt lo c.core c.balanced fl).value⟩)
        (cutLeft c lo fl).tree
        (.fork ((cutRight c lo fl).core.size,
          ⟨lo+1,(splitAt (lo+1) (cutRight c lo fl).core (cutRight c lo fl).balanced fh).value⟩)
          (c.ports (gapIndex (lo+1) c.core)) (cutRight (cutRight c lo fl) (lo+1) fh).tree))
      (11460 * Nat.clog 2 (c.core.size + 1) + 2) := by
  have first := expose_charged c lo fl
  have second := (expose_charged (cutRight c lo fl) (lo+1) fh).right
    (l := (cutLeft c lo fl).tree)
    (record := (c.core.size,⟨lo,(splitAt lo c.core c.balanced fl).value⟩))
  rw [adjacent_middle_port c ordered lo fl fh] at second
  apply (first.trans second).mono
  have smaller := Nat.clog_monotone 2 (Nat.add_le_add_right (cutRight_size_le c lo fl) 1)
  omega

theorem minimum_left_empty (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (key : Nat) (found : searchResult key c.core = true)
    (minimum : ∀ e ∈ c.core.toListModel, key ≤ e.1) : (cutLeft c key found).core = .leaf := by
  have empty : (cutLeft c key found).core.toListModel = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    have low := split_left_key key c.core c.balanced found ordered he
    have mem : e ∈ c.core.toListModel := by
      rw [← splitAt_toList key c.core c.balanced found]
      exact List.mem_append_left _ he
    have high := minimum e mem
    omega
  generalize hcore : (cutLeft c key found).core = core at empty ⊢
  cases core with
  | leaf => rfl
  | inner sz key value l r => simp [toListModel_inner] at empty

theorem minimum_expose_charged (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (key : Nat) (found : searchResult key c.core = true)
    (minimum : ∀ e ∈ c.core.toListModel, key ≤ e.1) :
    SourcePointer.Rearranges c.tree
      (.fork (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩)
        (c.ports (gapIndex key c.core)) (cutRight c key found).tree)
      (5730 * Nat.clog 2 (c.core.size + 1)) := by
  have empty := minimum_left_empty c ordered key found minimum
  have tree : (cutLeft c key found).tree = c.ports (gapIndex key c.core) := by
    rw [gapIndex_at_split c ordered key found,empty,size_leaf]
    unfold AuxiliaryComponent.tree
    rw [empty]
    rfl
  simpa only [tree] using expose_charged c key found

end TangoSquared.Paper20261030.AuxiliaryComponent
