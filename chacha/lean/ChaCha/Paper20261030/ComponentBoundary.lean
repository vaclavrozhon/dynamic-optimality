import ChaCha.Paper20261030.ComponentCut
import ChaCha.Paper20261030.PredecessorSearch

/-!
# Cutting an auxiliary at a numeric interval boundary

The boundary need not itself be a stored separator. Its predecessor is
found by charged reads, then the physical cut produces exactly the keys
at most the boundary and the keys above it. Both component cores remain
balanced; the upper part is the actual last port of the lower component.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {β : Nat → Type*}

theorem split_left_key (key : Nat) (t : Impl Nat β) (ht : t.Balanced)
    (hf : searchResult key t = true) (ho : t.Ordered)
    {entry : Sigma β} (hm : entry ∈ (splitAt key t ht hf).left.toListModel) : entry.1 < key := by
  have hs := splitAt_ordered key t ht hf ho
  change ((splitAt key t ht hf).left.toListModel ++
    ⟨key,(splitAt key t ht hf).value⟩ :: (splitAt key t ht hf).right.toListModel).Pairwise _ at hs
  exact Nat.compare_eq_lt.mp ((List.pairwise_append.mp hs).2.2 entry hm
    ⟨key,(splitAt key t ht hf).value⟩ (by simp))

theorem split_right_key (key : Nat) (t : Impl Nat β) (ht : t.Balanced)
    (hf : searchResult key t = true) (ho : t.Ordered)
    {entry : Sigma β} (hm : entry ∈ (splitAt key t ht hf).right.toListModel) : key < entry.1 := by
  have hs := splitAt_ordered key t ht hf ho
  change ((splitAt key t ht hf).left.toListModel ++
    ⟨key,(splitAt key t ht hf).value⟩ :: (splitAt key t ht hf).right.toListModel).Pairwise _ at hs
  exact Nat.compare_eq_lt.mp ((List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 entry hm)

theorem split_right_mem (key : Nat) (t : Impl Nat β) (ht : t.Balanced)
    (hf : searchResult key t = true)
    {entry : Sigma β} (hm : entry ∈ (splitAt key t ht hf).right.toListModel) : entry ∈ t.toListModel := by
  rw [← splitAt_toList key t ht hf]
  simp only [SplitResult.impl,bin,toListModel_inner,List.mem_append,List.mem_cons]
  exact Or.inr (Or.inr hm)

end ChaCha.Paper20261030.Auxiliary

namespace ChaCha.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α : Type*} {β : Nat → Type*}

theorem predecessor_cut_lower (bound : Nat) (c : AuxiliaryComponent α Nat β) (ho : c.core.Ordered)
    {pivot : Sigma β} (hp : lastGood (atMost bound) c.core = some pivot)
    {entry : Sigma β}
    (hm : entry ∈ (cutOutput c pivot.1 (predecessor_found bound c.core ho hp)).core.toListModel) :
    entry.1 ≤ bound := by
  have hpb := (predecessor_mem bound c.core ho hp).2
  simp only [cutOutput,append_word,cutLeft,List.mem_append,List.mem_singleton] at hm
  rcases hm with hleft | he
  · have hl := split_left_key pivot.1 c.core c.balanced (predecessor_found bound c.core ho hp) ho hleft
    omega
  · cases he
    exact hpb

theorem predecessor_cut_upper (bound : Nat) (c : AuxiliaryComponent α Nat β) (ho : c.core.Ordered)
    {pivot : Sigma β} (hp : lastGood (atMost bound) c.core = some pivot)
    {entry : Sigma β}
    (hm : entry ∈ (cutRight c pivot.1 (predecessor_found bound c.core ho hp)).core.toListModel) :
    bound < entry.1 := by
  have hg := split_right_key pivot.1 c.core c.balanced (predecessor_found bound c.core ho hp) ho hm
  have he := split_right_mem pivot.1 c.core c.balanced (predecessor_found bound c.core ho hp) hm
  by_contra hn
  have hle := predecessor_maximal bound c.core ho hp he (by omega)
  omega

theorem predecessor_cut_words (bound : Nat) (c : AuxiliaryComponent α Nat β) (ho : c.core.Ordered)
    {pivot : Sigma β} (hp : lastGood (atMost bound) c.core = some pivot) :
    (cutOutput c pivot.1 (predecessor_found bound c.core ho hp)).core.toListModel =
        c.core.toListModel.filter (atMost bound) ∧
      (cutRight c pivot.1 (predecessor_found bound c.core ho hp)).core.toListModel =
        c.core.toListModel.filter (fun e => decide (bound < e.1)) := by
  let found := predecessor_found bound c.core ho hp
  have he := cut_word c pivot.1 found
  have hlo : ∀ entry ∈ (cutOutput c pivot.1 found).core.toListModel, entry.1 ≤ bound :=
    fun _ hm => predecessor_cut_lower bound c ho hp hm
  have hhi : ∀ entry ∈ (cutRight c pivot.1 found).core.toListModel, bound < entry.1 :=
    fun _ hm => predecessor_cut_upper bound c ho hp hm
  rw [← he]
  let low := (cutOutput c pivot.1 found).core.toListModel
  let high := (cutRight c pivot.1 found).core.toListModel
  change low = (low ++ high).filter (fun e => decide (e.1 ≤ bound)) ∧
    high = (low ++ high).filter (fun e => decide (bound < e.1))
  constructor
  · rw [List.filter_append,
      List.filter_eq_self.mpr (fun e hm => decide_eq_true (hlo e hm)),
      List.filter_eq_nil_iff.mpr (fun e hm hb => by
        have hb' : e.1 ≤ bound := of_decide_eq_true hb
        have hh := hhi e hm
        omega),List.append_nil]
  · rw [List.filter_append,
      List.filter_eq_nil_iff.mpr (fun e hm hb => by
        have hb' : bound < e.1 := of_decide_eq_true hb
        have hh := hlo e hm
        omega),
      List.filter_eq_self.mpr (fun e hm => decide_eq_true (hhi e hm)),List.nil_append]

theorem predecessor_cut_charged (bound : Nat) (c : AuxiliaryComponent α Nat β) (ho : c.core.Ordered)
    {pivot : Sigma β} (hp : lastGood (atMost bound) c.core = some pivot) :
    SourcePointer.Rearranges c.tree (cutOutput c pivot.1 (predecessor_found bound c.core ho hp)).tree
      (6234 * Nat.clog 2 (c.core.size + 1) + 76) := by
  have queried : SourcePointer.Rearranges c.tree c.tree (9 * Nat.clog 2 (c.core.size + 1)) := by
    intro ancestors
    obtain ⟨cost,trace,hcost⟩ := query_charged_log (atMost bound) c.core c.balanced []
    have lifted := GapSource.metadata_trace trace c.ports 0
    have rooted : SourcePointer.Trace ⟨c.tree,[]⟩ (queryReads (atMost bound) c.core) ⟨c.tree,[]⟩ cost := by
      simpa only [GapSource.cursor,GapSource.frames,PointerGraft.offset,Nat.add_zero,tree] using lifted
    exact ⟨_,cost,rooted.extend ancestors,hcost⟩
  have full := queried.trans (cut_charged c pivot.1 (predecessor_found bound c.core ho hp))
  apply full.mono
  omega

end ChaCha.Paper20261030.AuxiliaryComponent
