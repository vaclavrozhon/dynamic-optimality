import TangoSquared.Paper20261030.PredicateSearch
import TangoSquared.Paper20261030.GraftedMetadata

/-!
# Finding and exposing an auxiliary interval boundary

The cut label need not occur in the auxiliary tree. Search finds the
largest stored key at most the label, or certifies that none exists.
When it exists, the existing charged split exposes that actual key.
This supports cuts specified by reference intervals without assuming
that their numeric endpoints are themselves auxiliary records.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {β : Nat → Type*}

def atMost (bound : Nat) (entry : Sigma β) : Bool := decide (entry.1 ≤ bound)

theorem atMost_prefix (bound : Nat) (t : Impl Nat β) (ho : t.Ordered) :
    PrefixPredicate (atMost bound) t := by
  apply ho.imp
  intro e f horder hf
  have hlt := Nat.compare_eq_lt.mp horder
  simp only [atMost,decide_eq_true_eq] at hf ⊢
  omega

theorem predecessor_correct (bound : Nat) (t : Impl Nat β) (ho : t.Ordered) :
    lastGood (atMost bound) t = (t.toListModel.filter (atMost bound)).getLast? :=
  lastGood_correct _ _ (atMost_prefix bound t ho)

theorem predecessor_mem (bound : Nat) (t : Impl Nat β) (ho : t.Ordered)
    {entry : Sigma β} (hp : lastGood (atMost bound) t = some entry) :
    entry ∈ t.toListModel ∧ entry.1 ≤ bound := by
  rw [predecessor_correct bound t ho] at hp
  have hm := List.mem_filter.mp (List.mem_of_getLast? hp)
  exact ⟨hm.1,of_decide_eq_true hm.2⟩

theorem predecessor_maximal (bound : Nat) (t : Impl Nat β) (ho : t.Ordered)
    {entry : Sigma β} (hp : lastGood (atMost bound) t = some entry)
    {other : Sigma β} (hm : other ∈ t.toListModel) (hb : other.1 ≤ bound) : other.1 ≤ entry.1 := by
  rw [predecessor_correct bound t ho] at hp
  obtain ⟨earlier,he⟩ := List.getLast?_eq_some_iff.mp hp
  have hs := ho.filter (atMost bound)
  have hmem : other ∈ t.toListModel.filter (atMost bound) :=
    List.mem_filter.mpr ⟨hm,by simpa only [atMost,decide_eq_true_eq] using hb⟩
  rw [he] at hs hmem
  rcases List.mem_append.mp hmem with hbefore | hlast
  · exact (Nat.compare_eq_lt.mp ((List.pairwise_append.mp hs).2.2 other hbefore entry (by simp))).le
  · have heq := List.mem_singleton.mp hlast
    subst other
    exact le_rfl

theorem predecessor_none_iff (bound : Nat) (t : Impl Nat β) (ho : t.Ordered) :
    lastGood (atMost bound) t = none ↔ ∀ entry ∈ t.toListModel, bound < entry.1 := by
  rw [predecessor_correct bound t ho,List.getLast?_eq_none_iff,List.filter_eq_nil_iff]
  simp only [atMost,decide_eq_true_eq,Nat.not_le]

theorem predecessor_found (bound : Nat) (t : Impl Nat β) (ho : t.Ordered)
    {entry : Sigma β} (hp : lastGood (atMost bound) t = some entry) :
    searchResult entry.1 t = true := by
  rw [searchResult_eq_contains,contains_eq_containsKey ho]
  exact Std.Internal.List.containsKey_of_mem (predecessor_mem bound t ho hp).1

theorem expose_predecessor_charged (bound : Nat) (t : Impl Nat β)
    (ht : t.Balanced) (ho : t.Ordered) {entry : Sigma β}
    (hp : lastGood (atMost bound) t = some entry) :
    ObservedRearranges t (splitAt entry.1 t ht (predecessor_found bound t ho hp)).impl
      (5739 * Nat.clog 2 (t.size + 1)) := by
  intro ancestors
  obtain ⟨qc,query,hqc⟩ := query_charged_log (atMost bound) t ht ancestors
  obtain ⟨word,sc,split,hsc⟩ := splitAt_charged_log entry.1 t ht
    (predecessor_found bound t ho hp) ancestors
  exact ⟨_,_,query.append split,by omega⟩

end TangoSquared.Paper20261030.Auxiliary.Metadata
