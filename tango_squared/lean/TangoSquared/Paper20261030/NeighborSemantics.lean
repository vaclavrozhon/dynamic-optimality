import TangoSquared.Paper20261030.ObservedNeighbors
import TangoSquared.Paper20261030.PredicateSearch

/-! The pair decoded from the actual binary-search observations consists
of the exact neighboring records in the ordered inorder word. Both absent
neighbors, including a query at zero, are handled without subtraction. -/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {κ : Type*} {β : κ → Type*}

def firstGood (good : Sigma β → Bool) : Impl κ β → Option (Sigma β)
  | .leaf => none
  | .inner _ key value l r =>
      if good ⟨key,value⟩ then some ((firstGood good l).getD ⟨key,value⟩) else firstGood good r

def SuffixPredicate (good : Sigma β → Bool) (t : Impl κ β) : Prop :=
  t.toListModel.Pairwise (fun a b => good a = true → good b = true)

theorem firstGood_correct (good : Sigma β → Bool) (t : Impl κ β) (hp : SuffixPredicate good t) :
    firstGood good t = (t.toListModel.filter good).head? := by
  induction t with
  | leaf => rfl
  | inner cached key value l r ihl ihr =>
    change (l.toListModel ++ ⟨key,value⟩ :: r.toListModel).Pairwise _ at hp
    obtain ⟨hl,hr,hcross⟩ := List.pairwise_append.mp hp
    obtain ⟨hroot,hrr⟩ := List.pairwise_cons.mp hr
    by_cases hg : good ⟨key,value⟩ = true
    · rw [firstGood,if_pos hg,ihl hl]
      simp only [toListModel_inner,List.filter_append,List.filter_cons,hg,if_true,
        List.head?_append,List.head?_cons]
      cases (l.toListModel.filter good).head? <;> rfl
    · have he : l.toListModel.filter good = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e hm hgood
        exact hg (hcross e hm ⟨key,value⟩ (by simp) hgood)
      rw [firstGood,if_neg hg,ihr hrr]
      simp [toListModel_inner,List.filter_append,hg,he]

end TangoSquared.Paper20261030.Auxiliary.Metadata

namespace TangoSquared.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open Auxiliary Auxiliary.Metadata

variable {β : Nat → Type*}

def belowQuery (d : Nat) (e : Sigma (Tagged β)) : Bool := decide (e.1 < d)
def aboveQuery (d : Nat) (e : Sigma (Tagged β)) : Bool := decide (d ≤ e.1)

theorem belowQuery_prefix (d : Nat) (t : Impl Nat (Tagged β)) (ordered : t.Ordered) :
    PrefixPredicate (belowQuery d) t := by
  apply ordered.imp
  intro e f horder hf
  have hlt := Nat.compare_eq_lt.mp horder
  simp only [belowQuery,decide_eq_true_eq] at hf ⊢
  omega

theorem aboveQuery_suffix (d : Nat) (t : Impl Nat (Tagged β)) (ordered : t.Ordered) :
    SuffixPredicate (aboveQuery d) t := by
  apply ordered.imp
  intro e f horder he
  have hlt := Nat.compare_eq_lt.mp horder
  simp only [aboveQuery,decide_eq_true_eq] at he ⊢
  omega

theorem neighbors_lower (d : Nat) (t : Impl Nat (Tagged β)) :
    (neighbors d t).1 = lastGood (belowQuery d) t := by
  induction t with
  | leaf => rfl
  | inner cached key value l r ihl ihr =>
    by_cases hd : d ≤ key
    · have hl : decide (key < d) = false := decide_eq_false (by omega)
      simp only [neighbors,if_pos hd,lastGood,belowQuery,hl,Bool.false_eq_true,if_false,ihl]
    · have hl : decide (key < d) = true := decide_eq_true (by omega)
      simp only [neighbors,if_neg hd,lastGood,belowQuery,hl,if_true,ihr]

theorem neighbors_upper (d : Nat) (t : Impl Nat (Tagged β)) :
    (neighbors d t).2 = firstGood (aboveQuery d) t := by
  induction t with
  | leaf => rfl
  | inner cached key value l r ihl ihr =>
    by_cases hd : d ≤ key
    · simp only [neighbors,if_pos hd,firstGood,aboveQuery,decide_eq_true hd,if_true,ihl]
    · simp only [neighbors,if_neg hd,firstGood,aboveQuery,decide_eq_false hd,Bool.false_eq_true,if_false,ihr]

theorem neighbors_correct (d : Nat) (t : Impl Nat (Tagged β)) (ordered : t.Ordered) :
    (neighbors d t).1 = (t.toListModel.filter (belowQuery d)).getLast? ∧
      (neighbors d t).2 = (t.toListModel.filter (aboveQuery d)).head? := by
  rw [neighbors_lower,neighbors_upper]
  exact ⟨lastGood_correct _ _ (belowQuery_prefix d t ordered),
    firstGood_correct _ _ (aboveQuery_suffix d t ordered)⟩

theorem neighbors_lower_mem (d : Nat) (t : Impl Nat (Tagged β)) (ordered : t.Ordered)
    {e : Sigma (Tagged β)} (he : (neighbors d t).1 = some e) : e ∈ t.toListModel ∧ e.1 < d := by
  rw [(neighbors_correct d t ordered).1] at he
  obtain ⟨hm,hb⟩ := List.mem_filter.mp (List.mem_of_getLast? he)
  exact ⟨hm,of_decide_eq_true hb⟩

theorem neighbors_upper_mem (d : Nat) (t : Impl Nat (Tagged β)) (ordered : t.Ordered)
    {e : Sigma (Tagged β)} (he : (neighbors d t).2 = some e) : e ∈ t.toListModel ∧ d ≤ e.1 := by
  rw [(neighbors_correct d t ordered).2] at he
  obtain ⟨hm,hb⟩ := List.mem_filter.mp (List.mem_of_head? he)
  exact ⟨hm,of_decide_eq_true hb⟩

end TangoSquared.Paper20261030.BoundaryObservations
