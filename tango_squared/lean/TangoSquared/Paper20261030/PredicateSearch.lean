import TangoSquared.Paper20261030.ChargedInsertion
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-!
# Observed binary search for a prefix predicate

The predicate is true on a prefix of the auxiliary tree's ordered record
list. Search returns the last true record, or `none` when that prefix is
empty. It reads one complete record at each visited vertex and returns to
the initial root, with at most three operations per level.

This is the search needed for the deepest interval of a preferred path
that contains a target depth. Instantiating the predicate with those
interval records, and charging its local evaluation, are separate steps.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open TangoSquared.MTR

variable {α : Type*} {β : α → Type*}

def lastGood (good : Sigma β → Bool) : Impl α β → Option (Sigma β)
  | .leaf => none
  | .inner _ k v l r =>
    if good ⟨k,v⟩ then some ((lastGood good r).getD ⟨k,v⟩) else lastGood good l

def queryReads (good : Sigma β → Bool) : Impl α β → List (NodeRecord α β)
  | .leaf => []
  | .inner sz k v l r =>
    (sz,⟨k,v⟩) :: if good ⟨k,v⟩ then queryReads good r else queryReads good l

/-- A later true entry forces every earlier entry to be true. -/
def PrefixPredicate (good : Sigma β → Bool) (t : Impl α β) : Prop :=
  t.toListModel.Pairwise (fun a b => good b = true → good a = true)

theorem lastGood_correct (good : Sigma β → Bool) (t : Impl α β)
    (hp : PrefixPredicate good t) :
    lastGood good t = (t.toListModel.filter good).getLast? := by
  induction t with
  | leaf => rfl
  | inner sz k v l r ihl ihr =>
    change (l.toListModel ++ ⟨k,v⟩ :: r.toListModel).Pairwise _ at hp
    obtain ⟨hl,hr,_⟩ := List.pairwise_append.mp hp
    obtain ⟨hroot,hrr⟩ := List.pairwise_cons.mp hr
    by_cases hg : good ⟨k,v⟩ = true
    · rw [lastGood,if_pos hg,ihr hrr]
      simp [Impl.toListModel,List.filter_append,hg,List.getLast?_append,List.getLast?_cons]
    · have he : r.toListModel.filter good = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro entry hentry hgood
        exact hg (hroot entry hentry hgood)
      rw [lastGood,if_neg hg,ihl hl]
      simp [Impl.toListModel,List.filter_append,hg,he]

theorem query_charged (good : Sigma β → Bool) (t : Impl α β) (ancestors) :
    ∃ cost, Trace ⟨recordTree t,ancestors⟩ (queryReads good t)
      ⟨recordTree t,ancestors⟩ cost ∧ cost ≤ 3 * height t := by
  induction t generalizing ancestors with
  | leaf => exact ⟨0,.nil _,le_rfl⟩
  | inner sz k v l r ihl ihr =>
    by_cases hg : good ⟨k,v⟩ = true
    · cases r with
      | leaf =>
        refine ⟨1,?_,by simp only [height]; omega⟩
        simpa only [queryReads,if_pos hg] using
          (Trace.read (c := ⟨recordTree (.inner sz k v l .leaf),ancestors⟩) rfl (.nil _))
      | inner sr rk rv rl rr =>
        obtain ⟨cost,trace,hcost⟩ := ihr (.right (recordTree l) (sz,⟨k,v⟩) :: ancestors)
        have up := Trace.step (Step.nav (.upRight (recordTree l)
          (recordTree (.inner sr rk rv rl rr)) (sz,⟨k,v⟩) ancestors)) (Trace.nil _)
        have full := Trace.read rfl (Trace.step
          (Step.nav (.right (recordTree l) (recordTree rl) (recordTree rr)
            (sz,⟨k,v⟩) (sr,⟨rk,rv⟩) ancestors)) (trace.append up))
        refine ⟨cost + 1 + 1 + 1,?_,?_⟩
        · simpa only [queryReads,if_pos hg,List.append_nil,recordTree,Nat.zero_add] using full
        · simp only [height] at hcost ⊢
          omega
    · cases l with
      | leaf =>
        refine ⟨1,?_,by simp only [height]; omega⟩
        simpa only [queryReads,if_neg hg] using
          (Trace.read (c := ⟨recordTree (.inner sz k v .leaf r),ancestors⟩) rfl (.nil _))
      | inner sl lk lv ll lr =>
        obtain ⟨cost,trace,hcost⟩ := ihl (.left (sz,⟨k,v⟩) (recordTree r) :: ancestors)
        have up := Trace.step (Step.nav (.upLeft
          (recordTree (.inner sl lk lv ll lr)) (recordTree r) (sz,⟨k,v⟩) ancestors)) (Trace.nil _)
        have full := Trace.read rfl (Trace.step
          (Step.nav (.left (recordTree ll) (recordTree lr) (recordTree r)
            (sl,⟨lk,lv⟩) (sz,⟨k,v⟩) ancestors)) (trace.append up))
        refine ⟨cost + 1 + 1 + 1,?_,?_⟩
        · simpa only [queryReads,if_neg hg,List.append_nil,recordTree,Nat.zero_add] using full
        · simp only [height] at hcost ⊢
          omega

theorem query_charged_log (good : Sigma β → Bool) (t : Impl α β)
    (ht : t.Balanced) (ancestors) :
    ∃ cost, Trace ⟨recordTree t,ancestors⟩ (queryReads good t)
      ⟨recordTree t,ancestors⟩ cost ∧ cost ≤ 9 * Nat.clog 2 (t.size + 1) := by
  obtain ⟨cost,trace,hcost⟩ := query_charged good t ancestors
  exact ⟨cost,trace,by have := balanced_height_log ht; omega⟩

end TangoSquared.Paper20261030.Auxiliary.Metadata
