import ChaCha.Paper20261030.AuxiliaryRotations
import ChaCha.Paper20261030.LocalObservations

/-!
# Local decisions for the actual auxiliary balancing routine

`Snapshot` is a bounded observation of an auxiliary tree. Its `unseen`
constructor exposes no information about the remaining subtree. A balance
plan is chosen from a snapshot, and its interpretation only rearranges
the indicated two or three pivots. Three observed levels suffice to choose
the plan; the fourth level also exposes the cached sizes needed to rebuild
all changed records. The final theorem charges an actual pointer tour that
reads the complete records, rather than just their keys.

This module does not yet compile cached-size writes into cursor operations.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ChaCha.MTR ChaCha.MTR.Pointer

variable {α : Type*} {β : α → Type*}

inductive Snapshot (α : Type*) (β : α → Type*) where
  | unseen
  | empty
  | node (size : Nat) (key : α) (value : β key) (left right : Snapshot α β)

def capture : Nat → Impl α β → Snapshot α β
  | 0, _ => .unseen
  | _ + 1, .leaf => .empty
  | depth + 1, .inner size key value l r =>
      .node size key value (capture depth l) (capture depth r)

def Snapshot.size : Snapshot α β → Nat
  | .node size _ _ _ _ => size
  | _ => 0

@[simp] theorem Snapshot.size_node (sz : Nat) (k : α) (v : β k) (l r : Snapshot α β) :
    (Snapshot.node sz k v l r).size = sz := rfl

@[simp] theorem Snapshot.size_empty : (Snapshot.empty : Snapshot α β).size = 0 := rfl

@[simp] theorem capture_size (depth : Nat) (t : Impl α β) :
    (capture (depth + 1) t).size = t.size := by cases t <;> rfl

inductive BalancePlan where
  | keep | singleLeft | singleRight | doubleLeft | doubleRight
  deriving DecidableEq, Repr

/-- This decision procedure cannot inspect anything below the snapshot. -/
def balancePlan : Snapshot α β → BalancePlan
  | .node _ _ _ l r =>
    if l.size + r.size ≤ 1 then .keep
    else if delta * l.size < r.size then
      match r with
      | .node _ _ _ rl rr =>
        if rl.size < ratio * rr.size then .singleLeft
        else match rl with
          | .node _ _ _ _ _ => .doubleLeft
          | _ => .singleLeft
      | _ => .keep
    else if delta * r.size < l.size then
      match l with
      | .node _ _ _ ll lr =>
        if lr.size < ratio * ll.size then .singleRight
        else match lr with
          | .node _ _ _ _ _ => .doubleRight
          | _ => .singleRight
      | _ => .keep
    else .keep
  | _ => .keep

/-- Apply a chosen rotation pattern. Subtrees below the pivots are opaque
operands: this operation does not traverse them. -/
def applyPlan (plan : BalancePlan) (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match plan, l, r with
  | .singleLeft, l, .inner _ rk rv rl rr => singleL k v l rk rv rl rr
  | .singleRight, .inner _ lk lv ll lr, r => singleR k v lk lv ll lr r
  | .doubleLeft, l, .inner _ rk rv (.inner _ mk mv ml mr) rr =>
      doubleL k v l rk rv mk mv ml mr rr
  | .doubleRight, .inner _ lk lv ll (.inner _ mk mv ml mr), r =>
      doubleR k v lk lv ll mk mv ml mr r
  | _, l, r => bin k v l r

theorem balancePlan_correct (k : α) (v : β k) (l r : Impl α β) :
    applyPlan (balancePlan (capture 3 (bin k v l r))) k v l r = balanceₘ k v l r := by
  simp only [capture, bin, balancePlan, capture_size]
  unfold balanceₘ
  split
  · rfl
  · split
    · cases r with
      | leaf =>
        have hz : (Impl.leaf : Impl α β).size = 0 := rfl
        omega
      | inner sz rk rv rl rr =>
        simp only [capture, capture_size, rotateL]
        split
        · rfl
        · cases rl <;> rfl
    · split
      · cases l with
        | leaf =>
          have hz : (Impl.leaf : Impl α β).size = 0 := rfl
          omega
        | inner sz lk lv ll lr =>
          simp only [capture, capture_size, rotateR]
          split
          · rfl
          · cases lr <;> rfl
      · rfl

theorem balancePlan_depth (depth : Nat) (k : α) (v : β k) (l r : Impl α β) :
    balancePlan (capture (depth + 3) (bin k v l r)) =
      balancePlan (capture 3 (bin k v l r)) := by
  simp only [Nat.add_assoc, capture, bin, balancePlan, capture_size]
  split
  · rfl
  · split
    · cases r with
      | leaf => rfl
      | inner sz rk rv rl rr =>
        simp only [capture, capture_size]
        split
        · rfl
        · cases rl <;> rfl
    · split
      · cases l with
        | leaf => rfl
        | inner sz lk lv ll lr =>
          simp only [capture, capture_size]
          split
          · rfl
          · cases lr <;> rfl
      · rfl

theorem applyPlan_pointer (plan : BalancePlan) (k : α) (v : β k) (l r : Impl α β) :
    Rearranges (erase (bin k v l r)) (erase (applyPlan plan k v l r)) 4 := by
  cases plan with
  | keep => exact rearranges_refl _ _
  | singleLeft =>
    cases r with
    | leaf => exact rearranges_refl _ _
    | inner => exact singleL_pointer _ _ _ _ _ _ _
  | singleRight =>
    cases l with
    | leaf => exact rearranges_refl _ _
    | inner => exact singleR_pointer _ _ _ _ _ _ _
  | doubleLeft =>
    cases r with
    | leaf => exact rearranges_refl _ _
    | inner sz rk rv rl rr =>
      cases rl with
      | leaf => exact rearranges_refl _ _
      | inner => exact doubleL_pointer _ _ _ _ _ _ _ _ _ _
  | doubleRight =>
    cases l with
    | leaf => exact rearranges_refl _ _
    | inner sz lk lv ll lr =>
      cases lr with
      | leaf => exact rearranges_refl _ _
      | inner => exact doubleR_pointer _ _ _ _ _ _ _ _ _ _

/-- All mutable and immutable fields stored at one auxiliary node. -/
abbrev NodeRecord (α : Type*) (β : α → Type*) := Nat × (Sigma β)

def recordTree : Impl α β → MTR.Tree (NodeRecord α β)
  | .leaf => .empty
  | .inner size key value l r => .node (recordTree l) (size, ⟨key,value⟩) (recordTree r)

def Snapshot.records : Snapshot α β → List (NodeRecord α β)
  | .unseen | .empty => []
  | .node size key value l r => (size, ⟨key,value⟩) :: (l.records ++ r.records)

theorem capture_records (depth : Nat) (t : Impl α β) :
    (capture depth t).records = localKeys depth (recordTree t) := by
  induction depth generalizing t with
  | zero => rfl
  | succ depth ih => cases t <;> simp [capture, Snapshot.records, recordTree, localKeys, ih]

/-- Every field used in the decision is actually read at its node, in a
tour returning to the original root. No whole-subtree observation occurs. -/
theorem balance_snapshot_tour (k : α) (v : β k) (l r : Impl α β)
    (ancestors : List (Frame (NodeRecord α β))) :
    ∃ cost, Trace ⟨recordTree (bin k v l r),ancestors⟩
      (capture 4 (bin k v l r)).records ⟨recordTree (bin k v l r),ancestors⟩ cost ∧
      cost ≤ 75 ∧
      applyPlan (balancePlan (capture 4 (bin k v l r))) k v l r = balanceₘ k v l r := by
  obtain ⟨cost, trace, hcost⟩ := four_level_tour (recordTree (bin k v l r)) ancestors
  refine ⟨cost, ?_, hcost, ?_⟩
  · simpa only [capture_records] using trace
  · rw [balancePlan_depth 1, balancePlan_correct]

end ChaCha.Paper20261030.Auxiliary
