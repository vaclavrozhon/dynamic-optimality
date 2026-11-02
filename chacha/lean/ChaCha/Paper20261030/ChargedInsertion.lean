import ChaCha.Paper20261030.ChargedBalance
import ChaCha.Paper20261030.AuxiliaryInsertion

/-!
# Boundary insertion with charged record operations

The separator is already a physical vertex. A recursive call observes a
bounded neighborhood, rotates this separator into a child, recurses, and
rebalances the old root. Cached sizes may be stale at the separator on
entry; every correction is charged at the record being updated. The
observation words below are internal reads, not user requests.
-/

namespace ChaCha.Paper20261030.Auxiliary.Metadata

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ChaCha.MTR

variable {α : Type*} {β : α → Type*}

def ObservedRearranges (before after : Impl α β) (budget : Nat) : Prop :=
  ∀ ancestors : List (Pointer.Frame (NodeRecord α β)), ∃ reads cost,
    Trace ⟨recordTree before,ancestors⟩ reads ⟨recordTree after,ancestors⟩ cost ∧ cost ≤ budget

theorem snapshot_charged (t : Impl α β) (ancestors) :
    ∃ cost, Trace ⟨recordTree t,ancestors⟩ (capture 4 t).records
      ⟨recordTree t,ancestors⟩ cost ∧ cost ≤ 75 := by
  obtain ⟨cost,trace,bound⟩ := four_level_tour (recordTree t) ancestors
  exact ⟨cost,by simpa only [capture_records] using Trace.ofPointer trace,bound⟩

theorem refresh_charged (old : Nat) (k : α) (v : β k) (l r : Impl α β) :
    ObservedRearranges (.inner old k v l r) (bin k v l r) 76 := by
  intro ancestors
  obtain ⟨rc,reads,hrc⟩ := snapshot_charged (.inner old k v l r) ancestors
  have update : Trace ⟨recordTree (.inner old k v l r),ancestors⟩ []
      ⟨recordTree (bin k v l r),ancestors⟩ 1 :=
    .step (.write (recordTree l) (recordTree r) old (l.size + 1 + r.size) ⟨k,v⟩ ancestors) (.nil _)
  exact ⟨_,rc + 1,reads.append update,by omega⟩

theorem balanceL_existing_charged (old : Nat) (k : α) (v : β k)
    (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced)
    (hp : BalanceLPrecond l.size r.size) (ancestors) :
    ∃ cost, Trace ⟨recordTree (.inner old k v l r),ancestors⟩
      (capture 4 (.inner old k v l r)).records
      ⟨recordTree (balanceL k v l r hl hr hp),ancestors⟩ cost ∧ cost ≤ 87 := by
  rw [balanceL_eq_balanceLErase]
  exact balanceLErase_existing_charged _ _ _ _ _ _ _ _ _

theorem balanceR_existing_charged (old : Nat) (k : α) (v : β k)
    (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced)
    (hp : BalanceLPrecond r.size l.size) (ancestors) :
    ∃ cost, Trace ⟨recordTree (.inner old k v l r),ancestors⟩
      (capture 4 (.inner old k v l r)).records
      ⟨recordTree (balanceR k v l r hl hr hp),ancestors⟩ cost ∧ cost ≤ 87 := by
  rw [balanceR_eq_balanceRErase]
  exact balanceRErase_existing_charged _ _ _ _ _ _ _ _ _

theorem insertMin_charged (old : Nat) (k : α) (v : β k)
    (t : Impl α β) (ht : t.Balanced) :
    ObservedRearranges (.inner old k v .leaf t) (insertMin k v t ht).impl
      (165 * height t + 76) := by
  induction t with
  | leaf => exact refresh_charged old k v .leaf .leaf
  | inner sz rk rv l r ihl ihr =>
    let d := insertMin k v l ht.left
    have hp : BalanceLPrecond d.impl.size r.size := by
      right
      rw [d.size_impl]
      exact ⟨by omega,by simpa using ht.at_root⟩
    have hout : (insertMin k v (.inner sz rk rv l r) ht).impl =
        balanceL rk rv d.impl r d.balanced_impl ht.right hp := by rw [insertMin]
    intro ancestors
    obtain ⟨rc,reads,hrc⟩ := snapshot_charged (.inner old k v .leaf (.inner sz rk rv l r)) ancestors
    obtain ⟨word,cost,trace,hcost⟩ := ihl ht.left (.left (sz,⟨rk,rv⟩) (recordTree r) :: ancestors)
    obtain ⟨bc,bt,hbc⟩ := balanceL_existing_charged sz rk rv d.impl r d.balanced_impl ht.right hp ancestors
    have up : Trace ⟨recordTree d.impl,.left (sz,⟨rk,rv⟩) (recordTree r) :: ancestors⟩ []
        ⟨recordTree (.inner sz rk rv d.impl r),ancestors⟩ 1 :=
      .step (.nav (.upLeft (recordTree d.impl) (recordTree r) (sz,⟨rk,rv⟩) ancestors)) (.nil _)
    have tail := trace.append (up.append bt)
    have full := Trace.step
      (Step.nav (.rotateLeft .empty (recordTree l) (recordTree r) (old,⟨k,v⟩) (sz,⟨rk,rv⟩) ancestors))
      (Trace.step (Step.nav (.left .empty (recordTree l) (recordTree r)
        (old,⟨k,v⟩) (sz,⟨rk,rv⟩) ancestors)) tail)
    rw [hout]
    refine ⟨_,_,reads.append full,?_⟩
    simp only [height]
    omega

theorem insertMax_charged (old : Nat) (k : α) (v : β k)
    (t : Impl α β) (ht : t.Balanced) :
    ObservedRearranges (.inner old k v t .leaf) (insertMax k v t ht).impl
      (165 * height t + 76) := by
  induction t with
  | leaf => exact refresh_charged old k v .leaf .leaf
  | inner sz lk lv l r ihl ihr =>
    let d := insertMax k v r ht.right
    have hp : BalanceLPrecond d.impl.size l.size := by
      right
      rw [d.size_impl]
      exact ⟨by omega,by simpa using ht.at_root.symm⟩
    have hout : (insertMax k v (.inner sz lk lv l r) ht).impl =
        balanceR lk lv l d.impl ht.left d.balanced_impl hp := by rw [insertMax]
    intro ancestors
    obtain ⟨rc,reads,hrc⟩ := snapshot_charged (.inner old k v (.inner sz lk lv l r) .leaf) ancestors
    obtain ⟨word,cost,trace,hcost⟩ := ihr ht.right (.right (recordTree l) (sz,⟨lk,lv⟩) :: ancestors)
    obtain ⟨bc,bt,hbc⟩ := balanceR_existing_charged sz lk lv l d.impl ht.left d.balanced_impl hp ancestors
    have up : Trace ⟨recordTree d.impl,.right (recordTree l) (sz,⟨lk,lv⟩) :: ancestors⟩ []
        ⟨recordTree (.inner sz lk lv l d.impl),ancestors⟩ 1 :=
      .step (.nav (.upRight (recordTree l) (recordTree d.impl) (sz,⟨lk,lv⟩) ancestors)) (.nil _)
    have tail := trace.append (up.append bt)
    have full := Trace.step
      (Step.nav (.rotateRight (recordTree l) (recordTree r) .empty (sz,⟨lk,lv⟩) (old,⟨k,v⟩) ancestors))
      (Trace.step (Step.nav (.right (recordTree l) (recordTree r) .empty
        (sz,⟨lk,lv⟩) (old,⟨k,v⟩) ancestors)) tail)
    rw [hout]
    refine ⟨_,_,reads.append full,?_⟩
    simp only [height]
    omega

theorem insertMin_charged_log (old : Nat) (k : α) (v : β k)
    (t : Impl α β) (ht : t.Balanced) :
    ObservedRearranges (.inner old k v .leaf t) (insertMin k v t ht).impl
      (495 * Nat.clog 2 (t.size + 1) + 76) := by
  intro ancestors
  obtain ⟨word,cost,trace,bound⟩ := insertMin_charged old k v t ht ancestors
  exact ⟨word,cost,trace,by have := balanced_height_log ht; omega⟩

theorem insertMax_charged_log (old : Nat) (k : α) (v : β k)
    (t : Impl α β) (ht : t.Balanced) :
    ObservedRearranges (.inner old k v t .leaf) (insertMax k v t ht).impl
      (495 * Nat.clog 2 (t.size + 1) + 76) := by
  intro ancestors
  obtain ⟨word,cost,trace,bound⟩ := insertMax_charged old k v t ht ancestors
  exact ⟨word,cost,trace,by have := balanced_height_log ht; omega⟩

end ChaCha.Paper20261030.Auxiliary.Metadata
