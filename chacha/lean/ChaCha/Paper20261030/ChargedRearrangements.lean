import ChaCha.Paper20261030.ChargedInsertion

/-!
# Composition and child excursions for charged record traces

Lifting an operation below a pivot preserves the pivot's cached size.
The `bin_left` and `bin_right` forms therefore require the operation to
preserve the child's size. Forced single rotations read the records used
to compute the new caches before applying the verified updates.
-/

namespace ChaCha.Paper20261030.Auxiliary.Metadata

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ChaCha.MTR

variable {α : Type*} {β : α → Type*}

theorem ObservedRearranges.mono {a b : Impl α β} {m n : Nat}
    (h : ObservedRearranges a b m) (hle : m ≤ n) : ObservedRearranges a b n := by
  intro ancestors
  obtain ⟨word,cost,trace,hcost⟩ := h ancestors
  exact ⟨word,cost,trace,hcost.trans hle⟩

theorem ObservedRearranges.trans {a b c : Impl α β} {m n : Nat}
    (h : ObservedRearranges a b m) (g : ObservedRearranges b c n) :
    ObservedRearranges a c (m + n) := by
  intro ancestors
  obtain ⟨hw,hc,ht,hb⟩ := h ancestors
  obtain ⟨gw,gc,gt,gb⟩ := g ancestors
  exact ⟨_,_,ht.append gt,Nat.add_le_add hb gb⟩

theorem ObservedRearranges.left {a b r : Impl α β} {k : α} {v : β k} {old n : Nat}
    (h : ObservedRearranges a b n) (ha : a ≠ .leaf) :
    ObservedRearranges (.inner old k v a r) (.inner old k v b r) (n + 2) := by
  cases a with
  | leaf => exact False.elim (ha rfl)
  | inner sz ak av al ar =>
    intro ancestors
    obtain ⟨word,cost,trace,hcost⟩ := h (.left (old,⟨k,v⟩) (recordTree r) :: ancestors)
    have up : Trace ⟨recordTree b,.left (old,⟨k,v⟩) (recordTree r) :: ancestors⟩ []
        ⟨recordTree (.inner old k v b r),ancestors⟩ 1 :=
      .step (.nav (.upLeft (recordTree b) (recordTree r) (old,⟨k,v⟩) ancestors)) (.nil _)
    have full := Trace.step (.nav (.left (recordTree al) (recordTree ar) (recordTree r)
      (sz,⟨ak,av⟩) (old,⟨k,v⟩) ancestors)) (trace.append up)
    exact ⟨_,_,full,by omega⟩

theorem ObservedRearranges.right {l a b : Impl α β} {k : α} {v : β k} {old n : Nat}
    (h : ObservedRearranges a b n) (ha : a ≠ .leaf) :
    ObservedRearranges (.inner old k v l a) (.inner old k v l b) (n + 2) := by
  cases a with
  | leaf => exact False.elim (ha rfl)
  | inner sz ak av al ar =>
    intro ancestors
    obtain ⟨word,cost,trace,hcost⟩ := h (.right (recordTree l) (old,⟨k,v⟩) :: ancestors)
    have up : Trace ⟨recordTree b,.right (recordTree l) (old,⟨k,v⟩) :: ancestors⟩ []
        ⟨recordTree (.inner old k v l b),ancestors⟩ 1 :=
      .step (.nav (.upRight (recordTree l) (recordTree b) (old,⟨k,v⟩) ancestors)) (.nil _)
    have full := Trace.step (.nav (.right (recordTree l) (recordTree al) (recordTree ar)
      (old,⟨k,v⟩) (sz,⟨ak,av⟩) ancestors)) (trace.append up)
    exact ⟨_,_,full,by omega⟩

theorem ObservedRearranges.bin_left {a b r : Impl α β} {k : α} {v : β k} {n : Nat}
    (h : ObservedRearranges a b n) (ha : a ≠ .leaf) (hs : a.size = b.size) :
    ObservedRearranges (bin k v a r) (bin k v b r) (n + 2) := by
  simpa only [bin,hs] using h.left (old := a.size + 1 + r.size) (r := r) (k := k) (v := v) ha

theorem ObservedRearranges.bin_right {l a b : Impl α β} {k : α} {v : β k} {n : Nat}
    (h : ObservedRearranges a b n) (ha : a ≠ .leaf) (hs : a.size = b.size) :
    ObservedRearranges (bin k v l a) (bin k v l b) (n + 2) := by
  simpa only [bin,hs] using h.right (old := l.size + 1 + a.size) (l := l) (k := k) (v := v) ha

theorem singleL_observed (k : α) (v : β k) (l : Impl α β)
    (rk : α) (rv : β rk) (rl rr : Impl α β) :
    ObservedRearranges (bin k v l (bin rk rv rl rr)) (singleL k v l rk rv rl rr) 86 := by
  intro ancestors
  obtain ⟨rc,reads,hrc⟩ := snapshot_charged (bin k v l (bin rk rv rl rr)) ancestors
  obtain ⟨wc,writes,hwc⟩ := singleL_repairs k v l (rl.size + 1 + rr.size) rk rv rl rr ancestors
  exact ⟨_,_,reads.append writes,by omega⟩

theorem singleR_observed (k : α) (v : β k) (lk : α) (lv : β lk)
    (ll lr r : Impl α β) :
    ObservedRearranges (bin k v (bin lk lv ll lr) r) (singleR k v lk lv ll lr r) 86 := by
  intro ancestors
  obtain ⟨rc,reads,hrc⟩ := snapshot_charged (bin k v (bin lk lv ll lr) r) ancestors
  obtain ⟨wc,writes,hwc⟩ := singleR_repairs k v (ll.size + 1 + lr.size) lk lv ll lr r ancestors
  exact ⟨_,_,reads.append writes,by omega⟩

end ChaCha.Paper20261030.Auxiliary.Metadata
