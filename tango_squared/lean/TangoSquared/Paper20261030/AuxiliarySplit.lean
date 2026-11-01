import TangoSquared.Paper20261030.AuxiliaryJoin

/-!
# Concrete successful splitting of a balanced auxiliary tree

`splitAt` exposes an existing key and produces balanced trees on either
side. It uses the actual verified library join while unwinding search.
This file first establishes the construction and exact size accounting;
the sharp amortized cost of a sequence of such splits is a separate task.
-/

namespace TangoSquared.Paper20261030.Auxiliary

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open TangoSquared.MTR TangoSquared.MTR.Pointer

variable {α : Type*} {β : α → Type*}

structure SplitResult (β : α → Type*) (x : α) where
  value : β x
  left : Impl α β
  right : Impl α β
  left_balanced : left.Balanced
  right_balanced : right.Balanced

def SplitResult.impl {x : α} (s : SplitResult β x) : Impl α β :=
  bin x s.value s.left s.right

def splitAt [Ord α] [LawfulEqOrd α] (x : α) :
    (t : Impl α β) → t.Balanced → searchResult x t = true → SplitResult β x
  | .leaf, _, hf => False.elim (by simp [searchResult] at hf)
  | .inner _ k v l r, ht, hf =>
    match hc : compare x k with
    | .eq =>
      ⟨cast (congrArg β (compare_eq_iff_eq.mp hc).symm) v,l,r,ht.left,ht.right⟩
    | .lt =>
      let s := splitAt x l ht.left (by simpa [searchResult,hc] using hf)
      let joined := link k v s.right r s.right_balanced ht.right
      ⟨s.value,s.left,joined.impl,s.left_balanced,joined.balanced_impl⟩
    | .gt =>
      let s := splitAt x r ht.right (by simpa [searchResult,hc] using hf)
      let joined := link k v l s.left ht.left s.left_balanced
      ⟨s.value,joined.impl,s.right,joined.balanced_impl,s.right_balanced⟩

theorem splitAt_size [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) :
    (splitAt x t ht hf).left.size + 1 + (splitAt x t ht hf).right.size = t.size := by
  induction t with
  | leaf => simp [searchResult] at hf
  | inner sz k v l r ihl ihr =>
    have hs := ht.eq
    cases hc : compare x k with
    | eq =>
      rw [splitAt]
      split <;> simp_all [Impl.size_inner]
    | lt =>
      have fl : searchResult x l = true := by simpa [searchResult,hc] using hf
      have il := ihl ht.left fl
      have hj := (link k v (splitAt x l ht.left fl).right r
        (splitAt x l ht.left fl).right_balanced ht.right).size_impl
      rw [splitAt]
      split <;> simp_all [Impl.size_inner] <;> omega
    | gt =>
      have fr : searchResult x r = true := by simpa [searchResult,hc] using hf
      have ir := ihr ht.right fr
      have hj := (link k v l (splitAt x r ht.right fr).left
        ht.left (splitAt x r ht.right fr).left_balanced).size_impl
      rw [splitAt]
      split <;> simp_all [Impl.size_inner] <;> omega

theorem splitAt_left_tree [Ord α] [LawfulEqOrd α] (x : α) {sz : Nat} {k : α} {v : β k}
    {l r : Impl α β} (ht : (Impl.inner sz k v l r).Balanced)
    (hf : searchResult x (.inner sz k v l r) = true) (hc : compare x k = .lt)
    (fl : searchResult x l = true) :
    erase (splitAt x (.inner sz k v l r) ht hf).impl =
      .node (erase (splitAt x l ht.left fl).left) x
        (erase (link k v (splitAt x l ht.left fl).right r
          (splitAt x l ht.left fl).right_balanced ht.right).impl) := by
  rw [splitAt]
  split <;> rename_i hb <;> simp [hc] at hb
  rfl

theorem splitAt_right_tree [Ord α] [LawfulEqOrd α] (x : α) {sz : Nat} {k : α} {v : β k}
    {l r : Impl α β} (ht : (Impl.inner sz k v l r).Balanced)
    (hf : searchResult x (.inner sz k v l r) = true) (hc : compare x k = .gt)
    (fr : searchResult x r = true) :
    erase (splitAt x (.inner sz k v l r) ht hf).impl =
      .node (erase (link k v l (splitAt x r ht.right fr).left
          ht.left (splitAt x r ht.right fr).left_balanced).impl) x
        (erase (splitAt x r ht.right fr).right) := by
  rw [splitAt]
  split <;> rename_i hb <;> simp [hc] at hb
  rfl

theorem splitAt_root_tree [Ord α] [LawfulEqOrd α] (x : α) {sz : Nat} {k : α} {v : β k}
    {l r : Impl α β} (ht : (Impl.inner sz k v l r).Balanced)
    (hf : searchResult x (.inner sz k v l r) = true) (hc : compare x k = .eq) :
    erase (splitAt x (.inner sz k v l r) ht hf).impl = erase (.inner sz k v l r) := by
  have hx := compare_eq_iff_eq.mp hc
  rw [splitAt]
  split <;> rename_i hb <;> simp [hc] at hb
  simp only [SplitResult.impl,bin,erase,hx]

/-- A direct cost bound for the concrete splitting algorithm. This bound
is intentionally intermediate: it charges every join separately and is
quadratic in the logarithm. It does not establish the manuscript's sharp
split/join amortization. -/
theorem splitAt_pointer [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true) (N : Nat) (hN : t.size ≤ N) :
    Rearranges (erase t) (erase (splitAt x t ht hf).impl)
      ((42 * Nat.clog 2 (N + 1) + 8) * height t) := by
  induction t with
  | leaf => simp [searchResult] at hf
  | inner sz k v l r ihl ihr =>
    have hs := ht.eq
    have hn : sz ≤ N := hN
    cases hc : compare x k with
    | eq =>
      rw [splitAt_root_tree x ht hf hc]
      exact rearranges_refl _ _
    | lt =>
      have fl : searchResult x l = true := by simpa [searchResult,hc] using hf
      let s := splitAt x l ht.left fl
      have ss : s.left.size + 1 + s.right.size = l.size := splitAt_size x l ht.left fl
      have hlne : erase l ≠ .empty := by cases l <;> simp_all [erase,searchResult]
      have first := (ihl ht.left fl (by omega)).left (k := k) (r := erase r) hlne
      have turn := singleR_pointer k v x s.value s.left s.right r
      have join := (link_pointer_log k v s.right r s.right_balanced ht.right).right
        (l := erase s.left) (k := x) (by simp [erase,bin])
      have all := (first.trans turn).trans join
      rw [splitAt_left_tree x ht hf hc fl]
      apply all.mono
      have hlog₁ := Nat.clog_monotone 2 (show s.right.size + 1 ≤ N + 1 by omega)
      have hlog₂ := Nat.clog_monotone 2 (show r.size + 1 ≤ N + 1 by omega)
      have hmul := Nat.mul_le_mul_left (42 * Nat.clog 2 (N + 1) + 8)
        (Nat.le_max_left (height l) (height r))
      simp only [height,Nat.mul_add,Nat.mul_one]
      omega
    | gt =>
      have fr : searchResult x r = true := by simpa [searchResult,hc] using hf
      let s := splitAt x r ht.right fr
      have ss : s.left.size + 1 + s.right.size = r.size := splitAt_size x r ht.right fr
      have hrne : erase r ≠ .empty := by cases r <;> simp_all [erase,searchResult]
      have first := (ihr ht.right fr (by omega)).right (l := erase l) (k := k) hrne
      have turn := singleL_pointer k v l x s.value s.left s.right
      have join := (link_pointer_log k v l s.left ht.left s.left_balanced).left
        (r := erase s.right) (k := x) (by simp [erase,bin])
      have all := (first.trans turn).trans join
      rw [splitAt_right_tree x ht hf hc fr]
      apply all.mono
      have hlog₁ := Nat.clog_monotone 2 (show l.size + 1 ≤ N + 1 by omega)
      have hlog₂ := Nat.clog_monotone 2 (show s.left.size + 1 ≤ N + 1 by omega)
      have hmul := Nat.mul_le_mul_left (42 * Nat.clog 2 (N + 1) + 8)
        (Nat.le_max_right (height l) (height r))
      simp only [height,Nat.mul_add,Nat.mul_one]
      omega

end TangoSquared.Paper20261030.Auxiliary
