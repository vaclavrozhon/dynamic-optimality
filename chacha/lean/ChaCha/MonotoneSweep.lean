import ChaCha.Words
import ChaCha.MTR

/-!
# A rotation-stable potential for a monotone finger sweep

The pending scan word is a subsequence of the fixed inorder word. Each
subtree cut crosses that word at most twice. A rotation replaces exactly
one subtree cut; consuming a scan step spends its cut distance exactly.

This structural kernel uses actual tree rotations. The identification of
cut distance with ordinary tree distance and the constant-finger BST
simulation used by the moving-port wrapper remain separate hand arguments.
-/

namespace ChaCha.MTR.Tree.MonotoneSweep

variable {α : Type*} [DecidableEq α]

theorem changesFrom_replicate_same (a : α) (k : Nat) :
    changesFrom a (List.replicate k a) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem alternations_replicate (a : α) (k : Nat) :
    alternations (List.replicate k a) = 0 := by
  cases k with
  | zero => rfl
  | succ k => simpa [List.replicate_succ, alternations] using
      changesFrom_replicate_same a k

theorem changesFrom_le_alternations_one (a : α) (xs : List α) :
    changesFrom a xs ≤ alternations xs + 1 := by
  cases xs with
  | nil => simp
  | cons b bs =>
      simp only [changesFrom, alternations]
      unfold edgeChange
      split_ifs <;> omega

theorem alternations_append_le (xs ys : List α) :
    alternations (xs ++ ys) ≤ alternations xs + alternations ys + 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      cases xs with
      | nil =>
          simpa [alternations] using changesFrom_le_alternations_one a ys
      | cons b bs =>
          simpa only [List.cons_append, alternations_cons_cons, Nat.add_assoc] using
            Nat.add_le_add_left ih (edgeChange a b)

theorem alternations_three_constant_blocks (a b c : α) (i j k : Nat) :
    alternations (List.replicate i a ++ List.replicate j b ++
      List.replicate k c) ≤ 2 := by
  have h₁ := alternations_append_le (List.replicate i a) (List.replicate j b)
  have h₂ := alternations_append_le
    (List.replicate i a ++ List.replicate j b) (List.replicate k c)
  simp only [alternations_replicate] at h₁ h₂
  omega

def cutWord (inside xs : List α) : List Bool :=
  xs.map (fun x => decide (x ∈ inside))

def cutCharge (inside xs : List α) : Nat := alternations (cutWord inside xs)

theorem cutWord_blocks (pre inside post : List α)
    (hn : (pre ++ inside ++ post).Nodup) :
    cutWord inside (pre ++ inside ++ post) =
      List.replicate pre.length false ++ List.replicate inside.length true ++
        List.replicate post.length false := by
  have hpi := (List.nodup_append.mp (List.nodup_append.mp hn).1).2.2
  have hip := (List.nodup_append.mp hn).2.2
  have hp : pre.map (fun x => decide (x ∈ inside)) =
      List.replicate pre.length false := by
    apply List.map_eq_replicate_iff.mpr
    intro x hx
    have hnot : x ∉ inside := fun hi => hpi x hx x hi rfl
    simp [hnot]
  have hi : inside.map (fun x => decide (x ∈ inside)) =
      List.replicate inside.length true := by
    apply List.map_eq_replicate_iff.mpr
    intro x hx
    simp [hx]
  have hz : post.map (fun x => decide (x ∈ inside)) =
      List.replicate post.length false := by
    apply List.map_eq_replicate_iff.mpr
    intro x hx
    have hnot : x ∉ inside := fun hi =>
      hip x (List.mem_append_right pre hi) x hx rfl
    simp [hnot]
  simp only [cutWord, List.map_append, hp, hi, hz]

theorem cutCharge_le_two {global inside xs : List α}
    (hn : global.Nodup) (hi : inside <:+: global) (hx : xs.Sublist global) :
    cutCharge inside xs ≤ 2 := by
  obtain ⟨pre, post, rfl⟩ := hi
  have hm := alternations_sublist (hx.map (fun x => decide (x ∈ inside)))
  change cutCharge inside xs ≤ cutCharge inside (pre ++ inside ++ post) at hm
  refine hm.trans ?_
  unfold cutCharge
  rw [cutWord_blocks pre inside post hn]
  exact alternations_three_constant_blocks false true false _ _ _

def potential (xs : List α) : Tree α → Nat
  | .empty => 0
  | t@(.node l _ r) => potential xs l + cutCharge (inorder t) xs + potential xs r

def cutDistance (x y : α) : Tree α → Nat
  | .empty => 0
  | t@(.node l _ r) => cutDistance x y l +
      edgeChange (decide (x ∈ inorder t)) (decide (y ∈ inorder t)) +
      cutDistance x y r

theorem potential_cons_cons (x y : α) (xs : List α) (t : Tree α) :
    potential (x :: y :: xs) t = cutDistance x y t + potential (y :: xs) t := by
  induction t with
  | empty => rfl
  | node l a r ihl ihr =>
      simp only [potential, cutDistance, cutCharge, cutWord, List.map_cons,
        alternations_cons_cons, ihl, ihr]
      omega

omit [DecidableEq α] in
theorem inorder_left_infix (l r : Tree α) (a : α) :
    inorder l <:+: inorder (.node l a r) := by
  exact ⟨[], [a] ++ inorder r, by simp [inorder, List.append_assoc]⟩

omit [DecidableEq α] in
theorem inorder_right_infix (l r : Tree α) (a : α) :
    inorder r <:+: inorder (.node l a r) := by
  exact ⟨inorder l ++ [a], [], by simp [inorder]⟩

theorem potential_le_twice_size {global xs : List α} (t : Tree α)
    (hn : global.Nodup) (ht : inorder t <:+: global) (hx : xs.Sublist global) :
    potential xs t ≤ 2 * size t := by
  induction t with
  | empty => simp [potential, size]
  | node l a r ihl ihr =>
      have hl := ihl ((inorder_left_infix l r a).trans ht)
      have hr := ihr ((inorder_right_infix l r a).trans ht)
      have hc := cutCharge_le_two hn ht hx
      simp only [potential, size]
      omega

theorem root_left_identity (A B C : Tree α) (a b : α) (xs : List α) :
    potential xs (.node (.node A a B) b C) +
        cutCharge (inorder (.node B b C)) xs =
      potential xs (.node A a (.node B b C)) +
        cutCharge (inorder (.node A a B)) xs := by
  simp only [potential, inorder, List.append_assoc]
  omega

/-- One ordinary rotation, at an arbitrary subtree of the physical tree. -/
inductive Rotation : Tree α → Tree α → Prop
  | left (A B C : Tree α) (a b : α) :
      Rotation (.node A a (.node B b C)) (.node (.node A a B) b C)
  | right (A B C : Tree α) (a b : α) :
      Rotation (.node (.node A a B) b C) (.node A a (.node B b C))
  | inLeft {s t : Tree α} (h : Rotation s t) (a : α) (r : Tree α) :
      Rotation (.node s a r) (.node t a r)
  | inRight {s t : Tree α} (h : Rotation s t) (l : Tree α) (a : α) :
      Rotation (.node l a s) (.node l a t)

omit [DecidableEq α] in
theorem Rotation.inorder_eq {s t : Tree α} (h : Rotation s t) :
    inorder s = inorder t := by
  induction h with
  | left => simp [inorder, List.append_assoc]
  | right => simp [inorder, List.append_assoc]
  | inLeft h a r ih => simp only [inorder, ih]
  | inRight h l a ih => simp only [inorder, ih]

theorem Rotation.potential_le {s t : Tree α} (h : Rotation s t)
    {global xs : List α} (hn : global.Nodup)
    (hs : inorder s <:+: global) (hx : xs.Sublist global) :
    potential xs t ≤ potential xs s + 2 := by
  induction h generalizing global xs with
  | left A B C a b =>
      have hi : inorder (.node A a B) <:+: inorder (.node A a (.node B b C)) := by
        exact ⟨[], [b] ++ inorder C, by simp [inorder, List.append_assoc]⟩
      have hc := cutCharge_le_two hn (hi.trans hs) hx
      have hid := root_left_identity A B C a b xs
      omega
  | right A B C a b =>
      have hi : inorder (.node B b C) <:+: inorder (.node (.node A a B) b C) := by
        exact ⟨inorder A ++ [a], [], by simp [inorder, List.append_assoc]⟩
      have hc := cutCharge_le_two hn (hi.trans hs) hx
      have hid := root_left_identity A B C a b xs
      omega
  | @inLeft s t h a r ih =>
      have hb := ih hn ((inorder_left_infix s r a).trans hs) hx
      have he := h.inorder_eq
      simp only [potential, inorder]
      rw [← he]
      omega
  | @inRight s t h l a ih =>
      have hb := ih hn ((inorder_right_infix l s a).trans hs) hx
      have he := h.inorder_eq
      simp only [potential, inorder]
      rw [← he]
      omega

/-- Interleave arbitrary physical rotations with successive scan steps.
The scan movement is charged by the exact subtree-cut metric. -/
inductive ScanRun : List α → Tree α → Nat → Nat → List α → Tree α → Prop
  | done (xs : List α) (t : Tree α) : ScanRun xs t 0 0 xs t
  | rotate {xs ys : List α} {s t u : Tree α} {work rotations : Nat}
      (h : Rotation s t) (rest : ScanRun xs t work rotations ys u) :
      ScanRun xs s work (rotations + 1) ys u
  | advance {x y : α} {xs ys : List α} {s t : Tree α} {work rotations : Nat}
      (rest : ScanRun (y :: xs) s work rotations ys t) :
      ScanRun (x :: y :: xs) s (cutDistance x y s + work) rotations ys t

theorem ScanRun.accounting {xs ys : List α} {s t : Tree α} {work rotations : Nat}
    (h : ScanRun xs s work rotations ys t)
    (hn : (inorder s).Nodup) (hx : xs.Sublist (inorder s)) :
    work + potential ys t ≤ potential xs s + 2 * rotations := by
  induction h with
  | done => simp
  | @rotate xs ys s t u work rotations hr rest ih =>
      have he := hr.inorder_eq
      have hb := ih (he ▸ hn) (he ▸ hx)
      have hp := hr.potential_le hn (List.infix_refl _) hx
      omega
  | @advance x y xs ys s t work rotations rest ih =>
      have ht : (y :: xs).Sublist (inorder s) :=
        (List.sublist_cons_self _ _).trans hx
      have hb := ih hn ht
      rw [potential_cons_cons]
      omega

/-- Over an entire monotone sweep, rotations replenish at most two units
of scan work each; the initial reserve is at most twice the host size. -/
theorem ScanRun.work_le {xs ys : List α} {s t : Tree α} {work rotations : Nat}
    (h : ScanRun xs s work rotations ys t)
    (hn : (inorder s).Nodup) (hx : xs.Sublist (inorder s)) :
    work ≤ 2 * size s + 2 * rotations := by
  have ha := h.accounting hn hx
  have hp := potential_le_twice_size s hn (List.infix_refl _) hx
  omega

end ChaCha.MTR.Tree.MonotoneSweep
