import ChaCha.BSTExecution

/-!
# Monotone priority updates on a reached hull

The skeletons use their inorder order to identify the unchanged gaps.
Priorities of corresponding selected labels may increase. No boundary
inequality is assumed: it is derived from the old grafted max-heap.
-/

namespace ChaCha.MTR.Tree.PriorityHull

open ChaCha.MTR.Tree

variable {α β : Type*} [Preorder β]

def Bounded (w : α → β) (b : β) (t : Tree α) : Prop :=
  ∀ x ∈ inorder t, w x ≤ b

def Heap (w : α → β) : Tree α → Prop
  | .empty => True
  | .node l x r => Heap w l ∧ Heap w r ∧ Bounded w (w x) l ∧ Bounded w (w x) r

theorem Bounded.trans {w : α → β} {a b : β} {t : Tree α}
    (h : Bounded w a t) (hab : a ≤ b) : Bounded w b t := by
  intro x hx
  exact le_trans (h x hx) hab

theorem bounded_node {w : α → β} {b : β} {l r : Tree α} {x : α} :
    Bounded w b (.node l x r) ↔
      Bounded w b l ∧ w x ≤ b ∧ Bounded w b r := by
  simp only [Bounded, inorder, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Or.inl (Or.inl hy)),
      h x (Or.inl (Or.inr rfl)), fun y hy => h y (Or.inr hy)⟩
  · rintro ⟨hl, hx, hr⟩ y ((hy | hy) | hy)
    · exact hl y hy
    · subst y; exact hx
    · exact hr y hy

/-- Every gap is a heap; each adjacent selected label bounds that gap.
The duplicated condition at an internal gap records BOTH neighbors. -/
def GapCondition (w : α → β) (gaps : Nat → Tree α) : List α → Nat → Prop
  | [], start => Heap w (gaps start)
  | x :: xs, start => Heap w (gaps start) ∧
      Bounded w (w x) (gaps start) ∧ Bounded w (w x) (gaps (start + 1)) ∧
      GapCondition w gaps xs (start + 1)

theorem gapCondition_append (w : α → β) (gaps : Nat → Tree α)
    (xs ys : List α) (start : Nat) :
    GapCondition w gaps (xs ++ ys) start ↔
      GapCondition w gaps xs start ∧ GapCondition w gaps ys (start + xs.length) := by
  induction xs generalizing start with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero, GapCondition]
    cases ys <;> simp only [GapCondition]
    · exact ⟨fun h => ⟨h, h⟩, fun h => h.2⟩
    · tauto
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, GapCondition]
    rw [ih]
    have hi : start + 1 + xs.length = start + (xs.length + 1) := by omega
    rw [hi]
    tauto

theorem bounded_first_gap {w : α → β} {b : β} (t : Tree α)
    (gaps : Nat → Tree α) (start : Nat)
    (h : Bounded w b (graft t gaps start)) : Bounded w b (gaps start) := by
  induction t generalizing start with
  | empty => exact h
  | node l x r ihl ihr =>
    exact ihl _ ((bounded_node.mp h).1)

theorem bounded_last_gap {w : α → β} {b : β} (t : Tree α)
    (gaps : Nat → Tree α) (start : Nat)
    (h : Bounded w b (graft t gaps start)) :
    Bounded w b (gaps (start + size t)) := by
  induction t generalizing start with
  | empty => simpa only [size, Nat.add_zero, graft] using h
  | node l x r ihl ihr =>
    have hh := ihr (start + size l + 1) ((bounded_node.mp h).2.2)
    simpa only [size, Nat.add_assoc] using hh

/-- The source heap supplies the two actual inorder-neighbor bounds. -/
theorem gapCondition_of_heap_graft (w : α → β) (t : Tree α)
    (gaps : Nat → Tree α) (start : Nat)
    (h : Heap w (graft t gaps start)) : GapCondition w gaps (inorder t) start := by
  induction t generalizing start with
  | empty => exact h
  | node l x r ihl ihr =>
    rcases h with ⟨hl, hr, hbl, hbr⟩
    have gl := ihl start hl
    have gr := ihr (start + size l + 1) hr
    have bl := bounded_last_gap l gaps start hbl
    have br := bounded_first_gap r gaps (start + size l + 1) hbr
    rw [inorder, gapCondition_append, gapCondition_append]
    refine ⟨⟨gl, ?_⟩, ?_⟩
    · simp only [GapCondition, length_inorder]
      refine ⟨?_, bl, br, ?_⟩
      · have hh := (gapCondition_append w gaps (inorder l) [] start).mp
          (by simpa using gl)
        simpa only [List.length_nil, length_inorder, GapCondition] using hh.2
      · have hh := (gapCondition_append w gaps [] (inorder r)
          (start + size l + 1)).mp (by simpa using gr)
        exact hh.1
    · simpa only [List.length_append, List.length_singleton, length_inorder,
        Nat.add_assoc] using gr

theorem gapCondition_node_parts {w : α → β} {gaps : Nat → Tree α}
    {l r : Tree α} {x : α} {start : Nat}
    (h : GapCondition w gaps (inorder (.node l x r)) start) :
    GapCondition w gaps (inorder l) start ∧
      Bounded w (w x) (gaps (start + size l)) ∧
      Bounded w (w x) (gaps (start + size l + 1)) ∧
      GapCondition w gaps (inorder r) (start + size l + 1) := by
  rw [inorder, gapCondition_append, gapCondition_append] at h
  rcases h with ⟨⟨hl, hx⟩, hr⟩
  simp only [GapCondition, length_inorder] at hx
  refine ⟨hl, hx.2.1, hx.2.2.1, ?_⟩
  simpa only [List.length_append, List.length_singleton, length_inorder,
    Nat.add_assoc] using hr

/-- Raising the selected labels preserves every already established gap bound. -/
theorem gapCondition_mono {w : α → β} {gaps : Nat → Tree α}
    {xs ys : List α} (hxy : List.Forall₂ (fun x y => w x ≤ w y) xs ys)
    (start : Nat) (h : GapCondition w gaps xs start) :
    GapCondition w gaps ys start := by
  induction hxy generalizing start with
  | nil => exact h
  | @cons x y xs ys hle hrest ih =>
    rcases h with ⟨hh, hleft, hright, htail⟩
    exact ⟨hh, hleft.trans hle, hright.trans hle, ih _ htail⟩

/-- A common bound for the selected labels and the initial gap bounds the
entire graft. The other gap bounds follow from their adjacent labels. -/
theorem bounded_graft_of_gapCondition {w : α → β} {b : β}
    (t : Tree α) (gaps : Nat → Tree α) (start : Nat)
    (ht : Bounded w b t) (hg : GapCondition w gaps (inorder t) start)
    (hfirst : Bounded w b (gaps start)) : Bounded w b (graft t gaps start) := by
  induction t generalizing start with
  | empty => exact hfirst
  | node l x r ihl ihr =>
    rcases bounded_node.mp ht with ⟨hl, hx, hr⟩
    rcases gapCondition_node_parts hg with ⟨gl, _, br, gr⟩
    apply bounded_node.mpr
    exact ⟨ihl _ hl gl hfirst, hx, ihr _ hr gr (br.trans hx)⟩

/-- For a nonempty skeleton the first label bounds the initial gap. An empty
skeleton uses its final gap, which is the same gap. -/
theorem bounded_first_gap_of_gapCondition {w : α → β} {b : β}
    (t : Tree α) (gaps : Nat → Tree α) (start : Nat)
    (ht : Bounded w b t) (hg : GapCondition w gaps (inorder t) start)
    (hlast : Bounded w b (gaps (start + size t))) :
    Bounded w b (gaps start) := by
  cases horder : inorder t with
  | nil =>
    have hs : size t = 0 := by simpa only [horder, List.length_nil] using
      (length_inorder t).symm
    simpa only [hs, Nat.add_zero] using hlast
  | cons x xs =>
    rw [horder] at hg
    exact hg.2.1.trans (ht x (by simp only [horder, List.mem_cons, true_or]))

/-- Any heap-shaped skeleton satisfying the inherited inorder gap conditions
can be grafted onto those same gaps. -/
theorem heap_graft_of_gapCondition {w : α → β}
    (t : Tree α) (gaps : Nat → Tree α) (start : Nat)
    (ht : Heap w t) (hg : GapCondition w gaps (inorder t) start) :
    Heap w (graft t gaps start) := by
  induction t generalizing start with
  | empty => exact hg
  | node l x r ihl ihr =>
    rcases ht with ⟨hl, hr, hbl, hbr⟩
    rcases gapCondition_node_parts hg with ⟨gl, bl, br, gr⟩
    have first := bounded_first_gap_of_gapCondition l gaps start hbl gl bl
    exact ⟨ihl _ hl gl, ihr _ hr gr,
      bounded_graft_of_gapCondition l gaps start hbl gl first,
      bounded_graft_of_gapCondition r gaps (start + size l + 1) hbr gr br⟩

/-- Frontier-preserving hull repair with independently raised selected
priorities. Boundary inequalities are conclusions of the source heap, not
additional assumptions of this theorem. -/
theorem heap_graft_monotone {w : α → β}
    (source target : Tree α) (gaps : Nat → Tree α) (start : Nat)
    (hold : Heap w (graft source gaps start))
    (htarget : Heap w target)
    (hraise : List.Forall₂ (fun x y => w x ≤ w y)
      (inorder source) (inorder target)) :
    Heap w (graft target gaps start) := by
  apply heap_graft_of_gapCondition target gaps start htarget
  exact gapCondition_mono hraise start
    (gapCondition_of_heap_graft w source gaps start hold)

/-- The concrete label convention is `(actual key, cached priority)`.
Selected keys remain the same in inorder, their priorities increase, and all
cold labels (including their priorities) remain literally in the same gaps. -/
theorem repair_same_keys_raise_priorities {κ : Type*}
    (source target : Tree (κ × β)) (gaps : Nat → Tree (κ × β)) (start : Nat)
    (hold : Heap Prod.snd (graft source gaps start))
    (htarget : Heap Prod.snd target)
    (hraise : List.Forall₂ (fun x y : κ × β => x.1 = y.1 ∧ x.2 ≤ y.2)
      (inorder source) (inorder target)) :
    (inorder source).map Prod.fst = (inorder target).map Prod.fst ∧
      Heap Prod.snd (graft target gaps start) := by
  have hkeys : (inorder source).map Prod.fst = (inorder target).map Prod.fst := by
    generalize hs : inorder source = xs at hraise ⊢
    generalize ht : inorder target = ys at hraise ⊢
    clear hs ht
    induction hraise with
    | nil => rfl
    | cons h _ ih => simp only [List.map_cons, h.1, ih]
  have hmono : List.Forall₂ (fun x y : κ × β => x.2 ≤ y.2)
      (inorder source) (inorder target) := by
    generalize hs : inorder source = xs at hraise ⊢
    generalize ht : inorder target = ys at hraise ⊢
    clear hs ht
    induction hraise with
    | nil => exact .nil
    | cons h _ ih => exact .cons h.2 ih
  exact ⟨hkeys, heap_graft_monotone source target gaps start hold htarget hmono⟩

end ChaCha.MTR.Tree.PriorityHull
