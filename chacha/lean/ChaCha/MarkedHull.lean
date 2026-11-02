import ChaCha.PointerModel

/-!
# The marked-hull potential for a monotone stack

`hullSize marked t` counts the vertices of the rooted subtree connecting
all marked keys.  Popping all marks below a query and retaining all marks
above it yields a potential drop that pays for the popped-key hull.

These are actual ordered-tree potential lemmas.  The legal sorted-hull
simulation and its application to comb emissions are not formalized here.
-/

namespace ChaCha.MTR.Tree

variable {α : Type*}

def hasMark (marked : α → Bool) : Tree α → Bool
  | .empty => false
  | .node l a r => hasMark marked l || marked a || hasMark marked r

def hullSize (marked : α → Bool) : Tree α → Nat
  | .empty => 0
  | .node l a r =>
      hullSize marked l + hullSize marked r +
        if hasMark marked (.node l a r) then 1 else 0

theorem hasMark_congr_on {p q : α → Bool} {t : Tree α}
    (h : ∀ a ∈ inorder t, p a = q a) : hasMark p t = hasMark q t := by
  induction t with
  | empty => rfl
  | node l a r ihl ihr =>
    have hl := ihl (fun b hb => h b (by simp [inorder, hb]))
    have hr := ihr (fun b hb => h b (by simp [inorder, hb]))
    have ha := h a (by simp [inorder])
    simp only [hasMark, hl, hr, ha]

theorem hullSize_congr_on {p q : α → Bool} {t : Tree α}
    (h : ∀ a ∈ inorder t, p a = q a) : hullSize p t = hullSize q t := by
  induction t with
  | empty => rfl
  | node l a r ihl ihr =>
    have hl := ihl (fun b hb => h b (by simp [inorder, hb]))
    have hr := ihr (fun b hb => h b (by simp [inorder, hb]))
    have hm := hasMark_congr_on h
    simp only [hullSize, hl, hr, hm]

@[simp] theorem hasMark_false (t : Tree α) : hasMark (fun _ => false) t = false := by
  induction t <;> simp_all [hasMark]

@[simp] theorem hullSize_false (t : Tree α) : hullSize (fun _ => false) t = 0 := by
  induction t <;> simp_all [hullSize]

theorem hullSize_le_size (p : α → Bool) (t : Tree α) : hullSize p t ≤ size t := by
  induction t with
  | empty => simp [hullSize, size]
  | node l a r ihl ihr =>
    simp only [hullSize, size]
    split <;> omega

/-- A rotation changes the marked-hull size by at most one. -/
theorem hullSize_root_rotation (p : α → Bool) (A B C : Tree α) (a b : α) :
    hullSize p (.node (.node A a B) b C) ≤
      hullSize p (.node A a (.node B b C)) + 1 ∧
    hullSize p (.node A a (.node B b C)) ≤
      hullSize p (.node (.node A a B) b C) + 1 := by
  have htotal : hasMark p (.node (.node A a B) b C) =
      hasMark p (.node A a (.node B b C)) := by
    simp [hasMark, Bool.or_assoc]
  simp only [hullSize, htotal]
  split <;> split <;> split <;> omega

variable [LinearOrder α]

/-- Number of vertices on the ordinary search path, also defined for absence. -/
def pathSize (x : α) : Tree α → Nat
  | .empty => 0
  | .node l a r =>
      1 + if x < a then pathSize x l else if a < x then pathSize x r else 0

def poppedBatch (marked : α → Bool) (x : α) (a : α) : Bool :=
  decide (a = x) || (decide (a < x) && marked a)

def retainedMarks (marked : α → Bool) (x : α) (a : α) : Bool :=
  decide (a = x) || (decide (x < a) && marked a)

private theorem ordered_children {l r : Tree α} {a : α}
    (h : Ordered (.node l a r)) :
    Ordered l ∧ Ordered r ∧ (∀ b ∈ inorder l, b < a) ∧
      (∀ b ∈ inorder r, a < b) := by
  have houter := List.pairwise_append.mp h
  have hinner := List.pairwise_append.mp houter.1
  refine ⟨hinner.1, houter.2.1, ?_, ?_⟩
  · intro b hb
    exact hinner.2.2 b hb a (by simp)
  · intro b hb
    exact houter.2.2 a (by simp) b hb

theorem poppedBatch_below {p : α → Bool} {x a : α} (h : a < x) :
    poppedBatch p x a = p a := by
  simp [poppedBatch, h, ne_of_lt h]

theorem retainedMarks_below {p : α → Bool} {x a : α} (h : a < x) :
    retainedMarks p x a = false := by
  simp [retainedMarks, ne_of_lt h, not_lt_of_gt h]

theorem poppedBatch_above {p : α → Bool} {x a : α} (h : x < a) :
    poppedBatch p x a = false := by
  simp [poppedBatch, ne_of_gt h, not_lt_of_gt h]

theorem retainedMarks_above {p : α → Bool} {x a : α} (h : x < a) :
    retainedMarks p x a = p a := by
  simp [retainedMarks, h, ne_of_gt h]

/-- The popped-key hull is paid by two search paths and the decrease in
the actual rooted marked-hull potential. No marked-state assumption on
the comparator BST is needed. -/
theorem popped_hull_potential (p : α → Bool) (x : α) {t : Tree α}
    (hord : Ordered t) :
    hullSize (poppedBatch p x) t + hullSize (retainedMarks p x) t ≤
      2 * pathSize x t + hullSize p t := by
  induction t with
  | empty => simp [hullSize, pathSize]
  | node l a r ihl ihr =>
    obtain ⟨hl, hr, hleft, hright⟩ := ordered_children hord
    by_cases hxa : x < a
    · have hs : hullSize (poppedBatch p x) r = 0 := by
        calc
          _ = hullSize (fun _ => false) r := hullSize_congr_on
            (fun b hb => poppedBatch_above (lt_trans hxa (hright b hb)))
          _ = 0 := hullSize_false r
      have hn : hullSize (retainedMarks p x) r = hullSize p r :=
        hullSize_congr_on
          (fun b hb => retainedMarks_above (lt_trans hxa (hright b hb)))
      have hi := ihl hl
      simp only [hullSize, pathSize, hxa, ↓reduceIte, hs, hn]
      split <;> split <;> split <;> omega
    · by_cases hax : a < x
      · have hs : hullSize (poppedBatch p x) l = hullSize p l :=
          hullSize_congr_on
            (fun b hb => poppedBatch_below (lt_trans (hleft b hb) hax))
        have hn : hullSize (retainedMarks p x) l = 0 := by
          calc
            _ = hullSize (fun _ => false) l := hullSize_congr_on
              (fun b hb => retainedMarks_below (lt_trans (hleft b hb) hax))
            _ = 0 := hullSize_false l
        have hi := ihr hr
        simp only [hullSize, pathSize, hxa, hax, ↓reduceIte, hs, hn]
        split <;> split <;> split <;> omega
      · have heq : a = x := le_antisymm (le_of_not_gt hxa) (le_of_not_gt hax)
        subst a
        have hsl : hullSize (poppedBatch p x) l = hullSize p l :=
          hullSize_congr_on (fun b hb => poppedBatch_below (hleft b hb))
        have hnr : hullSize (retainedMarks p x) r = hullSize p r :=
          hullSize_congr_on (fun b hb => retainedMarks_above (hright b hb))
        have hsr : hullSize (poppedBatch p x) r = 0 := by
          calc
            _ = hullSize (fun _ => false) r := hullSize_congr_on
              (fun b hb => poppedBatch_above (hright b hb))
            _ = 0 := hullSize_false r
        have hnl : hullSize (retainedMarks p x) l = 0 := by
          calc
            _ = hullSize (fun _ => false) l := hullSize_congr_on
              (fun b hb => retainedMarks_below (hleft b hb))
            _ = 0 := hullSize_false l
        simp only [hullSize, pathSize, lt_self_iff_false, ↓reduceIte, hsl, hnr, hsr, hnl]
        split <;> split <;> split <;> omega

end ChaCha.MTR.Tree

namespace ChaCha.MTR.Pointer

open Tree

variable {α : Type*}

theorem hasMark_plug_congr (p : α → Bool) {s t : Tree α}
    (heq : hasMark p s = hasMark p t) (frames : List (Frame α)) :
    hasMark p (plug s frames) = hasMark p (plug t frames) := by
  induction frames generalizing s t with
  | nil => exact heq
  | cons frame rest ih =>
    cases frame with
    | left a r => exact ih (by simp only [hasMark, heq])
    | right l a => exact ih (by simp only [hasMark, heq])

/-- A local hull-size bound propagates through an unchanged ancestor context,
provided the subtree has the same marked/nonmarked status. -/
theorem hullSize_plug_le (p : α → Bool) {s t : Tree α} {k : Nat}
    (heq : hasMark p s = hasMark p t)
    (hle : hullSize p s ≤ hullSize p t + k) (frames : List (Frame α)) :
    hullSize p (plug s frames) ≤ hullSize p (plug t frames) + k := by
  induction frames generalizing s t with
  | nil => exact hle
  | cons frame rest ih =>
    cases frame with
    | left a r =>
      apply ih
      · simp only [hasMark, heq]
      · simp only [hullSize, hasMark, heq]
        split_ifs <;> omega
    | right l a =>
      apply ih
      · simp only [hasMark, heq]
      · simp only [hullSize, hasMark, heq]
        split_ifs <;> omega

/-- Every actual pointer operation changes the marked-hull potential by at
most one. Pointer moves leave it unchanged; rotations may change it by one. -/
theorem Step.hullSize_change (p : α → Bool) {c d : Cursor α} (h : Step c d) :
    hullSize p c.tree ≤ hullSize p d.tree + 1 ∧
      hullSize p d.tree ≤ hullSize p c.tree + 1 := by
  cases h with
  | left => simp only [Cursor.tree, plug]; omega
  | right => simp only [Cursor.tree, plug]; omega
  | upLeft => simp only [Cursor.tree, plug]; omega
  | upRight => simp only [Cursor.tree, plug]; omega
  | rotateRight A B C a b frames =>
    have heq : hasMark p (.node (.node A a B) b C) =
        hasMark p (.node A a (.node B b C)) := by
      simp [hasMark, Bool.or_assoc]
    have hb := hullSize_root_rotation p A B C a b
    exact ⟨hullSize_plug_le p heq hb.1 frames,
      hullSize_plug_le p heq.symm hb.2 frames⟩
  | rotateLeft A B C a b frames =>
    have heq : hasMark p (.node (.node A a B) b C) =
        hasMark p (.node A a (.node B b C)) := by
      simp [hasMark, Bool.or_assoc]
    have hb := hullSize_root_rotation p A B C a b
    exact ⟨hullSize_plug_le p heq.symm hb.2 frames,
      hullSize_plug_le p heq hb.1 frames⟩

end ChaCha.MTR.Pointer
