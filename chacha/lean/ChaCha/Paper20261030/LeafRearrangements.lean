import ChaCha.Paper20261030.ProjectedExecution

/-!
# Local composition of charged leaf-oriented rearrangements

These lemmas retain arbitrary ancestor contexts and charge descent and
return when a rearrangement takes place in a child. Associativity of
concatenation is realized by zero or one root rotation.
-/

namespace ChaCha.Paper20261030.LeafPointer

open RouterProjection

variable {α : Type*}

theorem Step.symm {c d : Cursor α} (h : Step c d) : Step d c := by
  cases h with
  | nav move => exact .nav move.symm
  | rotateRight u v w rest => exact .rotateLeft u v w rest
  | rotateLeft u v w rest => exact .rotateRight u v w rest

theorem Trace.reverse {c d : Option (Cursor α)} {cost : Nat} (h : Trace c d cost) :
    Trace d c cost := by
  induction h with
  | nil => exact .nil _
  | step move rest ih =>
    simpa using ih.append (.step move.symm (.nil _))

def Rearranges (before after : Router α) (budget : Nat) : Prop :=
  ∀ ancestors : List (Frame α), ∃ cost,
    Trace (some ⟨before,ancestors⟩) (some ⟨after,ancestors⟩) cost ∧ cost ≤ budget

theorem rearranges_refl (t : Router α) (budget : Nat) : Rearranges t t budget :=
  fun _ => ⟨0,.nil _,Nat.zero_le _⟩

theorem Rearranges.mono {a b : Router α} {m n : Nat} (h : Rearranges a b m) (hmn : m ≤ n) :
    Rearranges a b n := by
  intro ancestors
  obtain ⟨cost,trace,hcost⟩ := h ancestors
  exact ⟨cost,trace,hcost.trans hmn⟩

theorem Rearranges.symm {a b : Router α} {m : Nat} (h : Rearranges a b m) : Rearranges b a m := by
  intro ancestors
  obtain ⟨cost,trace,hcost⟩ := h ancestors
  exact ⟨cost,trace.reverse,hcost⟩

theorem Rearranges.trans {a b c : Router α} {m n : Nat}
    (h : Rearranges a b m) (g : Rearranges b c n) : Rearranges a c (m + n) := by
  intro ancestors
  obtain ⟨hc,ht,hb⟩ := h ancestors
  obtain ⟨gc,gt,gb⟩ := g ancestors
  exact ⟨hc + gc,ht.append gt,Nat.add_le_add hb gb⟩

theorem join_nonempty_left {a b : Router α} (ha : a ≠ .empty) : a.join b ≠ .empty := by
  cases a <;> cases b <;> simp_all [Router.join]

theorem join_nonempty_right {a b : Router α} (hb : b ≠ .empty) : a.join b ≠ .empty := by
  cases a <;> cases b <;> simp_all [Router.join]

theorem Rearranges.join_left {a b r : Router α} {m : Nat}
    (h : Rearranges a b m) (ha : a ≠ .empty) (hb : b ≠ .empty) :
    Rearranges (a.join r) (b.join r) (m + 2) := by
  classical
  by_cases hr : r = .empty
  · subst r
    simpa using h.mono (Nat.le_add_right m 2)
  · rw [join_eq_fork ha hr,join_eq_fork hb hr]
    intro ancestors
    obtain ⟨cost,trace,hcost⟩ := h (.left r :: ancestors)
    have up := Trace.step (.nav (.upLeft b r ancestors hb)) (.nil _)
    have full := Trace.step (.nav (.left a r ancestors ha)) (trace.append up)
    exact ⟨cost + 2,by simpa using full,by omega⟩

theorem Rearranges.join_right {l a b : Router α} {m : Nat}
    (h : Rearranges a b m) (ha : a ≠ .empty) (hb : b ≠ .empty) :
    Rearranges (l.join a) (l.join b) (m + 2) := by
  classical
  by_cases hl : l = .empty
  · subst l
    simpa only [Router.join] using h.mono (Nat.le_add_right m 2)
  · rw [join_eq_fork hl ha,join_eq_fork hl hb]
    intro ancestors
    obtain ⟨cost,trace,hcost⟩ := h (.right l :: ancestors)
    have up := Trace.step (.nav (.upRight l b ancestors hb)) (.nil _)
    have full := Trace.step (.nav (.right l a ancestors ha)) (trace.append up)
    exact ⟨cost + 2,by simpa using full,by omega⟩

theorem join_associate (u v w : Router α) : Rearranges ((u.join v).join w) (u.join (v.join w)) 1 := by
  intro ancestors
  cases u <;> cases v <;> cases w <;> simp only [Router.join]
  all_goals first
    | exact ⟨0,.nil _,by decide⟩
    | exact ⟨1,.step (.rotateRight _ _ _ _) (.nil _),le_rfl⟩

def Cursor.extend (c : Cursor α) (outside : List (Frame α)) : Cursor α :=
  ⟨c.focus,c.ancestors ++ outside⟩

theorem Move.extend {c d : Cursor α} (h : Move c d) (outside : List (Frame α)) :
    Move (c.extend outside) (d.extend outside) := by
  cases h with
  | left l r rest hl => exact .left l r (rest ++ outside) hl
  | right l r rest hr => exact .right l r (rest ++ outside) hr
  | upLeft l r rest hl => exact .upLeft l r (rest ++ outside) hl
  | upRight l r rest hr => exact .upRight l r (rest ++ outside) hr

theorem Step.extend {c d : Cursor α} (h : Step c d) (outside : List (Frame α)) :
    Step (c.extend outside) (d.extend outside) := by
  cases h with
  | nav move => exact .nav (move.extend outside)
  | rotateRight u v w rest => exact .rotateRight u v w (rest ++ outside)
  | rotateLeft u v w rest => exact .rotateLeft u v w (rest ++ outside)

theorem Trace.extend {c d : Option (Cursor α)} {cost : Nat} (h : Trace c d cost)
    (outside : List (Frame α)) :
    Trace (c.map (fun z => z.extend outside)) (d.map (fun z => z.extend outside)) cost := by
  induction h with
  | nil => exact .nil _
  | step move rest ih => exact .step (move.extend outside) ih

end ChaCha.Paper20261030.LeafPointer
