import TangoSquared.RouterProjection

/-!
# Structural restriction lemmas for the 30 October manuscript

We reuse `Router`, the existing ordered leaf-labeled tree with an empty
constructor. `Full` excludes empty children at branching vertices.
`Subtree q t` means that `q` is a whole rooted subtree of `t`.
`Rotation` is one ordinary ordered-tree rotation at any position; `Step`
also permits leaving the tree unchanged. No cost or BST implementation
claim is hidden in these purely structural statements.
-/

namespace TangoSquared.Paper20261030

open RouterProjection

namespace Router

variable {α β : Type*}

def Full : Router α → Prop
  | .empty => True
  | .leaf _ => True
  | .fork l r => l ≠ .empty ∧ r ≠ .empty ∧ Full l ∧ Full r

def internalCount : Router α → Nat
  | .empty | .leaf _ => 0
  | .fork l r => internalCount l + internalCount r + 1

theorem full_join {l r : Router α} (hl : Full l) (hr : Full r) :
    Full (l.join r) := by
  cases l <;> cases r <;> simp_all [RouterProjection.Router.join, Full]

theorem full_prune (p : α → Bool) (t : Router α) : Full (t.prune p) := by
  induction t with
  | empty => trivial
  | leaf a => cases h : p a <;> simp [RouterProjection.Router.prune, h, Full]
  | fork l r ihl ihr => exact full_join ihl ihr

theorem full_leaf_count (t : Router α) (ht : Full t) (hne : t ≠ .empty) :
    t.leaves.length = internalCount t + 1 := by
  induction t with
  | empty => exact (hne rfl).elim
  | leaf a => rfl
  | fork l r ihl ihr =>
      obtain ⟨hl, hr, hfl, hfr⟩ := ht
      simp only [RouterProjection.Router.leaves, List.length_append, internalCount]
      rw [ihl hfl hl, ihr hfr hr]
      omega

inductive Subtree : Router α → Router α → Prop
  | refl (t) : Subtree t t
  | left {q l r} : Subtree q l → Subtree q (.fork l r)
  | right {q l r} : Subtree q r → Subtree q (.fork l r)

theorem subtree_join_left {q l r : Router α}
    (h : Subtree q l) (hl : l ≠ .empty) : Subtree q (l.join r) := by
  cases l <;> cases r <;>
    simp_all only [RouterProjection.Router.join] <;>
    first | contradiction | exact h | exact Subtree.left h

theorem subtree_join_right {q l r : Router α}
    (h : Subtree q r) (hr : r ≠ .empty) : Subtree q (l.join r) := by
  cases l <;> cases r <;>
    simp_all only [RouterProjection.Router.join] <;>
    first | contradiction | exact h | exact Subtree.right h

theorem subtree_empty {q : Router α} (h : Subtree q .empty) : q = .empty := by
  cases h
  rfl

/-- Lemmas `restrict subtree remains subtree` and `subtree preserv`. -/
theorem prune_subtree (p : α → Bool) {q t : Router α} (h : Subtree q t)
    (hq : q.prune p ≠ .empty) : Subtree (q.prune p) (t.prune p) := by
  induction h with
  | refl => exact Subtree.refl _
  | @left l r h ih =>
      apply subtree_join_left ih
      intro he
      exact hq (subtree_empty (he ▸ ih))
  | @right l r h ih =>
      apply subtree_join_right ih
      intro he
      exact hq (subtree_empty (he ▸ ih))

def mirror : Router α → Router α
  | .empty => .empty
  | .leaf a => .leaf a
  | .fork l r => .fork (mirror r) (mirror l)

theorem mirror_join (l r : Router α) :
    mirror (l.join r) = (mirror r).join (mirror l) := by
  cases l <;> cases r <;> rfl

/-- Lemma `restrict and mirror`. -/
theorem prune_mirror (p : α → Bool) (t : Router α) :
    (mirror t).prune p = mirror (t.prune p) := by
  induction t with
  | empty => rfl
  | leaf a => cases h : p a <;> simp [mirror, RouterProjection.Router.prune, h]
  | fork l r ihl ihr =>
      simp only [mirror, RouterProjection.Router.prune, ihl, ihr, mirror_join]

/-- Substitute a tree for every formal leaf, suppressing empty operands. -/
def substitute (f : α → Router β) : Router α → Router β
  | .empty => .empty
  | .leaf a => f a
  | .fork l r => (substitute f l).join (substitute f r)

theorem substitute_join (f : α → Router β) (l r : Router α) :
    substitute f (l.join r) = (substitute f l).join (substitute f r) := by
  cases l <;> cases r <;>
    first | rfl | exact (RouterProjection.Router.join_empty _).symm

theorem prune_substitute (p : β → Bool) (f : α → Router β) (t : Router α) :
    (substitute f t).prune p = substitute (fun a => (f a).prune p) t := by
  induction t with
  | empty => rfl
  | leaf a => rfl
  | fork l r ihl ihr =>
      simp only [substitute, RouterProjection.Router.prune_join, ihl, ihr]

theorem substitute_prune (p : α → Bool) (f : α → Router β)
    (h : ∀ a, p a = false → f a = .empty) (t : Router α) :
    substitute f (t.prune p) = substitute f t := by
  induction t with
  | empty => rfl
  | leaf a => cases ha : p a <;> simp [RouterProjection.Router.prune, ha, substitute, h]
  | fork l r ihl ihr =>
      simp only [RouterProjection.Router.prune, substitute_join, ihl, ihr, substitute]

/-- Lemma `restrict thr composition`, including empty projections. -/
theorem restriction_composition [DecidableEq β]
    (p : β → Bool) (f : α → Router β) (t : Router α) :
    (substitute f t).prune p =
      substitute (fun a => (f a).prune p)
        (t.prune (fun a => decide ((f a).prune p ≠ .empty))) := by
  rw [prune_substitute, substitute_prune]
  intro a h
  simpa using h

inductive Rotation : Router α → Router α → Prop
  | root (u v w) : Rotation (.fork (.fork u v) w) (.fork u (.fork v w))
  | rootRev (u v w) : Rotation (.fork u (.fork v w)) (.fork (.fork u v) w)
  | left {l l'} (r) : Rotation l l' → Rotation (.fork l r) (.fork l' r)
  | right (l) {r r'} : Rotation r r' → Rotation (.fork l r) (.fork l r')

def Step (s t : Router α) : Prop := s = t ∨ Rotation s t

theorem rotation_leaves {s t : Router α} (h : Rotation s t) : s.leaves = t.leaves := by
  induction h <;> simp_all [RouterProjection.Router.leaves, List.append_assoc]

theorem rotation_nonempty {s t : Router α} (h : Rotation s t) :
    s ≠ .empty ∧ t ≠ .empty := by
  cases h <;> simp

theorem step_join_left {s t : Router α} (h : Step s t) (r : Router α) :
    Step (s.join r) (t.join r) := by
  rcases h with h | h
  · exact Or.inl (h ▸ rfl)
  · obtain ⟨hs, ht⟩ := rotation_nonempty h
    cases s <;> cases t <;> cases r <;>
      simp_all only [RouterProjection.Router.join] <;>
      first | contradiction | exact Or.inr h | exact Or.inr (Rotation.left _ h)

theorem step_join_right (l : Router α) {s t : Router α} (h : Step s t) :
    Step (l.join s) (l.join t) := by
  rcases h with h | h
  · exact Or.inl (h ▸ rfl)
  · obtain ⟨hs, ht⟩ := rotation_nonempty h
    cases l <;> cases s <;> cases t <;>
      simp_all only [RouterProjection.Router.join] <;>
      first | contradiction | exact Or.inr h | exact Or.inr (Rotation.right _ h)

theorem step_join_assoc (u v w : Router α) :
    Step ((u.join v).join w) (u.join (v.join w)) := by
  cases u <;> cases v <;> cases w <;>
    simp only [RouterProjection.Router.join] <;>
    first | exact Or.inl rfl | exact Or.inr (Rotation.root _ _ _)

theorem step_join_assoc_rev (u v w : Router α) :
    Step (u.join (v.join w)) ((u.join v).join w) := by
  cases u <;> cases v <;> cases w <;>
    simp only [RouterProjection.Router.join] <;>
    first | exact Or.inl rfl | exact Or.inr (Rotation.rootRev _ _ _)

/-- Lemma `restriction-rotation`, for a rotation at any depth. -/
theorem prune_rotation (p : α → Bool) {s t : Router α} (h : Rotation s t) :
    Step (s.prune p) (t.prune p) := by
  induction h with
  | root u v w => exact step_join_assoc _ _ _
  | rootRev u v w => exact step_join_assoc_rev _ _ _
  | left r h ih => exact step_join_left ih _
  | right l h ih => exact step_join_right _ ih

end Router
end TangoSquared.Paper20261030
