import TangoSquared.MTR

/-!
# Linear simulation by rotations at depth at most two

The proof uses explicit legal rotations, rather than a hypothesis asserting that
arbitrary hull shapes can be transformed cheaply. Its bound is deliberately loose:
a tree is flattened in at most three times its size, and two trees with the same
inorder word are connected in at most six times their size.
-/

namespace TangoSquared.MTR
namespace Tree

variable {α : Type*}

/-- A rotation at a child or grandchild of the physical root. -/
inductive RestrictedStep : Tree α → Tree α → Prop
  | rootRight (A B C : Tree α) (a b : α) :
      RestrictedStep (.node (.node A a B) b C) (.node A a (.node B b C))
  | rootLeft (A B C : Tree α) (a b : α) :
      RestrictedStep (.node A a (.node B b C)) (.node (.node A a B) b C)
  | rightRight (A B C D : Tree α) (a b c : α) :
      RestrictedStep (.node A a (.node (.node B b C) c D))
        (.node A a (.node B b (.node C c D)))
  | rightLeft (A B C D : Tree α) (a b c : α) :
      RestrictedStep (.node A a (.node B b (.node C c D)))
        (.node A a (.node (.node B b C) c D))
  | leftRight (A B C D : Tree α) (a b c : α) :
      RestrictedStep (.node (.node (.node A a B) b C) c D)
        (.node (.node A a (.node B b C)) c D)
  | leftLeft (A B C D : Tree α) (a b c : α) :
      RestrictedStep (.node (.node A a (.node B b C)) c D)
        (.node (.node (.node A a B) b C) c D)

theorem RestrictedStep.symm {t u : Tree α} (h : RestrictedStep t u) :
    RestrictedStep u t := by
  cases h with
  | rootRight A B C a b => exact .rootLeft A B C a b
  | rootLeft A B C a b => exact .rootRight A B C a b
  | rightRight A B C D a b c => exact .rightLeft A B C D a b c
  | rightLeft A B C D a b c => exact .rightRight A B C D a b c
  | leftRight A B C D a b c => exact .leftLeft A B C D a b c
  | leftLeft A B C D a b c => exact .leftRight A B C D a b c

theorem RestrictedStep.inorder_eq {t u : Tree α} (h : RestrictedStep t u) :
    inorder t = inorder u := by
  cases h <;> simp [inorder, List.append_assoc]

theorem RestrictedStep.size_eq {t u : Tree α} (h : RestrictedStep t u) :
    size t = size u := by
  cases h <;> simp [size] <;> omega

/-- An actual sequence of exactly k restricted rotations. -/
inductive RestrictedSteps : Nat → Tree α → Tree α → Prop
  | refl (t : Tree α) : RestrictedSteps 0 t t
  | cons {t u v : Tree α} {k : Nat} (step : RestrictedStep t u)
      (rest : RestrictedSteps k u v) : RestrictedSteps (k + 1) t v

theorem RestrictedSteps.trans {t u v : Tree α} {k l : Nat}
    (h : RestrictedSteps k t u) (h' : RestrictedSteps l u v) :
    RestrictedSteps (k + l) t v := by
  induction h with
  | refl => simpa using h'
  | cons hs hr ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      RestrictedSteps.cons hs (ih h')

theorem RestrictedSteps.symm {t u : Tree α} {k : Nat} (h : RestrictedSteps k t u) :
    RestrictedSteps k u t := by
  induction h with
  | refl => exact .refl _
  | cons hs hr ih =>
    exact ih.trans (.cons hs.symm (.refl _))

theorem RestrictedSteps.inorder_eq {t u : Tree α} {k : Nat}
    (h : RestrictedSteps k t u) : inorder t = inorder u := by
  induction h with
  | refl => rfl
  | cons hs hr ih => exact hs.inorder_eq.trans ih

theorem RestrictedSteps.size_eq {t u : Tree α} {k : Nat}
    (h : RestrictedSteps k t u) : size t = size u := by
  induction h with
  | refl => rfl
  | cons hs hr ih => exact hs.size_eq.trans ih

def leftLength : Tree α → Nat
  | .empty => 0
  | .node l _ _ => leftLength l + 1

def rightLength : Tree α → Nat
  | .empty => 0
  | .node _ _ r => rightLength r + 1

theorem leftLength_le_size (t : Tree α) : leftLength t ≤ size t := by
  induction t with
  | empty => rfl
  | node l x r ihl ihr => simp only [leftLength, size]; omega

theorem rightLength_le_size (t : Tree α) : rightLength t ≤ size t := by
  induction t with
  | empty => rfl
  | node l x r ihl ihr => simp only [rightLength, size]; omega

/-- The root is the leftmost node (or the tree is empty). -/
def LeftEmpty : Tree α → Prop
  | .empty => True
  | .node l _ _ => l = .empty

/-- Repeated root-right rotations expose the leftmost node at linear cost. -/
theorem expose_leftmost (t : Tree α) :
    ∃ u k, RestrictedSteps k t u ∧ LeftEmpty u ∧ k ≤ leftLength t := by
  generalize hn : leftLength t = n
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    cases t with
    | empty => exact ⟨.empty, 0, .refl _, trivial, by omega⟩
    | node l b C =>
      cases l with
      | empty => exact ⟨.node .empty b C, 0, .refl _, rfl, by omega⟩
      | node A a B =>
        have hlt : leftLength (.node A a (.node B b C)) < n := by
          simp only [leftLength] at hn ⊢
          omega
        obtain ⟨u, k, hs, he, hk⟩ := ih _ hlt (.node A a (.node B b C)) rfl
        refine ⟨u, k + 1, .cons (.rootRight A B C a b) hs, he, ?_⟩
        simp only [leftLength] at hn hk
        omega

/-- All nodes lie on the left spine. -/
def FlatLeft : Tree α → Prop
  | .empty => True
  | .node l _ r => FlatLeft l ∧ r = .empty

/-- The already processed portion of the sweep is a left spine. -/
def LeftFlat : Tree α → Prop
  | .empty => True
  | .node l _ _ => FlatLeft l

/-- Number of sweep rotations remaining: each of the two rules lowers it by one. -/
def sweepWork : Tree α → Nat
  | .empty => 0
  | .node _ _ r => 2 * size r - rightLength r

theorem sweepWork_le_twice_size (t : Tree α) : sweepWork t ≤ 2 * size t := by
  cases t with
  | empty => rfl
  | node l a r => simp only [sweepWork, size]; omega

/-- Sweep the unprocessed right subtree, using only root and grandchild rotations. -/
theorem sweep_to_left_spine (t : Tree α) (hf : LeftFlat t) :
    ∃ u k, RestrictedSteps k t u ∧ FlatLeft u ∧ k ≤ sweepWork t := by
  generalize hn : sweepWork t = n
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    cases t with
    | empty => exact ⟨.empty, 0, .refl _, trivial, by omega⟩
    | node A a r =>
      cases r with
      | empty => exact ⟨.node A a .empty, 0, .refl _, ⟨hf, rfl⟩, by omega⟩
      | node B b C =>
        cases B with
        | empty =>
          let t' : Tree α := .node (.node A a .empty) b C
          have hb := rightLength_le_size C
          have hwork : sweepWork t' + 1 = n := by
            simp only [t', sweepWork, size, rightLength] at hn ⊢
            omega
          have hf' : LeftFlat t' := ⟨hf, rfl⟩
          obtain ⟨u, k, hs, he, hk⟩ := ih (sweepWork t') (by omega) t' hf' rfl
          exact ⟨u, k + 1, .cons (.rootLeft A .empty C a b) hs, he, by omega⟩
        | node B₁ b₁ B₂ =>
          let t' : Tree α := .node A a (.node B₁ b₁ (.node B₂ b C))
          have hb := rightLength_le_size C
          have hwork : sweepWork t' + 1 = n := by
            simp only [t', sweepWork, size, rightLength] at hn ⊢
            omega
          have hf' : LeftFlat t' := hf
          obtain ⟨u, k, hs, he, hk⟩ := ih (sweepWork t') (by omega) t' hf' rfl
          exact ⟨u, k + 1, .cons (.rightRight A B₁ B₂ C a b₁ b) hs, he, by omega⟩

/-- A deterministic canonical left spine for an inorder word. -/
def leftSpine (xs : List α) : Tree α := xs.foldl (fun t x => .node t x .empty) .empty

theorem leftSpine_append_singleton (xs : List α) (x : α) :
    leftSpine (xs ++ [x]) = .node (leftSpine xs) x .empty := by
  simp [leftSpine, List.foldl_append]

theorem flatLeft_eq_leftSpine (t : Tree α) (h : FlatLeft t) :
    t = leftSpine (inorder t) := by
  induction t with
  | empty => rfl
  | node l x r ihl ihr =>
    obtain ⟨hl, hr⟩ := h
    subst r
    simp only [inorder, List.append_nil, leftSpine_append_singleton]
    exact congrArg (fun (t : Tree α) => Tree.node t x Tree.empty) (ihl hl)

/-- Every tree has a linear sequence of actual shallow rotations to its left spine. -/
theorem flatten_linear (t : Tree α) :
    ∃ k ≤ 3 * size t, RestrictedSteps k t (leftSpine (inorder t)) := by
  obtain ⟨u, k, hku, hu, hk⟩ := expose_leftmost t
  have huf : LeftFlat u := by
    cases u with
    | empty => trivial
    | node l x r =>
      simp only [LeftEmpty] at hu
      simp [LeftFlat, hu, FlatLeft]
  obtain ⟨v, j, hjv, hv, hj⟩ := sweep_to_left_spine u huf
  have htrace := hku.trans hjv
  have hcanon : v = leftSpine (inorder t) := by
    rw [flatLeft_eq_leftSpine v hv, ← htrace.inorder_eq]
  refine ⟨k + j, ?_, ?_⟩
  · have hls := leftLength_le_size t
    have hwork := sweepWork_le_twice_size u
    have hsize := hku.size_eq
    omega
  · simpa only [hcanon] using htrace

/-- The restricted-rotation simulation theorem, without any unproved bridge. -/
theorem restricted_rotation_linear (t u : Tree α) (h : inorder t = inorder u) :
    ∃ k ≤ 3 * size t + 3 * size u, RestrictedSteps k t u := by
  obtain ⟨k, hk, ht⟩ := flatten_linear t
  obtain ⟨j, hj, hu⟩ := flatten_linear u
  refine ⟨k + j, by omega, ?_⟩
  rw [← h] at hu
  exact ht.trans hu.symm


/-- Plug arbitrary hanging subtrees into a skeleton's inorder gaps.

The offset indexes the leftmost gap. An internal key consumes one boundary;
therefore the right child starts at offset + size(left) + 1.
-/
def plug (gaps : Nat → Tree α) (offset : Nat) : Tree α → Tree α
  | .empty => gaps offset
  | .node l x r => .node (plug gaps offset l) x (plug gaps (offset + size l + 1) r)

/-- Every shallow skeleton rotation preserves the same hanging subtrees. -/
theorem RestrictedStep.plug {t u : Tree α} (h : RestrictedStep t u)
    (gaps : Nat → Tree α) (offset : Nat) :
    RestrictedStep (Tree.plug gaps offset t) (Tree.plug gaps offset u) := by
  cases h with
  | rootRight A B C a b =>
    simpa only [Tree.plug, size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      RestrictedStep.rootRight
        (Tree.plug gaps offset A)
        (Tree.plug gaps (offset + size A + 1) B)
        (Tree.plug gaps (offset + size A + 1 + size B + 1) C) a b
  | rootLeft A B C a b =>
    simpa only [Tree.plug, size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      RestrictedStep.rootLeft
        (Tree.plug gaps offset A)
        (Tree.plug gaps (offset + size A + 1) B)
        (Tree.plug gaps (offset + size A + 1 + size B + 1) C) a b
  | rightRight A B C D a b c =>
    simpa only [Tree.plug, size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      RestrictedStep.rightRight
        (Tree.plug gaps offset A)
        (Tree.plug gaps (offset + size A + 1) B)
        (Tree.plug gaps (offset + size A + 1 + size B + 1) C)
        (Tree.plug gaps (offset + size A + 1 + size B + 1 + size C + 1) D) a b c
  | rightLeft A B C D a b c =>
    simpa only [Tree.plug, size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      RestrictedStep.rightLeft
        (Tree.plug gaps offset A)
        (Tree.plug gaps (offset + size A + 1) B)
        (Tree.plug gaps (offset + size A + 1 + size B + 1) C)
        (Tree.plug gaps (offset + size A + 1 + size B + 1 + size C + 1) D) a b c
  | leftRight A B C D a b c =>
    simpa only [Tree.plug, size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      RestrictedStep.leftRight
        (Tree.plug gaps offset A)
        (Tree.plug gaps (offset + size A + 1) B)
        (Tree.plug gaps (offset + size A + 1 + size B + 1) C)
        (Tree.plug gaps (offset + size A + 1 + size B + 1 + size C + 1) D) a b c
  | leftLeft A B C D a b c =>
    simpa only [Tree.plug, size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      RestrictedStep.leftLeft
        (Tree.plug gaps offset A)
        (Tree.plug gaps (offset + size A + 1) B)
        (Tree.plug gaps (offset + size A + 1 + size B + 1) C)
        (Tree.plug gaps (offset + size A + 1 + size B + 1 + size C + 1) D) a b c

/-- The entire rotation sequence lifts while every untouched gap subtree stays intact. -/
theorem RestrictedSteps.plug {t u : Tree α} {k : Nat} (h : RestrictedSteps k t u)
    (gaps : Nat → Tree α) (offset : Nat) :
    RestrictedSteps k (Tree.plug gaps offset t) (Tree.plug gaps offset u) := by
  induction h with
  | refl => exact .refl _
  | cons hs hr ih => exact .cons (hs.plug gaps offset) ih

/-- Linear restricted rotation simulation of a rooted hull with arbitrary gaps.

The cost depends only on skeleton size, never on hanging subtree sizes.
-/
theorem rooted_hull_rotation_linear (t u : Tree α) (h : inorder t = inorder u)
    (gaps : Nat → Tree α) (offset : Nat) :
    ∃ k ≤ 3 * size t + 3 * size u,
      RestrictedSteps k (plug gaps offset t) (plug gaps offset u) := by
  obtain ⟨k, hk, hs⟩ := restricted_rotation_linear t u h
  exact ⟨k, hk, hs.plug gaps offset⟩

end Tree
end TangoSquared.MTR
