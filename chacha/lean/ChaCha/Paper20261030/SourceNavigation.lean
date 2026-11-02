import ChaCha.Paper20261030.PackedContext

/-!
# Lifting adjacent navigation to record-decorated trees

Erasing records does not change the available parent and child edges.
Every adjacent move of a routing cursor therefore lifts to one actual
move of the decorated cursor. No record values are changed by this lift.
-/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage RouterProjection

variable {α ρ : Type*}

inductive Move : Cursor α ρ → Cursor α ρ → Prop
  | left (l r : Source α ρ) (record : ρ) (rest) :
      Move ⟨.fork record l r,rest⟩ ⟨l,.left record r :: rest⟩
  | right (l r : Source α ρ) (record : ρ) (rest) :
      Move ⟨.fork record l r,rest⟩ ⟨r,.right l record :: rest⟩
  | upLeft (l r : Source α ρ) (record : ρ) (rest) :
      Move ⟨l,.left record r :: rest⟩ ⟨.fork record l r,rest⟩
  | upRight (l r : Source α ρ) (record : ρ) (rest) :
      Move ⟨r,.right l record :: rest⟩ ⟨.fork record l r,rest⟩

theorem Move.step {a b : Cursor α ρ} (h : Move a b) : Step a b := by
  cases h
  · exact .left _ _ _ _
  · exact .right _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _

theorem Move.tree {a b : Cursor α ρ} (h : Move a b) : a.tree = b.tree := by
  cases h <;> rfl

theorem Move.symm {a b : Cursor α ρ} (h : Move a b) : Move b a := by
  cases h
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _
  · exact .left _ _ _ _
  · exact .right _ _ _ _

theorem Move.shape {a b : Cursor α ρ} (h : Move a b) :
    LeafPointer.Move (cursorShape a) (cursorShape b) := by
  cases h
  · exact .left _ _ _ (source_nonempty _)
  · exact .right _ _ _ (source_nonempty _)
  · exact .upLeft _ _ _ (source_nonempty _)
  · exact .upRight _ _ _ (source_nonempty _)

theorem lift_move {c : Cursor α ρ} {d : LeafPointer.Cursor α}
    (h : LeafPointer.Move (cursorShape c) d) :
    ∃ actual : Cursor α ρ, Move c actual ∧ cursorShape actual = d := by
  generalize he : cursorShape c = erased at h
  rcases c with ⟨focus,rest⟩
  cases h with
  | left l r ancestors hl =>
    cases focus with
    | leaf => simp [cursorShape,Source.shape] at he
    | fork record a b =>
      simp only [cursorShape,Source.shape,LeafPointer.Cursor.mk.injEq,Router.fork.injEq] at he
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := he
      exact ⟨_,.left _ _ _ _,rfl⟩
  | right l r ancestors hr =>
    cases focus with
    | leaf => simp [cursorShape,Source.shape] at he
    | fork record a b =>
      simp only [cursorShape,Source.shape,LeafPointer.Cursor.mk.injEq,Router.fork.injEq] at he
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := he
      exact ⟨_,.right _ _ _ _,rfl⟩
  | upLeft l r ancestors hl =>
    cases rest with
    | nil => simp [cursorShape] at he
    | cons frame rest =>
      cases frame with
      | right => simp [cursorShape,frameShape] at he
      | left record sibling =>
        simp only [cursorShape,List.map_cons,frameShape,LeafPointer.Cursor.mk.injEq,
          List.cons.injEq,LeafPointer.Frame.left.injEq] at he
        obtain ⟨rfl,rfl,rfl⟩ := he
        exact ⟨_,.upLeft _ _ _ _,rfl⟩
  | upRight l r ancestors hr =>
    cases rest with
    | nil => simp [cursorShape] at he
    | cons frame rest =>
      cases frame with
      | left => simp [cursorShape,frameShape] at he
      | right sibling record =>
        simp only [cursorShape,List.map_cons,frameShape,LeafPointer.Cursor.mk.injEq,
          List.cons.injEq,LeafPointer.Frame.right.injEq] at he
        obtain ⟨rfl,rfl,rfl⟩ := he
        exact ⟨_,.upRight _ _ _ _,rfl⟩

theorem lift_atMostOne {c : Cursor α ρ} {d : Option (LeafPointer.Cursor α)}
    (h : LeafPointer.AtMostOne (some (cursorShape c)) d) :
    ∃ (actual : Cursor α ρ) (cost : Nat),
      d = some (cursorShape actual) ∧ actual.tree = c.tree ∧
      Trace c [] actual cost ∧ cost ≤ 1 := by
  cases h with
  | refl => exact ⟨c,0,rfl,rfl,.nil _,by decide⟩
  | move move =>
    obtain ⟨actual,hm,hs⟩ := lift_move move
    exact ⟨actual,1,congrArg some hs.symm,hm.tree.symm,.step hm.step (.nil _),le_rfl⟩

theorem lift_cursor (t : Source α ρ) (d : LeafPointer.Cursor α)
    (ht : d.tree = t.shape) (hne : d.focus ≠ .empty) :
    ∃ c : Cursor α ρ, c.tree = t ∧ cursorShape c = d := by
  rcases d with ⟨focus,ancestors⟩
  induction ancestors generalizing focus with
  | nil => exact ⟨⟨t,[]⟩,rfl,by cases ht; rfl⟩
  | cons frame rest ih =>
    cases frame with
    | left sibling =>
      obtain ⟨parent,hp,hs⟩ := ih (focus := .fork focus sibling) ht (by simp)
      have hm : LeafPointer.Move (cursorShape parent) ⟨focus,.left sibling :: rest⟩ := by
        rw [hs]
        exact .left _ _ _ hne
      obtain ⟨actual,ha,he⟩ := lift_move hm
      exact ⟨actual,ha.tree.symm.trans hp,he⟩
    | right sibling =>
      obtain ⟨parent,hp,hs⟩ := ih (focus := .fork sibling focus) ht (by simp)
      have hm : LeafPointer.Move (cursorShape parent) ⟨focus,.right sibling :: rest⟩ := by
        rw [hs]
        exact .right _ _ _ hne
      obtain ⟨actual,ha,he⟩ := lift_move hm
      exact ⟨actual,ha.tree.symm.trans hp,he⟩

theorem Cursor.eq_of_tree_shape (c d : Cursor α ρ) (ht : c.tree = d.tree)
    (hs : cursorShape c = cursorShape d) : c = d := by
  rcases c with ⟨focus,rest⟩
  induction rest generalizing focus d with
  | nil =>
    rcases d with ⟨other,ancestors⟩
    cases ancestors with
    | nil => exact congrArg (fun t => Cursor.mk t []) ht
    | cons frame rest => simp [cursorShape] at hs
  | cons frame rest ih =>
    rcases d with ⟨other,ancestors⟩
    cases ancestors with
    | nil => simp [cursorShape] at hs
    | cons otherFrame otherRest =>
      cases frame with
      | left record sibling =>
        cases otherFrame with
        | right => simp [cursorShape,frameShape] at hs
        | left otherRecord otherSibling =>
          simp only [cursorShape,List.map_cons,frameShape,LeafPointer.Cursor.mk.injEq,
            List.cons.injEq,LeafPointer.Frame.left.injEq] at hs
          have hp := ih (focus := .fork record focus sibling)
            (d := ⟨.fork otherRecord other otherSibling,otherRest⟩) ht
            (by simp only [cursorShape,Source.shape,hs.1,hs.2.1,hs.2.2])
          simp only [Cursor.mk.injEq,Source.fork.injEq] at hp
          obtain ⟨⟨rfl,rfl,rfl⟩,rfl⟩ := hp
          rfl
      | right sibling record =>
        cases otherFrame with
        | left => simp [cursorShape,frameShape] at hs
        | right otherSibling otherRecord =>
          simp only [cursorShape,List.map_cons,frameShape,LeafPointer.Cursor.mk.injEq,
            List.cons.injEq,LeafPointer.Frame.right.injEq] at hs
          have hp := ih (focus := .fork record sibling focus)
            (d := ⟨.fork otherRecord otherSibling other,otherRest⟩) ht
            (by simp only [cursorShape,Source.shape,hs.1,hs.2.1,hs.2.2])
          simp only [Cursor.mk.injEq,Source.fork.injEq] at hp
          obtain ⟨⟨rfl,rfl,rfl⟩,rfl⟩ := hp
          rfl

theorem navigation_charged {c d : Cursor α ρ} (ht : c.tree = d.tree)
    (h : LeafPointer.AtMostOne (some (cursorShape c)) (some (cursorShape d))) :
    ∃ cost, Trace c [] d cost ∧ cost ≤ 1 := by
  obtain ⟨actual,cost,hs,ha,trace,hcost⟩ := lift_atMostOne h
  have he : actual = d := Cursor.eq_of_tree_shape _ _ (ha.trans ht) (Option.some.inj hs).symm
  subst actual
  exact ⟨cost,trace,hcost⟩

end ChaCha.Paper20261030.SourcePointer
