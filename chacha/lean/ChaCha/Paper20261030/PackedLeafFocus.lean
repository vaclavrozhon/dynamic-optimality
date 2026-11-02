import ChaCha.Paper20261030.CursorRepresentationShapes

/-! A source leaf's owning projection is focused at that exact leaf.
This is a position invariant, stronger than equality of whole key words.
It is the bridge from logical exit exposure to the physical payload root.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer RouterProjection

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

theorem Represents.leaf_focus (color : α → C) (key : α) (record : ρ)
    (outside : List (Frame α ρ)) (physical : Cursor α (List ρ))
    (represented : Represents color (color key) ⟨.leaf key record,outside⟩ physical) :
    ∃ records, physical.focus = .leaf key records := by
  have projected := represented.2
  simp only [LeafPointer.project,cursorShape,Source.shape,Router.prune,keepColor,decide_true,
    if_true,reduceCtorEq,if_false,Option.some.injEq] at projected
  have focus := congrArg LeafPointer.Cursor.focus projected
  change Router.leaf key = physical.focus.shape at focus
  cases tree : physical.focus with
  | leaf other records =>
    have equal : key = other := by simpa only [tree,Source.shape,Router.leaf.injEq] using focus
    exact ⟨records,by rw [equal]⟩
  | fork record left right => simp only [tree,Source.shape,reduceCtorEq] at focus

theorem Represents.focus_leaf (color : α → C) (key : α) (record : ρ)
    (source : Cursor α ρ) (physical : Cursor α (List ρ))
    (leaf : source.focus = .leaf key record) (represented : Represents color (color key) source physical) :
    ∃ records, physical.focus = .leaf key records := by
  rcases source with ⟨focus,outside⟩
  dsimp only at leaf
  subst focus
  exact Represents.leaf_focus color key record outside physical represented

end ChaCha.Paper20261030.ColoredStorage
