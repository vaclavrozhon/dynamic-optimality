import TangoSquared.Paper20261030.SourceNavigation

/-!
# Charged navigation with the complete colored record packing

`Represents` relates a source cursor to its physical color cursor. The
physical whole tree is the actual packed record tree, and its position is
the active or parked position of `LeafPointer.project`. Adjacent source
navigation preserves this relation with zero or one physical moves,
including when the source cursor enters or leaves a color-free subtree.
-/

namespace TangoSquared.Paper20261030.ColoredStorage

open SourcePointer RouterProjection

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

def keepColor (color : α → C) (q : C) : α → Bool := fun key => decide (color key = q)

theorem packed_shape (color : α → C) (q : C) (source : Source α ρ)
    {actual : Source α (List ρ)} (h : packed color q source = some actual) :
    actual.shape = source.shape.prune (keepColor color q) := by
  have hf : Router.Full (pack color q source).shape := by
    rw [pack_shape]
    exact Router.full_prune _ _
  have he := (pack color q source).toSource_roundtrip hf
  change storedOption (packed color q source) = _ at he
  rw [h] at he
  have hs := congrArg Stored.shape he
  change actual.shape = source.shape.prune (fun key => decide (color key = q))
  simpa only [storedOption,Source.toStored_shape,pack_shape] using hs

def Represents (color : α → C) (q : C) (source : Cursor α ρ)
    (physical : Cursor α (List ρ)) : Prop :=
  packed color q source.tree = some physical.tree ∧
  LeafPointer.project (keepColor color q) (cursorShape source) = some (cursorShape physical)

theorem represents_root (color : α → C) (q : C) (source : Source α ρ)
    {actual : Source α (List ρ)} (h : packed color q source = some actual) :
    Represents color q ⟨source,[]⟩ ⟨actual,[]⟩ := by
  have hs := packed_shape color q source h
  have hn : source.shape.prune (keepColor color q) ≠ .empty := by
    rw [← hs]
    exact source_nonempty actual
  refine ⟨h,?_⟩
  simp only [LeafPointer.project,cursorShape,List.map_nil,hn,if_false,
    LeafPointer.projectedFrames,hs]

theorem Represents.unique (color : α → C) (q : C) (source : Cursor α ρ)
    {a b : Cursor α (List ρ)} (ha : Represents color q source a)
    (hb : Represents color q source b) : a = b :=
  Cursor.eq_of_tree_shape a b (Option.some.inj (ha.1.symm.trans hb.1))
    (Option.some.inj (ha.2.symm.trans hb.2))

theorem navigation (color : α → C) (q : C) {source final : Cursor α ρ}
    {physical : Cursor α (List ρ)} (represented : Represents color q source physical)
    (move : SourcePointer.Move source final) :
    ∃ (actual : Cursor α (List ρ)) (cost : Nat),
      SourcePointer.Trace physical [] actual cost ∧ cost ≤ 1 ∧
      Represents color q final actual := by
  have hm := LeafPointer.project_move (keepColor color q) move.shape
  rw [represented.2] at hm
  obtain ⟨actual,cost,hs,ht,trace,hcost⟩ := SourcePointer.lift_atMostOne hm
  refine ⟨actual,cost,trace,hcost,?_,hs⟩
  rw [← move.tree,represented.1,ht]

end TangoSquared.Paper20261030.ColoredStorage
