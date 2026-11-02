import ChaCha.Paper20261030.LocalComponentCompiler

/-! Whole-tree shapes and root positions of the component translations.
These lemmas relate ghost cursors to the already defined physical trees;
they introduce no runtime tree inspection.
-/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage

variable {α β ρ τ : Type*}

theorem plug_mapRecords (f : ρ → τ) (focus : Source α ρ) (outside : List (Frame α ρ)) :
    plug (focus.mapRecords f) (outside.map (Frame.mapRecords f)) = (plug focus outside).mapRecords f := by
  induction outside generalizing focus with
  | nil => rfl
  | cons first rest ih => cases first with
    | left record sibling => exact ih (.fork record focus sibling)
    | right sibling record => exact ih (.fork record sibling focus)

theorem Cursor.mapRecords_tree (f : ρ → τ) (current : Cursor α ρ) :
    (current.mapRecords f).tree = current.tree.mapRecords f := plug_mapRecords f current.focus current.ancestors

theorem plug_mirror (focus : Source α ρ) (outside : List (Frame α ρ)) :
    plug focus.mirror (outside.map Frame.mirror) = (plug focus outside).mirror := by
  induction outside generalizing focus with
  | nil => rfl
  | cons first rest ih => cases first with
    | left record sibling => exact ih (.fork record focus sibling)
    | right sibling record => exact ih (.fork record sibling focus)

theorem Cursor.mirror_tree (current : Cursor α ρ) : current.mirror.tree = current.tree.mirror :=
  plug_mirror current.focus current.ancestors

theorem plug_payload (payload : α → Source β (List (Option ρ))) (focus : Source α (List ρ))
    (outside : List (Frame α (List ρ))) :
    plug (SourcePayloads.graft payload focus) (outside.map (SourcePayloads.frame payload)) =
      SourcePayloads.graft payload (plug focus outside) := by
  induction outside generalizing focus with
  | nil => rfl
  | cons first rest ih => cases first with
    | left record sibling => exact ih (.fork record focus sibling)
    | right sibling record => exact ih (.fork record sibling focus)

theorem Cursor.payload_tree (payload : α → Source β (List (Option ρ))) (current : Cursor α (List ρ)) :
    (SourcePayloads.cursor payload current).tree = SourcePayloads.graft payload current.tree :=
  plug_payload payload current.focus current.ancestors

end ChaCha.Paper20261030.SourcePointer

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

theorem Represents.root_ancestors (color : α → C) (q : C) (source : Source α ρ)
    (physical : Cursor α (List ρ)) (represented : Represents color q ⟨source,[]⟩ physical) :
    physical.ancestors = [] := by
  have rooted := represents_root color q source represented.1
  exact congrArg Cursor.ancestors (Represents.unique color q ⟨source,[]⟩ represented rooted)

end ChaCha.Paper20261030.ColoredStorage
