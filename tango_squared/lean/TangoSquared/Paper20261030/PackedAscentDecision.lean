import TangoSquared.Paper20261030.PackedParentLocation

/-! Exact upward moves for active and parked projections. The physical
finger moves to its parent precisely when the logical parent's two child
masks both contain its color. All other physical fingers stay in place.
The decision therefore uses only the locally observed parent record.
-/

namespace TangoSquared.Paper20261030.ColoredStorage

open SourcePointer SourceLocalProgram

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

theorem up_left_active (color : α → C) (q : C) (l r : Source α ρ) (record : ρ) (outside)
    (active : q ∈ l.support color ∧ q ∈ r.support color) {physical : Cursor α (List ρ)}
    (represented : Represents color q ⟨l,.left record r::outside⟩ physical) :
    ∃ parent, navigate .up physical = some parent ∧
      Represents color q ⟨.fork record l r,outside⟩ parent := by
  obtain ⟨parent,_,_,_,parentRep⟩ := navigation color q represented (SourcePointer.Move.upLeft l r record outside)
  obtain ⟨child,moved,childRep⟩ := left_active color q l r record outside active parentRep
  have equal := Represents.unique color q ⟨l,.left record r::outside⟩ childRep represented
  subst child
  exact ⟨parent,up_of_left moved,parentRep⟩

theorem up_right_active (color : α → C) (q : C) (l r : Source α ρ) (record : ρ) (outside)
    (active : q ∈ l.support color ∧ q ∈ r.support color) {physical : Cursor α (List ρ)}
    (represented : Represents color q ⟨r,.right l record::outside⟩ physical) :
    ∃ parent, navigate .up physical = some parent ∧
      Represents color q ⟨.fork record l r,outside⟩ parent := by
  obtain ⟨parent,_,_,_,parentRep⟩ := navigation color q represented (SourcePointer.Move.upRight l r record outside)
  obtain ⟨child,moved,childRep⟩ := right_active color q l r record outside active parentRep
  have equal := Represents.unique color q ⟨r,.right l record::outside⟩ childRep represented
  subst child
  exact ⟨parent,up_of_right moved,parentRep⟩

theorem up_left_idle (color : α → C) (q : C) (l r : Source α ρ) (record : ρ) (outside)
    (idle : q ∉ l.support color ∨ q ∉ r.support color) {physical : Cursor α (List ρ)}
    (represented : Represents color q ⟨l,.left record r::outside⟩ physical) :
    Represents color q ⟨.fork record l r,outside⟩ physical := by
  obtain ⟨parent,_,_,_,parentRep⟩ := navigation color q represented (SourcePointer.Move.upLeft l r record outside)
  have childRep := left_idle color q l r record outside idle parentRep
  have equal := Represents.unique color q ⟨l,.left record r::outside⟩ childRep represented
  subst parent
  exact parentRep

theorem up_right_idle (color : α → C) (q : C) (l r : Source α ρ) (record : ρ) (outside)
    (idle : q ∉ l.support color ∨ q ∉ r.support color) {physical : Cursor α (List ρ)}
    (represented : Represents color q ⟨r,.right l record::outside⟩ physical) :
    Represents color q ⟨.fork record l r,outside⟩ physical := by
  obtain ⟨parent,_,_,_,parentRep⟩ := navigation color q represented (SourcePointer.Move.upRight l r record outside)
  have childRep := right_idle color q l r record outside idle parentRep
  have equal := Represents.unique color q ⟨r,.right l record::outside⟩ childRep represented
  subst parent
  exact parentRep

end TangoSquared.Paper20261030.ColoredStorage
