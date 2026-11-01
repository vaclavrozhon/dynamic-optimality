import TangoSquared.Paper20261030.SourceProgramComposition

/-! Ghost addresses for several fingers in one existing source tree.
An address records the root-to-vertex child directions; it is part of
the mathematical pointer model, not data exposed to the local program.
The tree and an address uniquely determine the full zipper cursor.
-/

namespace TangoSquared.Paper20261030.SourcePositions

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ : Type*}

def direction : Frame α ρ → Bool
  | .left _ _ => false
  | .right _ _ => true

def address (current : Cursor α ρ) : List Bool := current.ancestors.reverse.map direction

def descend (current : Cursor α ρ) : List Bool → Option (Cursor α ρ)
  | [] => some current
  | right::rest => (navigate (if right then .right else .left) current).bind (fun child => descend child rest)

def locate (tree : Source α ρ) (position : List Bool) : Option (Cursor α ρ) := descend ⟨tree,[]⟩ position

theorem descend_append (current : Cursor α ρ) (first rest : List Bool) :
    descend current (first++rest) = (descend current first).bind (fun middle => descend middle rest) := by
  induction first generalizing current with
  | nil => rfl
  | cons right tail ih =>
    cases moved : navigate (if right then .right else .left) current with
    | none => simp only [List.cons_append,descend,moved,Option.bind_none]
    | some middle =>
      simpa only [List.cons_append,descend,moved,Option.bind_some] using ih middle

theorem locate_cursor (current : Cursor α ρ) : locate current.tree (address current) = some current := by
  rcases current with ⟨focus,outside⟩
  induction outside generalizing focus with
  | nil => rfl
  | cons frame rest ih => cases frame with
    | left record sibling =>
      have parent := ih (.fork record focus sibling)
      change descend ⟨plug (.fork record focus sibling) rest,[]⟩
        ((.left record sibling::rest).reverse.map direction) = some ⟨focus,.left record sibling::rest⟩
      rw [List.reverse_cons,List.map_append]
      change descend ⟨plug (.fork record focus sibling) rest,[]⟩ ((rest.reverse.map direction)++[false]) = _
      rw [descend_append]
      change (locate (Cursor.tree ⟨.fork record focus sibling,rest⟩) (address ⟨.fork record focus sibling,rest⟩)).bind _ = _
      rw [parent]
      rfl
    | right sibling record =>
      have parent := ih (.fork record sibling focus)
      change descend ⟨plug (.fork record sibling focus) rest,[]⟩
        ((.right sibling record::rest).reverse.map direction) = some ⟨focus,.right sibling record::rest⟩
      rw [List.reverse_cons,List.map_append]
      change descend ⟨plug (.fork record sibling focus) rest,[]⟩ ((rest.reverse.map direction)++[true]) = _
      rw [descend_append]
      change (locate (Cursor.tree ⟨.fork record sibling focus,rest⟩) (address ⟨.fork record sibling focus,rest⟩)).bind _ = _
      rw [parent]
      rfl

theorem eq_of_tree_address (first last : Cursor α ρ) (sameTree : first.tree = last.tree)
    (sameAddress : address first = address last) : first = last := by
  have firstLocated := locate_cursor first
  rw [sameTree,sameAddress,locate_cursor last] at firstLocated
  exact (Option.some.inj firstLocated).symm

theorem descend_tree {before after : Cursor α ρ} {position : List Bool}
    (reached : descend before position = some after) : after.tree = before.tree := by
  induction position generalizing before with
  | nil => exact congrArg Cursor.tree (Option.some.inj reached).symm
  | cons right rest ih =>
    rcases before with ⟨focus,outside⟩
    cases focus with
    | leaf => cases right <;> simp [descend,navigate] at reached
    | fork record l r =>
      cases right
      · exact ih (before := ⟨l,.left record r::outside⟩) reached
      · exact ih (before := ⟨r,.right l record::outside⟩) reached

theorem locate_tree {tree : Source α ρ} {position : List Bool} {current : Cursor α ρ}
    (reached : locate tree position = some current) : current.tree = tree := descend_tree reached

end TangoSquared.Paper20261030.SourcePositions
