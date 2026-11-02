import ChaCha.Paper20261030.SourceFingerExtension
import ChaCha.Paper20261030.MultiSourceRecordMap
import ChaCha.Paper20261030.SourceIdentifierPositions
import ChaCha.Paper20261030.SourceLocatedAddress

set_option autoImplicit false

/-! A nonempty downward route ignores changes to its starting root record.
The same route works below any enclosing context and through a record
erasure. This transports already computed routes to actual cached trees. -/

namespace ChaCha.Paper20261030.SourcePositions

open ColoredStorage SourcePointer

variable {α ρ τ : Type*}

theorem distinct_labels_of_proper_descent {ι : Type*} (identify : ρ → ι)
    (before after : Cursor α ρ) (path : List Bool) (proper : path ≠ [])
    (descended : descend before path = some after) (unique : (before.tree.inventory identify).Nodup) :
    identify before.focus.rootRecord ≠ identify after.focus.rootRecord := by
  intro equal
  have same := cursors_eq_of_label identify before after (descend_tree descended).symm unique equal
  have position := descend_address before after path descended
  rw [← same] at position
  have lengths := congrArg List.length position
  simp only [List.length_append] at lengths
  exact proper (List.length_eq_zero_iff.mp (by omega))

theorem subtree_setRoot_proper (source : Source α ρ) (record : ρ) (path : List Bool) (proper : path ≠ []) :
    subtree (source.setRoot record) path = subtree source path := by
  cases path with
  | nil => exact False.elim (proper rfl)
  | cons right rest => cases source <;> cases right <;> rfl

theorem locate_setRoot_proper (source : Source α ρ) (record : ρ) (path : List Bool) (proper : path ≠ [])
    (current : Cursor α ρ) (located : locate source path = some current) :
    ∃ reached, locate (source.setRoot record) path = some reached ∧ reached.focus = current.focus := by
  have focus := congrArg (Option.map Cursor.focus) located
  rw [locate_focus] at focus
  rw [← subtree_setRoot_proper source record path proper,← locate_focus] at focus
  cases found : locate (source.setRoot record) path with
  | none => simp only [found,Option.map_none,Option.map_some,reduceCtorEq] at focus
  | some reached =>
    simp only [found,Option.map_some,Option.some.injEq] at focus
    exact ⟨reached,rfl,focus⟩

theorem reached_proper (erase : τ → ρ) (source : Source α ρ) (record : ρ)
    (path : List Bool) (proper : path ≠ []) (view : Cursor α ρ) (located : locate source path = some view)
    (current : Cursor α τ) (erases : current.focus.mapRecords erase = source.setRoot record) :
    ∃ reached, descend current path = some reached ∧ reached.focus.mapRecords erase = view.focus := by
  obtain ⟨target,targetLocated,targetFocus⟩ := locate_setRoot_proper source record path proper view located
  have ghost : descend (current.mapRecords erase) path =
      some (target.extend (current.ancestors.map (Frame.mapRecords erase))) := by
    change descend ⟨current.focus.mapRecords erase,current.ancestors.map (Frame.mapRecords erase)⟩ _ = _
    rw [erases]
    exact descend_extend targetLocated _
  rw [descend_mapRecords] at ghost
  cases found : descend current path with
  | none => simp only [found,Option.map_none,reduceCtorEq] at ghost
  | some reached =>
    simp only [found,Option.map_some,Option.some.injEq] at ghost
    exact ⟨reached,rfl,(congrArg Cursor.focus ghost).trans targetFocus⟩

end ChaCha.Paper20261030.SourcePositions
