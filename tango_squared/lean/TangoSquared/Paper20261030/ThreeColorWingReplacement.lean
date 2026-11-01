import TangoSquared.Paper20261030.CanonicalPayloadOccurrence

set_option autoImplicit false

/-! A real wing and any replacement for it occupy the same connector
context in the three-color assembly. The connectors have empty packets
and form a nonempty context around every present real wing. -/

namespace TangoSquared.Paper20261030.ForestConnector.ThreeColors

open ColoredStorage SourcePointer

variable {α ρ : Type*}

def EmptyConnector (outside : List (Frame α (List ρ))) : Prop :=
  ∀ current ∈ outside, match current with
    | .left record _ | .right _ record => record = []

theorem real_piece_empty_context (forest : ProjectionForest.State (Option Bool) α ρ)
    (header : Cursor α (List ρ)) (side : Bool) (current : Cursor α (List ρ))
    (present : forest (some side) = some current) :
    ∃ outside, outside ≠ [] ∧ EmptyConnector outside ∧ (configuration forest header).tree = plug current.tree outside := by
  cases side with
  | false => cases left : forest (some true) with
    | none =>
      exact ⟨[.right header.tree []],by simp,by simp [EmptyConnector],by simp only [configuration,present,left,MultiSourceProgram.join,single,plug]⟩
    | some other =>
      exact ⟨[.right (.fork [] other.tree header.tree) []],by simp,by simp [EmptyConnector],
        by simp only [configuration,present,left,MultiSourceProgram.join,single,plug]⟩
  | true => cases right : forest (some false) with
    | none =>
      exact ⟨[.left [] header.tree],by simp,by simp [EmptyConnector],by simp only [configuration,present,right,MultiSourceProgram.join,single,plug]⟩
    | some other =>
      exact ⟨[.left [] header.tree,.left [] other.tree],by simp,by simp [EmptyConnector],
        by simp only [configuration,present,right,MultiSourceProgram.join,single,plug]⟩


theorem replace_piece (forest : ProjectionForest.State (Option Bool) α ρ)
    (header : Cursor α (List ρ)) (side : Bool) (current : Cursor α (List ρ))
    (present : forest (some side) = some current) :
    ∃ outside, outside ≠ [] ∧ EmptyConnector outside ∧
      (configuration forest header).tree = plug current.tree outside ∧
      ∀ fresh : Cursor α (List ρ),
        (configuration (Function.update forest (some side) (some fresh)) header).tree = plug fresh.tree outside := by
  cases side with
  | false => cases left : forest (some true) with
    | none =>
      refine ⟨[.right header.tree []],by simp,by simp [EmptyConnector],?_,?_⟩
      · simp only [configuration,present,left,MultiSourceProgram.join,single,plug]
      · intro fresh
        simp [configuration,Function.update_apply,left,MultiSourceProgram.join,single,plug]
    | some other =>
      refine ⟨[.right (.fork [] other.tree header.tree) []],by simp,by simp [EmptyConnector],?_,?_⟩
      · simp only [configuration,present,left,MultiSourceProgram.join,single,plug]
      · intro fresh
        simp [configuration,Function.update_apply,left,MultiSourceProgram.join,single,plug]
  | true => cases right : forest (some false) with
    | none =>
      refine ⟨[.left [] header.tree],by simp,by simp [EmptyConnector],?_,?_⟩
      · simp only [configuration,present,right,MultiSourceProgram.join,single,plug]
      · intro fresh
        simp [configuration,Function.update_apply,right,MultiSourceProgram.join,single,plug]
    | some other =>
      refine ⟨[.left [] header.tree,.left [] other.tree],by simp,by simp [EmptyConnector],?_,?_⟩
      · simp only [configuration,present,right,MultiSourceProgram.join,single,plug]
      · intro fresh
        simp [configuration,Function.update_apply,right,MultiSourceProgram.join,single,plug]

end TangoSquared.Paper20261030.ForestConnector.ThreeColors
