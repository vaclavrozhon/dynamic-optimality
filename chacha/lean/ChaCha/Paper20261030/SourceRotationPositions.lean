import ChaCha.Paper20261030.SourceCursorPositions

/-! Where stationary fingers point after a rotation. Rotating changes
their ghost addresses but leaves the underlying vertices and records
unchanged. The five cases are the two pivots and the three intact subtrees.
-/

namespace ChaCha.Paper20261030.SourcePositions

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ : Type*}

def subtree : Source α ρ → List Bool → Option (Source α ρ)
  | source,[] => some source
  | .leaf _ _,_::_ => none
  | .fork _ l _,false::rest => subtree l rest
  | .fork _ _ r,true::rest => subtree r rest

theorem descend_focus (current : Cursor α ρ) (position : List Bool) :
    (descend current position).map Cursor.focus = subtree current.focus position := by
  induction position generalizing current with
  | nil => rcases current with ⟨focus,outside⟩; cases focus <;> rfl
  | cons right rest ih =>
    rcases current with ⟨focus,outside⟩
    cases focus with
    | leaf => cases right <;> rfl
    | fork record l r =>
      cases right
      · exact ih ⟨l,.left record r::outside⟩
      · exact ih ⟨r,.right l record::outside⟩

theorem locate_focus (tree : Source α ρ) (position : List Bool) :
    (locate tree position).map Cursor.focus = subtree tree position := descend_focus ⟨tree,[]⟩ position

def recordAt (tree : Source α ρ) (position : List Bool) : Option ρ :=
  (subtree tree position).map Source.rootRecord

theorem locate_record (tree : Source α ρ) (position : List Bool) :
    (locate tree position).map (fun current => current.focus.rootRecord) = recordAt tree position := by
  rw [recordAt,← locate_focus,Option.map_map]
  rfl

def rightAddress : List Bool → List Bool
  | [] => [true]
  | [false] => []
  | false::false::rest => false::rest
  | false::true::rest => true::false::rest
  | true::rest => true::true::rest

def leftAddress : List Bool → List Bool
  | [] => [false]
  | [true] => []
  | true::false::rest => false::true::rest
  | true::true::rest => true::rest
  | false::rest => false::false::rest

theorem left_right_address (position : List Bool) : leftAddress (rightAddress position) = position := by
  cases position with
  | nil => rfl
  | cons first rest => cases first with
    | true => rfl
    | false => cases rest with
      | nil => rfl
      | cons second tail => cases second <;> rfl

theorem right_left_address (position : List Bool) : rightAddress (leftAddress position) = position := by
  cases position with
  | nil => rfl
  | cons first rest => cases first with
    | false => rfl
    | true => cases rest with
      | nil => rfl
      | cons second tail => cases second <;> rfl

theorem rotate_right_record (u v w : Source α ρ) (p top : ρ) (position : List Bool) :
    recordAt (.fork p u (.fork top v w)) (rightAddress position) =
      recordAt (.fork top (.fork p u v) w) position := by
  cases position with
  | nil => rfl
  | cons first rest => cases first with
    | true => rfl
    | false => cases rest with
      | nil => rfl
      | cons second tail => cases second <;> rfl

theorem rotate_left_record (u v w : Source α ρ) (p top : ρ) (position : List Bool) :
    recordAt (.fork top (.fork p u v) w) (leftAddress position) =
      recordAt (.fork p u (.fork top v w)) position := by
  have forward := rotate_right_record u v w p top (leftAddress position)
  rw [right_left_address] at forward
  exact forward.symm

theorem valid_of_record {tree : Source α ρ} {position : List Bool} {record : ρ}
    (observed : recordAt tree position = some record) :
    ∃ current, locate tree position = some current ∧ current.focus.rootRecord = record := by
  rw [← locate_record] at observed
  cases reached : locate tree position with
  | none => simp only [reached,Option.map_none,reduceCtorEq] at observed
  | some current =>
    exact ⟨current,rfl,by simpa only [reached,Option.map_some,Option.some.injEq] using observed⟩

theorem rotate_right_valid (u v w : Source α ρ) (p top : ρ) (position : List Bool)
    (current : Cursor α ρ) (reached : locate (.fork top (.fork p u v) w) position = some current) :
    ∃ target, locate (.fork p u (.fork top v w)) (rightAddress position) = some target ∧
      target.focus.rootRecord = current.focus.rootRecord := by
  apply valid_of_record
  rw [rotate_right_record,← locate_record,reached]
  rfl

theorem rotate_left_valid (u v w : Source α ρ) (p top : ρ) (position : List Bool)
    (current : Cursor α ρ) (reached : locate (.fork p u (.fork top v w)) position = some current) :
    ∃ target, locate (.fork top (.fork p u v) w) (leftAddress position) = some target ∧
      target.focus.rootRecord = current.focus.rootRecord := by
  apply valid_of_record
  rw [rotate_left_record,← locate_record,reached]
  rfl

end ChaCha.Paper20261030.SourcePositions
