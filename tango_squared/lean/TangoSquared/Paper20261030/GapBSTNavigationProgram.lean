import TangoSquared.Paper20261030.GapBSTSlotProgram

/-! Local navigation in the gap encoding. The controller reads the current
node's null-child flags and keeps only the logical slot flag. A source
edge move uses at most one physical edge move, plus the charged read. -/

namespace TangoSquared.Paper20261030.GapBST.Storage

open ColoredStorage DynamicOptimality.LocalProgram

variable {α ρ : Type*}

inductive Navigation where
  | left | right | up

inductive NavigationState where
  | start (slot : Flag)
  | move (direction : Move)
  | done (slot : Flag)

def chooseNavigation (action : Navigation) (slot : Flag) (view : View α (Slots ρ)) : NavigationState :=
  match action,slot with
  | .left,.internal => if view.leftEmpty then .done .leftLeaf else .move .left
  | .right,.internal => if view.rightEmpty then .done .rightLeaf else .move .right
  | .up,.internal => .move .up
  | .up,_ => .done .internal
  | _,_ => .done slot

def navigationProgram (action : Navigation) : Program NavigationState α (Slots ρ)
  | .start slot => .read (chooseNavigation action slot)
  | .move direction => .nav direction (.done .internal)
  | .done _ => .halt

theorem navigation_done {action : Navigation} {slot output : Flag}
    {current : Auxiliary.Metadata.Cursor α (fun _ => Slots ρ)} {view : View α (Slots ρ)}
    (observed : observe current = some view) (choice : chooseNavigation action slot view = .done output) :
    Run (navigationProgram action) (.start slot) current (.done output) current [view.entry] 1 := by
  apply Run.next (entry := some view.entry) (cost := 0)
  · exact Step.read rfl observed
  · simpa only [choice] using (Run.halt (program := navigationProgram action)
      (state := NavigationState.done output) (cursor := current) rfl)

theorem navigation_move {action : Navigation} {slot : Flag} {direction : Move}
    {before after : Auxiliary.Metadata.Cursor α (fun _ => Slots ρ)} {view : View α (Slots ρ)}
    (observed : observe before = some view) (choice : chooseNavigation action slot view = .move direction)
    (moved : navigate direction before = some after) :
    Run (navigationProgram action) (.start slot) before (.done .internal) after [view.entry] 2 := by
  apply Run.next (entry := some view.entry) (cost := 1)
  · exact Step.read rfl observed
  · rw [choice]
    apply Run.next (entry := none) (cost := 0)
    · exact Step.nav rfl moved
    exact Run.halt rfl

theorem left_program (left right : Source α ρ) (value : ρ) (rest : List (SourcePointer.Frame α ρ)) :
    ∃ reads cost, Run (navigationProgram .left) (.start .internal) (cursor ⟨.fork value left right,rest⟩)
      (.done (flag ⟨left,.left value right::rest⟩)) (cursor ⟨left,.left value right::rest⟩) reads cost ∧ cost ≤ 2 := by
  cases left with
  | leaf key old =>
    let view : View α (Slots ρ) := ⟨record key ⟨some value,some old,leafRecord right⟩,true,empty (gaps right)⟩
    refine ⟨[view.entry],1,?_,by decide⟩
    apply navigation_done (view := view) <;> rfl
  | fork old a b =>
    let view : View α (Slots ρ) := ⟨record (lastKey b) ⟨some value,none,leafRecord right⟩,false,empty (gaps right)⟩
    refine ⟨[view.entry],2,?_,le_rfl⟩
    apply navigation_move (view := view) (direction := .left) <;> rfl

theorem right_program (left right : Source α ρ) (value : ρ) (rest : List (SourcePointer.Frame α ρ)) :
    ∃ reads cost, Run (navigationProgram .right) (.start .internal) (cursor ⟨.fork value left right,rest⟩)
      (.done (flag ⟨right,.right left value::rest⟩)) (cursor ⟨right,.right left value::rest⟩) reads cost ∧ cost ≤ 2 := by
  cases right with
  | leaf key old =>
    let view : View α (Slots ρ) := ⟨record (lastKey left) ⟨some value,leafRecord left,some old⟩,empty (gaps left),true⟩
    refine ⟨[view.entry],1,?_,by decide⟩
    apply navigation_done (view := view) <;> rfl
  | fork old a b =>
    let view : View α (Slots ρ) := ⟨record (lastKey left) ⟨some value,leafRecord left,none⟩,empty (gaps left),false⟩
    refine ⟨[view.entry],2,?_,le_rfl⟩
    apply navigation_move (view := view) (direction := .right) <;> rfl

theorem up_left_program (left right : Source α ρ) (value : ρ) (rest : List (SourcePointer.Frame α ρ)) :
    ∃ reads cost, Run (navigationProgram .up) (.start (flag ⟨left,.left value right::rest⟩))
      (cursor ⟨left,.left value right::rest⟩) (.done .internal) (cursor ⟨.fork value left right,rest⟩) reads cost ∧ cost ≤ 2 := by
  cases left with
  | leaf key old =>
    let view : View α (Slots ρ) := ⟨record key ⟨some value,some old,leafRecord right⟩,true,empty (gaps right)⟩
    refine ⟨[view.entry],1,?_,by decide⟩
    apply navigation_done (view := view) <;> rfl
  | fork old a b =>
    let view : View α (Slots ρ) := ⟨record (lastKey a) ⟨some old,leafRecord a,leafRecord b⟩,empty (gaps a),empty (gaps b)⟩
    refine ⟨[view.entry],2,?_,le_rfl⟩
    apply navigation_move (view := view) (direction := .up) <;> rfl

theorem up_right_program (left right : Source α ρ) (value : ρ) (rest : List (SourcePointer.Frame α ρ)) :
    ∃ reads cost, Run (navigationProgram .up) (.start (flag ⟨right,.right left value::rest⟩))
      (cursor ⟨right,.right left value::rest⟩) (.done .internal) (cursor ⟨.fork value left right,rest⟩) reads cost ∧ cost ≤ 2 := by
  cases right with
  | leaf key old =>
    let view : View α (Slots ρ) := ⟨record (lastKey left) ⟨some value,leafRecord left,some old⟩,empty (gaps left),true⟩
    refine ⟨[view.entry],1,?_,by decide⟩
    apply navigation_done (view := view) <;> rfl
  | fork old a b =>
    let view : View α (Slots ρ) := ⟨record (lastKey a) ⟨some old,leafRecord a,leafRecord b⟩,empty (gaps a),empty (gaps b)⟩
    refine ⟨[view.entry],2,?_,le_rfl⟩
    apply navigation_move (view := view) (direction := .up) <;> rfl

end TangoSquared.Paper20261030.GapBST.Storage
