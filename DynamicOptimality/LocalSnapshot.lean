import DynamicOptimality.LocalProgramComposition

/-! A local observation tour, controlled by an explicit finite stack.
The depth parameter limits the observation: a four-level snapshot contains
at most fifteen records. All child tests come from a charged read at the
parent, and every descent is paired with a return along the same edge. -/

namespace DynamicOptimality.LocalSnapshot

open TangoSquared.MTR TangoSquared.Paper20261030.Auxiliary LocalProgram

variable {α ρ : Type*}

abbrev Record (α ρ : Type*) := NodeRecord α (fun _ => ρ)
abbrev Snapshot (α ρ : Type*) := TangoSquared.Paper20261030.Auxiliary.Snapshot α (fun _ => ρ)

def node (entry : Record α ρ) (left right : Snapshot α ρ) : Snapshot α ρ :=
  .node entry.1 entry.2.1 entry.2.2 left right

def capture : Nat → RawTree (Record α ρ) → Snapshot α ρ
  | 0,_ => .unseen
  | _+1,.empty => .empty
  | depth+1,.node left entry right => node entry (capture depth left) (capture depth right)

inductive Frame (α ρ : Type*) where
  | left (depth : Nat) (entry : Record α ρ) (rightEmpty : Bool)
  | right (entry : Record α ρ) (left : Snapshot α ρ)

inductive State (α ρ : Type*) where
  | read (depth : Nat) (stack : List (Frame α ρ))
  | left (depth : Nat) (entry : Record α ρ) (rightEmpty : Bool) (stack : List (Frame α ρ))
  | right (depth : Nat) (entry : Record α ρ) (left : Snapshot α ρ) (stack : List (Frame α ρ))
  | up (result : Snapshot α ρ) (frame : Frame α ρ) (stack : List (Frame α ρ))
  | done (result : Snapshot α ρ)

def finish (result : Snapshot α ρ) : List (Frame α ρ) → State α ρ
  | [] => .done result
  | frame::stack => .up result frame stack

def afterLeft (depth : Nat) (entry : Record α ρ) (rightEmpty : Bool)
    (left : Snapshot α ρ) (stack : List (Frame α ρ)) : State α ρ :=
  if rightEmpty then finish (node entry left .empty) stack
  else .right depth entry left stack

def program : Program (State α ρ) α ρ
  | .read 0 stack => .read (fun view => finish (node view.entry .unseen .unseen) stack)
  | .read (depth+1) stack => .read (fun view =>
      if view.leftEmpty then afterLeft depth view.entry view.rightEmpty .empty stack
      else .left depth view.entry view.rightEmpty stack)
  | .left depth entry rightEmpty stack =>
      .nav .left (.read depth (.left depth entry rightEmpty::stack))
  | .right depth entry left stack => .nav .right (.read depth (.right entry left::stack))
  | .up result (.left depth entry rightEmpty) stack =>
      .nav .up (afterLeft depth entry rightEmpty result stack)
  | .up result (.right entry left) stack => .nav .up (finish (node entry left result) stack)
  | .done _ => .halt

theorem capture_records_node (depth : Nat) (left right : RawTree (Record α ρ)) (entry : Record α ρ) :
    (capture (depth+1) (.node left entry right)).records =
      entry::((capture depth left).records++(capture depth right).records) := by
  rcases entry with ⟨size,key,value⟩
  rfl

theorem tour (depth : Nat) (tree : RawTree (Record α ρ)) (nonempty : tree ≠ .empty)
    (stack : List (Frame α ρ)) (outside : List (Pointer.Frame (Record α ρ))) :
    ∃ cost, Steps program (.read depth stack) ⟨tree,outside⟩
      (finish (capture (depth+1) tree) stack) ⟨tree,outside⟩
      (capture (depth+1) tree).records cost ∧ cost+2 = 3*(capture (depth+1) tree).records.length := by
  induction depth generalizing tree stack outside with
  | zero =>
    cases tree with
    | empty => contradiction
    | node left entry right =>
      refine ⟨1,?_,?_⟩
      · have read : Step program (.read 0 stack) ⟨.node left entry right,outside⟩
            (finish (node entry .unseen .unseen) stack) ⟨.node left entry right,outside⟩ (some entry) := by
          apply Step.read (next := fun view => finish (node view.entry .unseen .unseen) stack)
            (view := ⟨entry,empty left,empty right⟩) <;> rfl
        exact read.prefix
      · rcases entry with ⟨size,key,value⟩; rfl
  | succ depth ih =>
    cases tree with
    | empty => contradiction
    | node left entry right =>
      have rightTour (leftSnapshot : Snapshot α ρ) :
          ∃ cost, Steps program (afterLeft depth entry (empty right) leftSnapshot stack)
            ⟨.node left entry right,outside⟩
            (finish (node entry leftSnapshot (capture (depth+1) right)) stack)
            ⟨.node left entry right,outside⟩ (capture (depth+1) right).records cost ∧
            cost = 3*(capture (depth+1) right).records.length := by
        cases right with
        | empty => exact ⟨0,.nil _ _,rfl⟩
        | node a x b =>
          obtain ⟨cost,child,bound⟩ := ih (.node a x b) (by simp) (.right entry leftSnapshot::stack)
            (.right left entry::outside)
          have down : Step program (.right depth entry leftSnapshot stack)
              ⟨.node left entry (.node a x b),outside⟩
              (.read depth (.right entry leftSnapshot::stack))
              ⟨.node a x b,.right left entry::outside⟩ none := .nav rfl rfl
          have up : Step program (finish (capture (depth+1) (.node a x b)) (.right entry leftSnapshot::stack))
              ⟨.node a x b,.right left entry::outside⟩
              (finish (node entry leftSnapshot (capture (depth+1) (.node a x b))) stack)
              ⟨.node left entry (.node a x b),outside⟩ none := .nav rfl rfl
          refine ⟨1+cost+1,?_,by omega⟩
          simpa only [Option.toList_none,List.nil_append,List.append_nil,afterLeft,empty,Bool.false_eq_true,ite_false]
            using (down.prefix.append child).append up.prefix
      cases left with
      | empty =>
        obtain ⟨cost,rest,bound⟩ := rightTour .empty
        refine ⟨cost+1,?_,?_⟩
        · have read : Step program (.read (depth+1) stack)
              ⟨.node .empty entry right,outside⟩
              (afterLeft depth entry (empty right) .empty stack)
              ⟨.node .empty entry right,outside⟩ (some entry) := by
            apply Step.read (next := fun view => if view.leftEmpty then
              afterLeft depth view.entry view.rightEmpty .empty stack
              else .left depth view.entry view.rightEmpty stack)
              (view := ⟨entry,true,empty right⟩) <;> rfl
          simpa only [capture_records_node,capture,node,TangoSquared.Paper20261030.Auxiliary.Snapshot.records,
            List.nil_append,Option.toList_some,List.singleton_append] using Steps.next read rest
        · rw [capture_records_node]
          simp only [capture,TangoSquared.Paper20261030.Auxiliary.Snapshot.records,List.nil_append,List.length_cons]
          omega
      | node a x b =>
        obtain ⟨leftCost,child,leftBound⟩ := ih (.node a x b) (by simp)
          (.left depth entry (empty right)::stack) (.left entry right::outside)
        obtain ⟨rightCost,rest,rightBound⟩ := rightTour (capture (depth+1) (.node a x b))
        have read : Step program (.read (depth+1) stack)
            ⟨.node (.node a x b) entry right,outside⟩ (.left depth entry (empty right) stack)
            ⟨.node (.node a x b) entry right,outside⟩ (some entry) := by
          apply Step.read (next := fun view => if view.leftEmpty then
            afterLeft depth view.entry view.rightEmpty .empty stack
            else .left depth view.entry view.rightEmpty stack)
            (view := ⟨entry,false,empty right⟩) <;> rfl
        have down : Step program (.left depth entry (empty right) stack)
            ⟨.node (.node a x b) entry right,outside⟩
            (.read depth (.left depth entry (empty right)::stack))
            ⟨.node a x b,.left entry right::outside⟩ none := .nav rfl rfl
        have up : Step program (finish (capture (depth+1) (.node a x b)) (.left depth entry (empty right)::stack))
            ⟨.node a x b,.left entry right::outside⟩
            (afterLeft depth entry (empty right) (capture (depth+1) (.node a x b)) stack)
            ⟨.node (.node a x b) entry right,outside⟩ none := .nav rfl rfl
        refine ⟨1+(1+leftCost+1+rightCost),?_,?_⟩
        · simpa only [Option.toList_none,Option.toList_some,List.nil_append,List.append_nil,
            List.singleton_append,capture_records_node,capture,node,
            TangoSquared.Paper20261030.Auxiliary.Snapshot.records,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
            using read.prefix.append (((down.prefix.append child).append up.prefix).append rest)
        · rw [capture_records_node]
          simp only [List.length_cons,List.length_append]
          omega

theorem capture_recordTree (depth : Nat) (tree : Std.DTreeMap.Internal.Impl α (fun _ => ρ)) :
    capture depth (recordTree tree) = TangoSquared.Paper20261030.Auxiliary.capture depth tree := by
  induction depth generalizing tree with
  | zero => rfl
  | succ depth ih => cases tree <;> simp [recordTree,capture,TangoSquared.Paper20261030.Auxiliary.capture,node,ih]

theorem records_bound (depth : Nat) (tree : RawTree (Record α ρ)) :
    (capture depth tree).records.length+1 ≤ 2^depth := by
  induction depth generalizing tree with
  | zero => simp [capture,TangoSquared.Paper20261030.Auxiliary.Snapshot.records]
  | succ depth ih =>
    cases tree with
    | empty =>
      change 1 ≤ 2^(depth+1)
      exact Nat.pow_pos (n := depth+1) (by decide : 0 < 2)
    | node left entry right =>
      rw [capture_records_node]
      simp only [List.length_cons,List.length_append,pow_succ]
      have hl := ih left
      have hr := ih right
      omega

theorem four_levels (tree : RawTree (Record α ρ)) (nonempty : tree ≠ .empty)
    (outside : List (Pointer.Frame (Record α ρ))) :
    ∃ cost ≤ 43, Run program (.read 3 []) ⟨tree,outside⟩ (.done (capture 4 tree))
      ⟨tree,outside⟩ (capture 4 tree).records cost := by
  obtain ⟨cost,steps,equation⟩ := tour 3 tree nonempty [] outside
  have bound := records_bound 4 tree
  exact ⟨cost,by norm_num at bound equation; omega,steps.run rfl⟩

end DynamicOptimality.LocalSnapshot
