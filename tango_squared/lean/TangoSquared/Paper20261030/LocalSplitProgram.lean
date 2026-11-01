import TangoSquared.Paper20261030.LocalJoinController
import TangoSquared.Paper20261030.ChargedSplit

/-! A local controller for exposing an existing auxiliary key.
The descent follows comparisons read at the current vertex. On return,
the old parent is read again to recover the direction and its total size.
The exposed key is rotated above that parent, the affected child is joined,
and the saved total size is written at the exposed root. The controller
keeps one split-depth counter and one saved size across each join. -/

namespace TangoSquared.Paper20261030.Auxiliary.SplitController

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open MTR DynamicOptimality DynamicOptimality.LocalProgram

variable {α ρ : Type*} [Ord α]

inductive State (α ρ : Type*) where
  | search (depth : Nat)
  | descend (depth : Nat) (left : Bool)
  | returning (depth : Nat)
  | parent (depth : Nat)
  | turn (depth : Nat) (left : Bool) (size : Nat)
  | enter (depth : Nat) (left : Bool) (size : Nat)
  | joining (depth size : Nat) (state : JoinController.State α ρ)
  | up (depth size : Nat)
  | write (depth size : Nat)

def searchNext (request : α) (depth : Nat) (view : View α ρ) : State α ρ :=
  match compare request view.entry.2.1 with
  | .eq => .returning depth
  | .lt => .descend depth true
  | .gt => .descend depth false

def parentNext (request : α) (depth : Nat) (view : View α ρ) : State α ρ :=
  match compare request view.entry.2.1 with
  | .eq => .returning depth
  | .lt => .turn depth true view.entry.1
  | .gt => .turn depth false view.entry.1

def joining (depth size : Nat) : JoinController.State α ρ → State α ρ
  | .returning 0 => .up depth size
  | state => .joining depth size state

def program (request : α) : Program (State α ρ) α ρ
  | .search depth => .read (searchNext request depth)
  | .descend depth left => .nav (if left then .left else .right) (.search (depth+1))
  | .returning 0 => .halt
  | .returning (depth+1) => .nav .up (.parent depth)
  | .parent depth => .read (parentNext request depth)
  | .turn depth left size => .nav (if left then .rotateRight else .rotateLeft) (.enter depth left size)
  | .enter depth left size => .nav (if left then .right else .left) (.joining depth size (.observing 0 (.read 3 [])))
  | .joining depth size state => (JoinController.program state).mapState (joining depth size)
  | .up depth size => .nav .up (.write depth size)
  | .write depth size => .writeSize size (.returning depth)

theorem joining_code (request : α) (depth size : Nat) (state : JoinController.State α ρ)
    (active : JoinController.program state ≠ .halt) :
    program request (joining depth size state) =
      (JoinController.program state).mapState (joining depth size) := by
  cases state with
  | returning depth => cases depth with
    | zero => exact False.elim (active rfl)
    | succ => rfl
  | observing | turn | descend | refresh | balancing => rfl

theorem join_prefix (request : α) (depth size : Nat) {old : Nat} {key : α} {value : ρ}
    {left right : Impl α (fun _ => ρ)} {leftBalanced : left.Balanced} {rightBalanced : right.Balanced}
    {outside reads cost}
    (run : Steps JoinController.program (.observing 0 (.read 3 []))
      ⟨recordTree (.inner old key value left right),outside⟩ (.returning 0)
      ⟨recordTree (link key value left right leftBalanced rightBalanced).impl,outside⟩ reads cost) :
    Steps (program request) (.joining depth size (.observing 0 (.read 3 [])))
      ⟨recordTree (.inner old key value left right),outside⟩ (.up depth size)
      ⟨recordTree (link key value left right leftBalanced rightBalanced).impl,outside⟩ reads cost :=
  (run.run rfl).map_prefix (joining depth size) (joining_code request depth size)

theorem read_search (request key : α) (depth old : Nat) (value : ρ)
    (left right : Impl α (fun _ => ρ)) (outside) :
    Step (program request) (.search depth) ⟨recordTree (.inner old key value left right),outside⟩
      (match compare request key with | .eq => .returning depth | .lt => .descend depth true | .gt => .descend depth false)
      ⟨recordTree (.inner old key value left right),outside⟩ (some (old,⟨key,value⟩)) := by
  apply Step.read (next := searchNext request depth)
    (view := ⟨(old,⟨key,value⟩),empty (recordTree left),empty (recordTree right)⟩) <;> rfl

theorem read_parent (request key : α) (depth old : Nat) (value : ρ)
    (left right : Impl α (fun _ => ρ)) (outside) :
    Step (program request) (.parent depth) ⟨recordTree (.inner old key value left right),outside⟩
      (match compare request key with | .eq => .returning depth | .lt => .turn depth true old | .gt => .turn depth false old)
      ⟨recordTree (.inner old key value left right),outside⟩ (some (old,⟨key,value⟩)) := by
  apply Step.read (next := parentNext request depth)
    (view := ⟨(old,⟨key,value⟩),empty (recordTree left),empty (recordTree right)⟩) <;> rfl

theorem turn_left (request : α) (depth size : Nat) (a b c : RawTree (NodeRecord α (fun _ => ρ))) (p q) (outside) :
    Steps (program request) (.turn depth true size) ⟨.node (.node a p b) q c,outside⟩
      (.joining depth size (.observing 0 (.read 3 []))) ⟨.node b q c,.right a p::outside⟩ [] 2 := by
  have first : Step (program request) (.turn depth true size) ⟨.node (.node a p b) q c,outside⟩
      (.enter depth true size) ⟨.node a p (.node b q c),outside⟩ none := .nav rfl rfl
  have second : Step (program request) (.enter depth true size) ⟨.node a p (.node b q c),outside⟩
      (.joining depth size (.observing 0 (.read 3 []))) ⟨.node b q c,.right a p::outside⟩ none := .nav rfl rfl
  exact .next first (.next second (.nil _ _))

theorem turn_right (request : α) (depth size : Nat) (a b c : RawTree (NodeRecord α (fun _ => ρ))) (p q) (outside) :
    Steps (program request) (.turn depth false size) ⟨.node a p (.node b q c),outside⟩
      (.joining depth size (.observing 0 (.read 3 []))) ⟨.node a p b,.left q c::outside⟩ [] 2 := by
  have first : Step (program request) (.turn depth false size) ⟨.node a p (.node b q c),outside⟩
      (.enter depth false size) ⟨.node (.node a p b) q c,outside⟩ none := .nav rfl rfl
  have second : Step (program request) (.enter depth false size) ⟨.node (.node a p b) q c,outside⟩
      (.joining depth size (.observing 0 (.read 3 []))) ⟨.node a p b,.left q c::outside⟩ none := .nav rfl rfl
  exact .next first (.next second (.nil _ _))

theorem finish_left (request : α) (depth size old : Nat) (key : α) (value : ρ)
    (left right : RawTree (NodeRecord α (fun _ => ρ))) (outside) :
    Steps (program request) (.up depth size) ⟨left,.left (old,⟨key,value⟩) right::outside⟩ (.returning depth)
      ⟨.node left (size,⟨key,value⟩) right,outside⟩ [] 2 := by
  have up : Step (program request) (.up depth size) ⟨left,.left (old,⟨key,value⟩) right::outside⟩
      (.write depth size) ⟨.node left (old,⟨key,value⟩) right,outside⟩ none := .nav rfl rfl
  have write : Step (program request) (.write depth size) ⟨.node left (old,⟨key,value⟩) right,outside⟩
      (.returning depth) ⟨.node left (size,⟨key,value⟩) right,outside⟩ none := .writeSize rfl
  exact .next up (.next write (.nil _ _))

theorem finish_right (request : α) (depth size old : Nat) (key : α) (value : ρ)
    (left right : RawTree (NodeRecord α (fun _ => ρ))) (outside) :
    Steps (program request) (.up depth size) ⟨right,.right left (old,⟨key,value⟩)::outside⟩ (.returning depth)
      ⟨.node left (size,⟨key,value⟩) right,outside⟩ [] 2 := by
  have up : Step (program request) (.up depth size) ⟨right,.right left (old,⟨key,value⟩)::outside⟩
      (.write depth size) ⟨.node left (old,⟨key,value⟩) right,outside⟩ none := .nav rfl rfl
  have write : Step (program request) (.write depth size) ⟨.node left (old,⟨key,value⟩) right,outside⟩
      (.returning depth) ⟨.node left (size,⟨key,value⟩) right,outside⟩ none := .writeSize rfl
  exact .next up (.next write (.nil _ _))

end TangoSquared.Paper20261030.Auxiliary.SplitController
