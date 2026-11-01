import TangoSquared.Paper20261030.LocalBalanceController
import TangoSquared.Paper20261030.ChargedJoin

/-! A local controller for joining two auxiliary trees around their
existing separator. The unfinished recursion is the actual ancestor path.
One counter records how many ancestors require repair; no list of saved
subtrees or recursive arguments occurs in the controller state. -/

namespace TangoSquared.Paper20261030.Auxiliary.JoinController

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open MTR DynamicOptimality DynamicOptimality.LocalProgram

variable {α ρ : Type*}

inductive Choice where
  | descend (right : Bool)
  | refresh (size : Nat)

def choice : Snapshot α (fun _ => ρ) → Choice
  | .node _ _ _ .empty .empty => .refresh 1
  | .node _ _ _ .empty (.node _ _ _ _ _) => .descend true
  | .node _ _ _ (.node _ _ _ _ _) .empty => .descend false
  | .node _ _ _ (.node left _ _ _ _) (.node right _ _ _ _) =>
      if delta*left < right then .descend true
      else if delta*right < left then .descend false
      else .refresh (left+1+right)
  | _ => .refresh 1

inductive State (α ρ : Type*) where
  | observing (depth : Nat) (state : LocalSnapshot.State α ρ)
  | turn (depth : Nat) (right : Bool)
  | descend (depth : Nat) (right : Bool)
  | refresh (depth size : Nat)
  | balancing (depth : Nat) (state : BalanceController.State α ρ)
  | returning (depth : Nat)

def dispatch (depth : Nat) : Choice → State α ρ
  | .descend right => .turn depth right
  | .refresh size => .refresh depth size

def observing (depth : Nat) : LocalSnapshot.State α ρ → State α ρ
  | .done result => dispatch depth (choice result)
  | state => .observing depth state

def balancing (depth : Nat) : BalanceController.State α ρ → State α ρ
  | .repairing [] => .returning depth
  | state => .balancing depth state

def program : Program (State α ρ) α ρ
  | .observing depth state => (LocalSnapshot.program state).mapState (observing depth)
  | .turn depth right => .nav (if right then .rotateLeft else .rotateRight) (.descend depth right)
  | .descend depth right => .nav (if right then .left else .right) (.observing (depth+1) (.read 3 []))
  | .refresh depth size => .writeSize size (.returning depth)
  | .balancing depth state => (BalanceController.program state).mapState (balancing depth)
  | .returning 0 => .halt
  | .returning (depth+1) => .nav .up (.balancing depth (.observing (.read 3 [])))

theorem observing_code (depth : Nat) (state : LocalSnapshot.State α ρ)
    (active : LocalSnapshot.program state ≠ .halt) :
    program (observing depth state) = (LocalSnapshot.program state).mapState (observing depth) := by
  cases state with
  | done => exact False.elim (active rfl)
  | read | left | right | up => rfl

theorem balancing_code (depth : Nat) (state : BalanceController.State α ρ)
    (active : BalanceController.program state ≠ .halt) :
    program (balancing depth state) = (BalanceController.program state).mapState (balancing depth) := by
  cases state with
  | observing => rfl
  | repairing commands => cases commands with
    | nil => exact False.elim (active rfl)
    | cons => rfl

theorem inspect (depth old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ)) (outside) :
    ∃ cost ≤ 43, Steps program (.observing depth (.read 3 []))
      ⟨recordTree (.inner old key value left right),outside⟩
      (dispatch depth (choice (capture 4 (.inner old key value left right))))
      ⟨recordTree (.inner old key value left right),outside⟩
      (capture 4 (.inner old key value left right)).records cost := by
  obtain ⟨cost,bound,run⟩ := LocalSnapshot.four_levels
    (recordTree (.inner old key value left right)) (by simp [recordTree]) outside
  have compiled := run.map_prefix (observing depth) (observing_code depth)
  rw [LocalSnapshot.capture_recordTree] at compiled
  exact ⟨cost,bound,compiled⟩

theorem balance (depth old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ)) (outside) :
    ∃ cost ≤ 54, Steps program (.balancing depth (.observing (.read 3 [])))
      ⟨recordTree (.inner old key value left right),outside⟩ (.returning depth)
      ⟨recordTree (balanceₘ key value left right),outside⟩
      (capture 4 (.inner old key value left right)).records cost := by
  obtain ⟨cost,bound,run⟩ := BalanceController.balance_run old key value left right outside
  exact ⟨cost,bound,run.map_prefix (balancing depth) (balancing_code depth)⟩

theorem turn_right (depth : Nat) (a b c : RawTree (NodeRecord α (fun _ => ρ))) (p q) (outside) :
    Steps program (.turn depth true) ⟨.node a p (.node b q c),outside⟩
      (.observing (depth+1) (.read 3 [])) ⟨.node a p b,.left q c::outside⟩ [] 2 := by
  have first : Step program (.turn depth true) ⟨.node a p (.node b q c),outside⟩
      (.descend depth true) ⟨.node (.node a p b) q c,outside⟩ none := .nav rfl rfl
  have second : Step program (.descend depth true) ⟨.node (.node a p b) q c,outside⟩
      (.observing (depth+1) (.read 3 [])) ⟨.node a p b,.left q c::outside⟩ none := .nav rfl rfl
  exact .next first (.next second (.nil _ _))

theorem turn_left (depth : Nat) (a b c : RawTree (NodeRecord α (fun _ => ρ))) (p q) (outside) :
    Steps program (.turn depth false) ⟨.node (.node a p b) q c,outside⟩
      (.observing (depth+1) (.read 3 [])) ⟨.node b q c,.right a p::outside⟩ [] 2 := by
  have first : Step program (.turn depth false) ⟨.node (.node a p b) q c,outside⟩
      (.descend depth false) ⟨.node a p (.node b q c),outside⟩ none := .nav rfl rfl
  have second : Step program (.descend depth false) ⟨.node a p (.node b q c),outside⟩
      (.observing (depth+1) (.read 3 [])) ⟨.node b q c,.right a p::outside⟩ none := .nav rfl rfl
  exact .next first (.next second (.nil _ _))

theorem return_left (depth old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ)) (outside) :
    ∃ cost ≤ 55, Steps program (.returning (depth+1))
      ⟨recordTree left,.left (old,⟨key,value⟩) (recordTree right)::outside⟩ (.returning depth)
      ⟨recordTree (balanceₘ key value left right),outside⟩
      (capture 4 (.inner old key value left right)).records cost := by
  obtain ⟨cost,bound,run⟩ := balance depth old key value left right outside
  have up : Step program (.returning (depth+1))
      ⟨recordTree left,.left (old,⟨key,value⟩) (recordTree right)::outside⟩
      (.balancing depth (.observing (.read 3 [])))
      ⟨recordTree (.inner old key value left right),outside⟩ none := .nav rfl rfl
  exact ⟨cost+1,by omega,.next up run⟩

theorem return_right (depth old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ)) (outside) :
    ∃ cost ≤ 55, Steps program (.returning (depth+1))
      ⟨recordTree right,.right (recordTree left) (old,⟨key,value⟩)::outside⟩ (.returning depth)
      ⟨recordTree (balanceₘ key value left right),outside⟩
      (capture 4 (.inner old key value left right)).records cost := by
  obtain ⟨cost,bound,run⟩ := balance depth old key value left right outside
  have up : Step program (.returning (depth+1))
      ⟨recordTree right,.right (recordTree left) (old,⟨key,value⟩)::outside⟩
      (.balancing depth (.observing (.read 3 [])))
      ⟨recordTree (.inner old key value left right),outside⟩ none := .nav rfl rfl
  exact ⟨cost+1,by omega,.next up run⟩

end TangoSquared.Paper20261030.Auxiliary.JoinController
