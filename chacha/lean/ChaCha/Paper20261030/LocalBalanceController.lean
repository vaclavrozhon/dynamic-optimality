import ChaCha.Paper20261030.LocalBalanceProgram

/-! The observation and rotation phases form one deterministic program.
The caller supplies no snapshot, rotation plan, or replacement sizes.
Starting at any nonempty auxiliary root, the program reads the required
records and performs the existing weight-balanced repair in at most
fifty-four charged operations, returning to the repaired subtree root. -/

namespace ChaCha.Paper20261030.Auxiliary.BalanceController

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open MTR DynamicOptimality DynamicOptimality.LocalProgram
open DynamicOptimality.LocalCommandList (Command)

variable {α ρ : Type*}

inductive State (α ρ : Type*) where
  | observing (state : LocalSnapshot.State α ρ)
  | repairing (commands : List (Command ρ))

def observing : LocalSnapshot.State α ρ → State α ρ
  | .done result => .repairing (commands (balancePlan result) result)
  | state => .observing state

def program : Program (State α ρ) α ρ
  | .observing state => (LocalSnapshot.program state).mapState observing
  | .repairing commands => (LocalCommandList.program commands).mapState .repairing

theorem observing_code (state : LocalSnapshot.State α ρ)
    (active : LocalSnapshot.program state ≠ .halt) :
    program (observing state) = (LocalSnapshot.program state).mapState observing := by
  cases state with
  | done => exact False.elim (active rfl)
  | read | left | right | up => rfl

theorem repairing_code (commands : List (Command ρ)) :
    program (α := α) (.repairing commands) =
      (LocalCommandList.program commands).mapState State.repairing := rfl

theorem balance_run (old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ))
    (outside : List (Pointer.Frame (NodeRecord α (fun _ => ρ)))) :
    ∃ cost ≤ 54, Run program (.observing (.read 3 []))
      ⟨recordTree (.inner old key value left right),outside⟩ (.repairing [])
      ⟨recordTree (balanceₘ key value left right),outside⟩
      (capture 4 (.inner old key value left right)).records cost := by
  obtain ⟨readCost,readBound,readRun⟩ := LocalSnapshot.four_levels
    (recordTree (.inner old key value left right)) (by simp [recordTree]) outside
  have inspected := readRun.map_prefix observing observing_code
  rw [LocalSnapshot.capture_recordTree] at inspected
  obtain ⟨repairCost,repairBound,repairRun⟩ := commands_run
    (balancePlan (capture 4 (.inner old key value left right))) old key value left right outside
  have repaired := repairRun.map_prefix (State.repairing (α := α)) (fun cs _ => repairing_code cs)
  have output : applyPlan (balancePlan (capture 4 (.inner old key value left right))) key value left right =
      balanceₘ key value left right := by
    change applyPlan (balancePlan (capture 4 (bin key value left right))) key value left right = _
    rw [balancePlan_depth 1,balancePlan_correct]
  rw [output] at repaired
  refine ⟨readCost+repairCost,by omega,?_⟩
  simpa only [observing,List.append_nil] using (inspected.append repaired).run rfl

end ChaCha.Paper20261030.Auxiliary.BalanceController
