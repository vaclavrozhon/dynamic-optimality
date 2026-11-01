import DynamicOptimality.LocalSnapshotSpace
import DynamicOptimality.LocalCommandList
import TangoSquared.Paper20261030.ChargedBalance

/-! A concrete local controller for the auxiliary balancing primitive.
All branching and replacement sizes are computed from the four-level
snapshot. The selected command list uses at most eleven instructions. -/

namespace TangoSquared.Paper20261030.Auxiliary.BalanceController

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open MTR DynamicOptimality DynamicOptimality.LocalProgram
open DynamicOptimality.LocalCommandList (Command)

variable {α ρ : Type*}

def commands (plan : BalancePlan) : Snapshot α (fun _ => ρ) → List (Command ρ)
  | .node _ _ _ l r =>
    let unchanged := [Command.writeSize (l.size+1+r.size)]
    match plan,l,r with
    | .singleLeft,l,.node _ _ _ rl rr =>
        let lower := l.size+1+rl.size
        [.nav .rotateLeft,.nav .left,.writeSize lower,.nav .up,.writeSize (lower+1+rr.size)]
    | .singleRight,.node _ _ _ ll lr,r =>
        let lower := lr.size+1+r.size
        [.nav .rotateRight,.nav .right,.writeSize lower,.nav .up,.writeSize (ll.size+1+lower)]
    | .doubleLeft,l,.node _ _ _ (.node _ _ _ ml mr) rr =>
        let lowerLeft := l.size+1+ml.size
        let lowerRight := mr.size+1+rr.size
        [.nav .right,.nav .rotateRight,.nav .up,.nav .rotateLeft,
         .nav .left,.writeSize lowerLeft,.nav .up,
         .nav .right,.writeSize lowerRight,.nav .up,.writeSize (lowerLeft+1+lowerRight)]
    | .doubleRight,.node _ _ _ ll (.node _ _ _ ml mr),r =>
        let lowerLeft := ll.size+1+ml.size
        let lowerRight := mr.size+1+r.size
        [.nav .left,.nav .rotateLeft,.nav .up,.nav .rotateRight,
         .nav .left,.writeSize lowerLeft,.nav .up,
         .nav .right,.writeSize lowerRight,.nav .up,.writeSize (lowerLeft+1+lowerRight)]
    | _,_,_ => unchanged
  | _ => []

theorem commands_run (plan : BalancePlan) (old : Nat) (key : α) (value : ρ)
    (left right : Impl α (fun _ => ρ)) (outside) :
    ∃ cost ≤ 11, Run LocalCommandList.program
      (commands plan (capture 4 (.inner old key value left right)))
      ⟨recordTree (.inner old key value left right),outside⟩ []
      ⟨recordTree (applyPlan plan key value left right),outside⟩ [] cost := by
  cases plan with
  | keep =>
    refine ⟨1,by decide,?_⟩
    apply LocalCommandList.run_writeSize
    simp only [capture_size]
    apply Run.halt
    rfl
  | singleLeft =>
    cases right with
    | leaf =>
      refine ⟨1,by decide,?_⟩
      apply LocalCommandList.run_writeSize
      simp only [capture_size]
      apply Run.halt
      rfl
    | inner size rk rv rl rr =>
      refine ⟨5,by decide,?_⟩
      apply LocalCommandList.run_nav (by rfl)
      apply LocalCommandList.run_nav (by rfl)
      apply LocalCommandList.run_writeSize
      apply LocalCommandList.run_nav (by rfl)
      apply LocalCommandList.run_writeSize
      simp only [capture_size]
      apply Run.halt
      rfl
  | singleRight =>
    cases left with
    | leaf =>
      refine ⟨1,by decide,?_⟩
      apply LocalCommandList.run_writeSize
      simp only [capture_size]
      apply Run.halt
      rfl
    | inner size lk lv ll lr =>
      refine ⟨5,by decide,?_⟩
      apply LocalCommandList.run_nav (by rfl)
      apply LocalCommandList.run_nav (by rfl)
      apply LocalCommandList.run_writeSize
      apply LocalCommandList.run_nav (by rfl)
      apply LocalCommandList.run_writeSize
      simp only [capture_size]
      apply Run.halt
      rfl
  | doubleLeft =>
    cases right with
    | leaf =>
      refine ⟨1,by decide,?_⟩
      apply LocalCommandList.run_writeSize
      simp only [capture_size]
      apply Run.halt
      rfl
    | inner size rk rv rl rr =>
      cases rl with
      | leaf =>
        refine ⟨1,by decide,?_⟩
        apply LocalCommandList.run_writeSize
        simp only [capture_size]
        apply Run.halt
        rfl
      | inner midSize mk mv ml mr =>
        refine ⟨11,le_rfl,?_⟩
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_writeSize
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_writeSize
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_writeSize
        simp only [capture_size]
        apply Run.halt
        rfl
  | doubleRight =>
    cases left with
    | leaf =>
      refine ⟨1,by decide,?_⟩
      apply LocalCommandList.run_writeSize
      simp only [capture_size]
      apply Run.halt
      rfl
    | inner size lk lv ll lr =>
      cases lr with
      | leaf =>
        refine ⟨1,by decide,?_⟩
        apply LocalCommandList.run_writeSize
        simp only [capture_size]
        apply Run.halt
        rfl
      | inner midSize mk mv ml mr =>
        refine ⟨11,le_rfl,?_⟩
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_writeSize
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_writeSize
        apply LocalCommandList.run_nav (by rfl)
        apply LocalCommandList.run_writeSize
        simp only [capture_size]
        apply Run.halt
        rfl

end TangoSquared.Paper20261030.Auxiliary.BalanceController
