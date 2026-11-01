import TangoSquared.Paper20261030.GapSourceFinitePorts
import TangoSquared.Paper20261030.SourceProgramExtension
import TangoSquared.Paper20261030.LocalSplitController

/-! Concrete auxiliary programs in the marked-port source representation.
All attached payload trees are preserved literally. The finite marker
premise concerns exactly the existing ports of the component; there is no
global marker assumption, externally supplied snapshot, or stored tree in
the controller's register state. -/

namespace TangoSquared.Paper20261030.Auxiliary.SourceController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open MTR ColoredStorage DynamicOptimality SourceLocalProgram GapSource.Controller

variable {α κ ρ : Type*}

def tree (core : Impl κ (fun _ => ρ)) (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat) :
    Source α (MarkedRecord κ ρ) := GapSource.encode (Relabel.tree mark (recordTree core)) ports base

theorem balance (old : Nat) (key : κ) (value : ρ) (left right : Impl κ (fun _ => ρ))
    (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base+(recordTree (.inner old key value left right)).size → boundary (ports i).rootRecord = true)
    (outside) :
    ∃ reads cost, Run (code BalanceController.program) (.ready (.observing (.read 3 [])))
      ⟨tree (.inner old key value left right) ports base,outside⟩ (.ready (.repairing []))
      ⟨tree (balanceₘ key value left right) ports base,outside⟩ reads cost ∧ cost ≤ 378 := by
  obtain ⟨budget,bound,run⟩ := BalanceController.balance_run old key value left right []
  obtain ⟨reads,cost,compiled,compiledBound⟩ := compile_root_run run ports base marked
  exact ⟨reads,cost,compiled.extend outside,by omega⟩

theorem join (old : Nat) (key : κ) (value : ρ) (left right : Impl κ (fun _ => ρ))
    (leftBalanced : left.Balanced) (rightBalanced : right.Balanced)
    (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base+(recordTree (.inner old key value left right)).size → boundary (ports i).rootRecord = true)
    (outside) :
    ∃ reads cost, Run (code JoinController.program) (.ready (.observing 0 (.read 3 [])))
      ⟨tree (.inner old key value left right) ports base,outside⟩ (.ready (.returning 0))
      ⟨tree (link key value left right leftBalanced rightBalanced).impl ports base,outside⟩ reads cost ∧
      cost ≤ 2100*(Nat.clog 2 (left.size+1)+Nat.clog 2 (right.size+1))+308 := by
  obtain ⟨observations,budget,run,bound⟩ := JoinController.link_run old key value left right leftBalanced rightBalanced []
  obtain ⟨reads,cost,compiled,compiledBound⟩ := compile_root_run run ports base marked
  exact ⟨reads,cost,compiled.extend outside,by omega⟩

theorem split [Ord κ] [LawfulEqOrd κ] (request : κ) (core : Impl κ (fun _ => ρ))
    (balanced : core.Balanced) (found : searchResult request core = true)
    (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base+(recordTree core).size → boundary (ports i).rootRecord = true)
    (outside) :
    ∃ reads cost, Run (code (SplitController.program request)) (.ready (.search 0))
      ⟨tree core ports base,outside⟩ (.ready (.returning 0))
      ⟨tree (splitAt request core balanced found).impl ports base,outside⟩ reads cost ∧
      cost ≤ 40110*Nat.clog 2 (core.size+1) := by
  obtain ⟨observations,budget,run,bound⟩ := SplitController.split_run request core balanced found []
  obtain ⟨reads,cost,compiled,compiledBound⟩ := compile_root_run run ports base marked
  exact ⟨reads,cost,compiled.extend outside,by omega⟩

end TangoSquared.Paper20261030.Auxiliary.SourceController
