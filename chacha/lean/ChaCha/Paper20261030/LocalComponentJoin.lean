import ChaCha.Paper20261030.CleanAuxiliaryControllers
import ChaCha.Paper20261030.MarkedJoin

/-! The actual join controller on the existing pair of clean components.
Its result is literally the component used by the decomposition proofs. -/

namespace ChaCha.Paper20261030.BoundaryObservations.CleanController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram GapSource.Controller

variable {α κ ρ : Type*} [Ord κ]

theorem join_components (left right : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (leftClean : Clean left.core) (rightClean : Clean right.core)
    (leftMarked : MarkedPorts left) (rightMarked : MarkedPorts right)
    (key : κ) (value : ρ×Bool) (unmarked : value.2 = false) (old : Nat) (outside) :
    ∃ reads cost, Run (code JoinController.program) (.ready (.observing 0 (.read 3 [])))
      ⟨.fork (old,⟨key,value⟩) left.tree right.tree,outside⟩ (.ready (.returning 0))
      ⟨(AuxiliaryComponent.join key value left right).tree,outside⟩ reads cost ∧
      cost ≤ 2100*(Nat.clog 2 (left.core.size+1)+Nat.clog 2 (right.core.size+1))+308 := by
  obtain ⟨reads,cost,run,bound⟩ := join old key value unmarked left.core right.core leftClean rightClean
    left.balanced right.balanced (AuxiliaryComponent.join key value left right).ports
    (by intro i hi; apply marked_join key value left right leftMarked rightMarked i; rw [join_size]; exact hi) outside
  rw [join_input] at run
  exact ⟨reads,cost,run,bound⟩

end ChaCha.Paper20261030.BoundaryObservations.CleanController
