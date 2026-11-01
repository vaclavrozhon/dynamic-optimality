import TangoSquared.Paper20261030.LocalMarkedCutProgram

/-! Exact correctness and logarithmic cost of the marked-component cut.
The output is the existing `cutMarked`, so its established clean-core and
marked-port invariants apply directly to this actual local execution. -/

namespace TangoSquared.Paper20261030.BoundaryObservations.MarkedCutController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram

variable {α κ ρ : Type*} [Ord κ] [LawfulEqOrd κ]

theorem cut (component : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (key : κ) (found : searchResult key component.core = true) (outside) :
    ∃ reads cost, Run (program key) .start ⟨closed component,outside⟩ .done
      ⟨closed (cutMarked component key found),outside⟩ reads cost ∧
      cost ≤ 42210*Nat.clog 2 (component.core.size+1)+316 := by
  have nonempty : component.core ≠ .leaf := by intro empty; simp only [empty,searchResult,Bool.false_eq_true] at found
  obtain ⟨splitReads,splitCost,splitRun,splitBound⟩ := CleanController.split component clean marked key found outside
  obtain ⟨separatorClean,leftClean,_⟩ := clean_split component clean key found
  obtain ⟨joinReads,joinCost,joinRun,joinBound⟩ := CleanController.append (cutLeft component key found)
    leftClean (marked_cutLeft component marked key found) key
    (splitAt key component.core component.balanced found).value separatorClean
    (closed (cutRight component key found)) (closed_entry _) component.core.size outside
  have opened := open_prefix key component clean nonempty outside
  have exposed := splitRun.map_prefix splitting (splitting_code key)
  have detached := suffix_prefix key
    (component.core.size,⟨key,(splitAt key component.core component.balanced found).value⟩)
    (cutLeft component key found).tree (cutRight component key found) outside
  have joined := joinRun.map_prefix joining (joining_code key)
  have finished := close_prefix key (cutMarked component key found) outside
  have full := (((opened.append exposed).append detached).append joined).append finished
  have size := splitAt_size key component.core component.balanced found
  have rank := Nat.clog_monotone 2
    (show (cutLeft component key found).core.size+1 ≤ component.core.size+1 by
      change (splitAt key component.core component.balanced found).left.size+1 ≤ _
      omega)
  exact ⟨_,_,full.run rfl,by omega⟩

end TangoSquared.Paper20261030.BoundaryObservations.MarkedCutController
