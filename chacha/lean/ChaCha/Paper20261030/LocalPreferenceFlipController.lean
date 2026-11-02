import ChaCha.Paper20261030.LocalPreferenceFlipProgram

/-! Exact runs of both head-preference flips on the maintained component
representation. The output is the existing `preferRight` or `preferLeft`.
The input head key is exposed by an actual split, and the updated payload
is computed from that reached separator's record. -/

namespace ChaCha.Paper20261030.BoundaryObservations.PreferenceFlipController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram

variable {α κ ρ : Type*} [Ord κ] [LawfulEqOrd κ]

theorem prefer_right (outer incoming : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (outerClean : Clean outer.core) (incomingClean : Clean incoming.core)
    (outerMarked : MarkedPorts outer) (incomingMarked : MarkedPorts incoming)
    (terminal : incoming.core = .leaf → isLeaf incoming.tree = true)
    (key : κ) (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).right = .leaf)
    (attached : outer.ports outer.core.size = closed incoming)
    (update : κ → ρ → ρ) (outside) :
    let fresh := (update key (splitAt key outer.core outer.balanced found).value.1,false)
    ∃ reads cost, Run (program key true update) (.opening .start) ⟨closed outer,outside⟩ .done
      ⟨closed (preferRight outer incoming key found fresh),outside⟩ reads cost ∧
      cost ≤ 40110*Nat.clog 2 (outer.core.size+1)+2100*Nat.clog 2 (incoming.core.size+1)+322 := by
  let fresh := (update key (splitAt key outer.core outer.balanced found).value.1,false)
  have nonempty : outer.core ≠ .leaf := by intro empty; simp only [empty,searchResult,Bool.false_eq_true] at found
  obtain ⟨openReads,openCost,openRun,openBound⟩ := RootMarkerController.open_component outer outerClean outerMarked
    (by intro empty; exact False.elim (nonempty empty)) outside
  have opened := openRun.map_prefix opening (opening_code key true update)
  obtain ⟨splitReads,splitCost,splitRun,splitBound⟩ := CleanController.split outer outerClean outerMarked key found outside
  rw [cutRight_empty_tree outer key found empty,attached] at splitRun
  have exposed := splitRun.map_prefix splitting (splitting_code key true update)
  have detached := detach_prefix key true update
    (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩)
    (closed incoming) (cutLeft outer key found) outside
  have changed := update_prefix key true update
    (Source.fork (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩)
      (closed (cutLeft outer key found)) (closed incoming)) outside
  obtain ⟨incomingReads,incomingCost,incomingRun,incomingBound⟩ := incoming_prefix key true update
    (outer.core.size,⟨key,fresh⟩) (closed (cutLeft outer key found)) incoming incomingClean incomingMarked terminal outside
  obtain ⟨joinReads,joinCost,joinRun,joinBound⟩ := CleanController.prepend incoming incomingClean incomingMarked
    key fresh rfl (closed (cutLeft outer key found)) (closed_entry _) outer.core.size outside
  have joined := joinRun.map_prefix joining (joining_code key true update)
  have finished := (RootMarkerController.close_component (preferRight outer incoming key found fresh) outside).map_prefix
    closing (closing_code key true update)
  have full := (((((opened.append exposed).append detached).append changed).append incomingRun).append joined).append finished
  exact ⟨_,_,full.run rfl,by omega⟩

theorem prefer_left (incoming outer : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (incomingClean : Clean incoming.core) (outerClean : Clean outer.core)
    (incomingMarked : MarkedPorts incoming) (outerMarked : MarkedPorts outer)
    (terminal : incoming.core = .leaf → isLeaf incoming.tree = true)
    (key : κ) (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).left = .leaf)
    (attached : outer.ports 0 = closed incoming)
    (update : κ → ρ → ρ) (outside) :
    let fresh := (update key (splitAt key outer.core outer.balanced found).value.1,false)
    ∃ reads cost, Run (program key false update) (.opening .start) ⟨closed outer,outside⟩ .done
      ⟨closed (preferLeft incoming outer key found fresh),outside⟩ reads cost ∧
      cost ≤ 40110*Nat.clog 2 (outer.core.size+1)+2100*Nat.clog 2 (incoming.core.size+1)+322 := by
  let fresh := (update key (splitAt key outer.core outer.balanced found).value.1,false)
  have nonempty : outer.core ≠ .leaf := by intro empty; simp only [empty,searchResult,Bool.false_eq_true] at found
  obtain ⟨openReads,openCost,openRun,openBound⟩ := RootMarkerController.open_component outer outerClean outerMarked
    (by intro empty; exact False.elim (nonempty empty)) outside
  have opened := openRun.map_prefix opening (opening_code key false update)
  obtain ⟨splitReads,splitCost,splitRun,splitBound⟩ := CleanController.split outer outerClean outerMarked key found outside
  rw [cutLeft_empty_tree outer key found empty,attached] at splitRun
  have exposed := splitRun.map_prefix splitting (splitting_code key false update)
  have detached := detach_prefix key false update
    (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩)
    (closed incoming) (cutRight outer key found) outside
  have changed := update_prefix key false update
    (Source.fork (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩)
      (closed incoming) (closed (cutRight outer key found))) outside
  obtain ⟨incomingReads,incomingCost,incomingRun,incomingBound⟩ := incoming_prefix key false update
    (outer.core.size,⟨key,fresh⟩) (closed (cutRight outer key found)) incoming incomingClean incomingMarked terminal outside
  obtain ⟨joinReads,joinCost,joinRun,joinBound⟩ := CleanController.append incoming incomingClean incomingMarked
    key fresh rfl (closed (cutRight outer key found)) (closed_entry _) outer.core.size outside
  have joined := joinRun.map_prefix joining (joining_code key false update)
  have finished := (RootMarkerController.close_component (preferLeft incoming outer key found fresh) outside).map_prefix
    closing (closing_code key false update)
  have full := (((((opened.append exposed).append detached).append changed).append incomingRun).append joined).append finished
  exact ⟨_,_,full.run rfl,by omega⟩

end ChaCha.Paper20261030.BoundaryObservations.PreferenceFlipController
