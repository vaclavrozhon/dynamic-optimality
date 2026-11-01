import TangoSquared.Paper20261030.LocalBoundaryRepairProgram
import TangoSquared.Paper20261030.BoundaryReplacement

/-! The one-boundary repair wrapper implements the existing prefix and
suffix replacements. Its subprogram is an actual local run. Every read,
marker update, navigation, and join in the wrapper is charged. -/

namespace TangoSquared.Paper20261030.BoundaryObservations.BoundaryRepairController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram GapSource.Controller

variable {α κ ρ σ : Type*} [Ord κ] [LawfulEqOrd κ]

theorem replace_prefix (component fresh : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (freshClean : Clean fresh.core) (freshMarked : MarkedPorts fresh)
    (terminal : fresh.core = .leaf → isLeaf fresh.tree = true)
    (key : κ) (found : searchResult key component.core = true)
    (repair : Program σ (MarkedRecord κ ρ)) (initial last : σ) (reads budget)
    (body : Run repair initial ⟨closed (cutLeft component key found),[]⟩ last ⟨closed fresh,[]⟩ reads budget)
    (K : Nat) (oldSize : component.core.size ≤ K) (newSize : (replacePrefix component key found fresh).core.size ≤ K)
    (outside) :
    ∃ observed cost, Run (program key false repair initial) (.marker .openOuter .start)
      ⟨closed component,outside⟩ .done ⟨closed (replacePrefix component key found fresh),outside⟩ observed cost ∧
      cost ≤ budget+44310*Nat.clog 2 (K+1)+318 := by
  have nonempty : component.core ≠ .leaf := by intro empty; simp only [empty,searchResult,Bool.false_eq_true] at found
  obtain ⟨openReads,openCost,openRun,openBound⟩ := RootMarkerController.open_component component clean marked
    (by intro empty; exact False.elim (nonempty empty)) outside
  have opened := openRun.map_prefix (marking repair initial .openOuter) (marking_code key false repair initial .openOuter)
  obtain ⟨splitReads,splitCost,splitRun,splitBound⟩ := CleanController.split component clean marked key found outside
  have exposed := splitRun.map_prefix splitting (splitting_code key false repair initial)
  obtain ⟨childReads,childCost,childRun,childBound⟩ := child_repair key false repair initial last
    (component.core.size,⟨key,(splitAt key component.core component.balanced found).value⟩)
    (cutRight component key found).tree (cutLeft component key found) fresh freshClean freshMarked terminal reads budget outside body
  obtain ⟨separatorClean,_,rightClean⟩ := clean_split component clean key found
  obtain ⟨joinReads,joinCost,joinRun,joinBound⟩ := CleanController.join_components fresh (cutRight component key found)
    freshClean rightClean freshMarked (marked_cutRight component marked key found) key
    (splitAt key component.core component.balanced found).value separatorClean component.core.size outside
  have joined := joinRun.map_prefix joining (joining_code key false repair initial)
  have finished := (RootMarkerController.close_component (replacePrefix component key found fresh) outside).map_prefix
    (marking repair initial .closeOuter) (marking_code key false repair initial .closeOuter)
  have full := (((opened.append exposed).append childRun).append joined).append finished
  have size : (replacePrefix component key found fresh).core.size = fresh.core.size+1+(cutRight component key found).core.size := join_size _ _ _ _
  have oldRank := Nat.clog_monotone 2 (Nat.add_le_add_right oldSize 1)
  have freshRank := Nat.clog_monotone 2 (show fresh.core.size+1 ≤ K+1 by omega)
  have rightRank := Nat.clog_monotone 2 (show (cutRight component key found).core.size+1 ≤ K+1 by omega)
  exact ⟨_,_,full.run rfl,by omega⟩

theorem replace_suffix (component fresh : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (freshClean : Clean fresh.core) (freshMarked : MarkedPorts fresh)
    (terminal : fresh.core = .leaf → isLeaf fresh.tree = true)
    (key : κ) (found : searchResult key component.core = true)
    (repair : Program σ (MarkedRecord κ ρ)) (initial last : σ) (reads budget)
    (body : Run repair initial ⟨closed (cutRight component key found),[]⟩ last ⟨closed fresh,[]⟩ reads budget)
    (K : Nat) (oldSize : component.core.size ≤ K) (newSize : (replaceSuffix component key found fresh).core.size ≤ K)
    (outside) :
    ∃ observed cost, Run (program key true repair initial) (.marker .openOuter .start)
      ⟨closed component,outside⟩ .done ⟨closed (replaceSuffix component key found fresh),outside⟩ observed cost ∧
      cost ≤ budget+44310*Nat.clog 2 (K+1)+318 := by
  have nonempty : component.core ≠ .leaf := by intro empty; simp only [empty,searchResult,Bool.false_eq_true] at found
  obtain ⟨openReads,openCost,openRun,openBound⟩ := RootMarkerController.open_component component clean marked
    (by intro empty; exact False.elim (nonempty empty)) outside
  have opened := openRun.map_prefix (marking repair initial .openOuter) (marking_code key true repair initial .openOuter)
  obtain ⟨splitReads,splitCost,splitRun,splitBound⟩ := CleanController.split component clean marked key found outside
  have exposed := splitRun.map_prefix splitting (splitting_code key true repair initial)
  obtain ⟨childReads,childCost,childRun,childBound⟩ := child_repair key true repair initial last
    (component.core.size,⟨key,(splitAt key component.core component.balanced found).value⟩)
    (cutLeft component key found).tree (cutRight component key found) fresh freshClean freshMarked terminal reads budget outside body
  obtain ⟨separatorClean,leftClean,_⟩ := clean_split component clean key found
  obtain ⟨joinReads,joinCost,joinRun,joinBound⟩ := CleanController.join_components (cutLeft component key found) fresh
    leftClean freshClean (marked_cutLeft component marked key found) freshMarked key
    (splitAt key component.core component.balanced found).value separatorClean component.core.size outside
  have joined := joinRun.map_prefix joining (joining_code key true repair initial)
  have finished := (RootMarkerController.close_component (replaceSuffix component key found fresh) outside).map_prefix
    (marking repair initial .closeOuter) (marking_code key true repair initial .closeOuter)
  have full := (((opened.append exposed).append childRun).append joined).append finished
  have size : (replaceSuffix component key found fresh).core.size = (cutLeft component key found).core.size+1+fresh.core.size := join_size _ _ _ _
  have oldRank := Nat.clog_monotone 2 (Nat.add_le_add_right oldSize 1)
  have freshRank := Nat.clog_monotone 2 (show fresh.core.size+1 ≤ K+1 by omega)
  have leftRank := Nat.clog_monotone 2 (show (cutLeft component key found).core.size+1 ≤ K+1 by omega)
  exact ⟨_,_,full.run rfl,by omega⟩

end TangoSquared.Paper20261030.BoundaryObservations.BoundaryRepairController
