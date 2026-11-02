import ChaCha.Paper20261030.LocalBoundaryRepairController

/-! Two nested boundary wrappers repair an interior interval. There are
exactly two wrapper levels, independent of the auxiliary size. Each joins
at the same existing boundary separator as `replaceMiddle`. -/

namespace ChaCha.Paper20261030.BoundaryObservations.BoundaryRepairController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram GapSource.Controller

variable {α κ ρ σ : Type*} [Ord κ] [LawfulEqOrd κ]

theorem replace_middle (component fresh : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (freshClean : Clean fresh.core) (freshMarked : MarkedPorts fresh)
    (terminal : fresh.core = .leaf → isLeaf fresh.tree = true)
    (lo : κ) (fl : searchResult lo component.core = true)
    (hi : κ) (fh : searchResult hi (cutRight component lo fl).core = true)
    (repair : Program σ (MarkedRecord κ ρ)) (initial last : σ) (reads budget)
    (body : Run repair initial ⟨closed (middle component lo fl hi fh),[]⟩ last ⟨closed fresh,[]⟩ reads budget)
    (K : Nat) (oldSize : component.core.size ≤ K) (newSize : (replaceMiddle component lo fl hi fh fresh).core.size ≤ K)
    (outside) :
    ∃ observed cost, Run (program lo true (program hi false repair initial) (.marker .openOuter .start))
      (.marker .openOuter .start) ⟨closed component,outside⟩ .done
      ⟨closed (replaceMiddle component lo fl hi fh fresh),outside⟩ observed cost ∧
      cost ≤ budget+88620*Nat.clog 2 (K+1)+636 := by
  let upper := cutRight component lo fl
  let repairedUpper := replacePrefix upper hi fh fresh
  have upperSize : upper.core.size ≤ K := (cutRight_size_le component lo fl).trans oldSize
  have totalSize : (replaceMiddle component lo fl hi fh fresh).core.size =
      (cutLeft component lo fl).core.size+1+repairedUpper.core.size := join_size _ _ _ _
  have repairedSize : repairedUpper.core.size ≤ K := by omega
  have upperClean : Clean upper.core := (clean_split component clean lo fl).2.2
  have upperMarked : MarkedPorts upper := marked_cutRight component marked lo fl
  obtain ⟨innerReads,innerCost,innerRun,innerBound⟩ := replace_prefix upper fresh upperClean upperMarked
    freshClean freshMarked terminal hi fh repair initial last reads budget body K upperSize repairedSize []
  obtain ⟨repairedClean,repairedMarked⟩ := replacePrefix_invariant upper upperClean upperMarked hi fh fresh freshClean freshMarked
  have repairedTerminal : repairedUpper.core = .leaf → isLeaf repairedUpper.tree = true := by
    intro empty
    have positive : repairedUpper.core.size = fresh.core.size+1+(cutRight upper hi fh).core.size := join_size _ _ _ _
    rw [empty,Impl.size_leaf] at positive
    omega
  obtain ⟨outerReads,outerCost,outerRun,outerBound⟩ := replace_suffix component repairedUpper clean marked
    repairedClean repairedMarked repairedTerminal lo fl (program hi false repair initial) (.marker .openOuter .start) .done
    innerReads innerCost innerRun K oldSize newSize outside
  exact ⟨outerReads,outerCost,outerRun,by omega⟩

end ChaCha.Paper20261030.BoundaryObservations.BoundaryRepairController
