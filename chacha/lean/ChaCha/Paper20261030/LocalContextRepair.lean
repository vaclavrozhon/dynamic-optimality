import ChaCha.Paper20261030.LocalIntervalProgram
import ChaCha.Paper20261030.LocalClosedNeighborProgram
import ChaCha.Paper20261030.ContextRepair

/-! Lifting one fixed local repair program through a preferred context.
The wrapper receives the two boundary keys, executes the same local
subprogram on the exposed component, and restores the surrounding
representation. Its four branches match the existing context lemmas. -/

namespace ChaCha.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations SourceLocalProgram

variable {α ρ σ : Type*} {right : Record (β := fun _ => ρ) → Bool}

theorem repair_context_controller (oldSource newSource : Source α (Record (β := fun _ => ρ)))
    (sub component : AuxiliaryComponent α Nat (fun _ => ρ×Bool)) (frames : List (ContextFrame right))
    (representedSub : Represents right oldSource sub)
    (same : Equivalent component (PreferredContext.wrap sub frames)) (ordered : component.core.Ordered)
    (repair : Program σ (Record (β := fun _ => ρ))) (initial : σ) (repairCost : Nat)
    (correct : ∀ actual : AuxiliaryComponent α Nat (fun _ => ρ×Bool), Represents right oldSource actual →
      ∃ fresh : AuxiliaryComponent α Nat (fun _ => ρ×Bool), Represents right newSource fresh ∧
        ∃ last reads cost, Run repair initial ⟨closed actual,[]⟩ last ⟨closed fresh,[]⟩ reads cost ∧ cost ≤ repairCost)
    (K : Nat) (oldSize : component.core.size ≤ K)
    (newSize : (PreferredContext.plug newSource frames).shape.height ≤ K) (outside) :
    let lower := (PreferredContext.before frames).getLast?.map (fun entry => entry.1)
    let upper := (PreferredContext.after frames).head?.map (fun entry => entry.1)
    ∃ out : AuxiliaryComponent α Nat (fun _ => ρ×Bool),
      Represents right (PreferredContext.plug newSource frames) out ∧
      ∃ reads cost, Run (IntervalRepairController.program lower upper repair initial)
        (IntervalRepairController.initial lower upper repair initial) ⟨closed component,outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ repairCost+88620*Nat.clog 2 (K+1)+636 := by
  dsimp only
  have represented := (PreferredContext.represents frames representedSub).equivalent same
  obtain ⟨clean,marked⟩ := represented.invariant
  cases last : (PreferredContext.before frames).getLast? with
  | none =>
    have beforeEmpty := List.getLast?_eq_none_iff.mp last
    cases after : PreferredContext.after frames with
    | nil =>
      have equivalent := same.trans (empty_context sub frames beforeEmpty after).symm
      obtain ⟨fresh,freshRep,final,reads,cost,body,bound⟩ := correct component (representedSub.equivalent equivalent)
      have output := (PreferredContext.represents frames freshRep).equivalent (empty_context fresh frames beforeEmpty after)
      have complete := IntervalRepairController.bare_run repair initial final _ _ reads cost (body.extend outside)
      refine ⟨fresh,output,reads,cost,?_,by omega⟩
      simpa only [last,after,List.head?_nil,Option.map_none,SourcePointer.Cursor.extend,List.nil_append] using complete
    | cons hi tail =>
      obtain ⟨found,equivalent,rejoin⟩ := prefix_context component sub frames same ordered tail hi beforeEmpty after
      obtain ⟨fresh,freshRep,final,reads,cost,body,bound⟩ := correct (cutLeft component hi.1 found) (representedSub.equivalent equivalent)
      have output := (PreferredContext.represents frames freshRep).equivalent (rejoin fresh)
      obtain ⟨freshClean,freshMarked⟩ := freshRep.invariant
      obtain ⟨observed,total,run,totalBound⟩ := BoundaryRepairController.replace_prefix component fresh clean marked
        freshClean freshMarked (ClosedNeighborController.represented_terminal freshRep) hi.1 found repair initial final
        reads cost body K oldSize (output.size_height.trans newSize) outside
      have complete := IntervalRepairController.prefix_run hi.1 repair initial _ _ observed total run
      refine ⟨_,output,observed,total,?_,by omega⟩
      simpa only [last,after,List.head?_cons,Option.map_none,Option.map_some] using complete
  | some lo =>
    obtain ⟨before,beforeWord⟩ := List.getLast?_eq_some_iff.mp last
    cases after : PreferredContext.after frames with
    | nil =>
      obtain ⟨found,equivalent,rejoin⟩ := suffix_context component sub frames same ordered before lo beforeWord after
      obtain ⟨fresh,freshRep,final,reads,cost,body,bound⟩ := correct (cutRight component lo.1 found) (representedSub.equivalent equivalent)
      have output := (PreferredContext.represents frames freshRep).equivalent (rejoin fresh)
      obtain ⟨freshClean,freshMarked⟩ := freshRep.invariant
      obtain ⟨observed,total,run,totalBound⟩ := BoundaryRepairController.replace_suffix component fresh clean marked
        freshClean freshMarked (ClosedNeighborController.represented_terminal freshRep) lo.1 found repair initial final
        reads cost body K oldSize (output.size_height.trans newSize) outside
      have complete := IntervalRepairController.suffix_run lo.1 repair initial _ _ observed total run
      refine ⟨_,output,observed,total,?_,by omega⟩
      simpa only [last,after,List.head?_nil,Option.map_none,Option.map_some] using complete
    | cons hi tail =>
      obtain ⟨fl,fh,equivalent,rejoin⟩ := middle_context component sub frames same ordered before tail lo hi beforeWord after
      obtain ⟨fresh,freshRep,final,reads,cost,body,bound⟩ := correct (middle component lo.1 fl hi.1 fh) (representedSub.equivalent equivalent)
      have output := (PreferredContext.represents frames freshRep).equivalent (rejoin fresh)
      obtain ⟨freshClean,freshMarked⟩ := freshRep.invariant
      obtain ⟨observed,total,run,totalBound⟩ := BoundaryRepairController.replace_middle component fresh clean marked
        freshClean freshMarked (ClosedNeighborController.represented_terminal freshRep) lo.1 fl hi.1 fh repair initial final
        reads cost body K oldSize (output.size_height.trans newSize) outside
      have complete := IntervalRepairController.middle_run lo.1 hi.1 repair initial _ _ observed total run
      refine ⟨_,output,observed,total,?_,by omega⟩
      simpa only [last,after,List.head?_cons,Option.map_some] using complete

end ChaCha.Paper20261030.PathDecomposition
