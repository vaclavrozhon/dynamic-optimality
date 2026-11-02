import ChaCha.Paper20261030.SourceProgramObservation
import ChaCha.Paper20261030.LocalNeighborProgram
import ChaCha.Paper20261030.TerminalRank

/-! The neighbor query actually reads the selected gap port. When the
maintained terminal is the request, this is the requested physical leaf.
The witness is a prefix of the same local program used by the access loop. -/

namespace ChaCha.Paper20261030.BoundaryObservations.NeighborController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata SourcePointer SourceLocalProgram

variable {α : Type*} {β : Nat → Type*}

theorem reads_port (request : Nat) (core : Impl Nat (Tagged β)) (balanced : core.Balanced) (clean : Clean core)
    (ports : Nat → Source α (Record (β := β))) (base : Nat) (target : α) (record : Record (β := β))
    (terminal : ports (base+gapIndex request core) = .leaf target record)
    (depth : Nat) (candidates : NeighborPair (β := β)) (outside) :
    ReachesLeafRead (program request) (.search depth candidates)
      ⟨GapSource.encode (recordTree core) ports base,outside⟩ target := by
  induction core generalizing base depth candidates outside with
  | leaf =>
    refine ⟨.search depth candidates,⟨ports base,outside⟩,record,[],0,
      (fun record _ => next request depth candidates record),.nil _ _,?_,rfl⟩
    simpa only [gapIndex,Nat.add_zero] using terminal
  | inner size key value left right ihl ihr =>
    have coreEntry : entry (size,⟨key,value⟩) = false := clean.1
    have read : Step (program request) (.search depth candidates)
        ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩
        (next request depth candidates (size,⟨key,value⟩))
        ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩ (some (size,⟨key,value⟩)) := by
      apply Step.read (next := fun (record : Record (β := β)) (_ : Bool) => next request depth candidates record)
      rfl
    by_cases direction : request ≤ key
    · have childTerminal : ports (base+gapIndex request left) = .leaf target record := by
        simpa only [gapIndex,if_pos direction] using terminal
      have reached := ihl balanced.left clean.2.1 base childTerminal (depth+1) (candidates.1,some ⟨key,value⟩)
        (.left (size,⟨key,value⟩) (GapSource.encode (recordTree right) ports (base+(recordTree left).size+1))::outside)
      simp only [next,coreEntry,Bool.false_eq_true,ite_false,direction,ite_true] at read
      have down : Step (program request) (.down depth true (candidates.1,some ⟨key,value⟩))
          ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩
          (.search (depth+1) (candidates.1,some ⟨key,value⟩))
          ⟨GapSource.encode (recordTree left) ports base,
            .left (size,⟨key,value⟩) (GapSource.encode (recordTree right) ports (base+(recordTree left).size+1))::outside⟩ none := .nav rfl rfl
      exact reached.prepend (read.prefix.append down.prefix)
    · have childTerminal : ports (base+(recordTree left).size+1+gapIndex request right) = .leaf target record := by
        simpa only [gapIndex,if_neg direction,recordTree_size_of_balanced left balanced.left,Nat.add_assoc] using terminal
      have reached := ihr balanced.right clean.2.2 (base+(recordTree left).size+1) childTerminal
        (depth+1) (some ⟨key,value⟩,candidates.2)
        (.right (GapSource.encode (recordTree left) ports base) (size,⟨key,value⟩)::outside)
      simp only [next,coreEntry,Bool.false_eq_true,ite_false,direction] at read
      have down : Step (program request) (.down depth false (some ⟨key,value⟩,candidates.2))
          ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩
          (.search (depth+1) (some ⟨key,value⟩,candidates.2))
          ⟨GapSource.encode (recordTree right) ports (base+(recordTree left).size+1),
            .right (GapSource.encode (recordTree left) ports base) (size,⟨key,value⟩)::outside⟩ none := .nav rfl rfl
      exact reached.prepend (read.prefix.append down.prefix)

theorem terminal_read {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = request)
    (component : AuxiliaryComponent Nat Nat (Tagged SecondaryDecomposition.Payload))
    (represented : PathDecomposition.Represents SecondaryDecomposition.followsRight
      (SecondaryDecomposition.source reference preferences) component) (outside) :
    ReachesLeafRead (program request) (.search 0 (none,none)) ⟨component.tree,outside⟩ request := by
  apply reads_port request component.core component.balanced represented.invariant.1 component.ports 0 request
    (0,⟨request,((⟨request,request,request⟩,false),true)⟩)
  simpa only [Nat.zero_add,SecondaryDecomposition.terminalLeaf] using
    SecondaryDecomposition.represented_terminal_port reference preferences request terminal component represented

end ChaCha.Paper20261030.BoundaryObservations.NeighborController
