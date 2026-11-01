import TangoSquared.Paper20261030.ObservedCutBoundaries

/-!
# Actual observed queries on a closed auxiliary component

Open its marked root, perform one or three root-to-port-and-back searches,
then close it again. Each query is decoded from its own actual read word.
The three-query version permits the latter two search labels to be the
interval endpoints of the departure decoded from the first query.
-/

namespace TangoSquared.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent SourcePointer

variable {α : Type*} {β : Nat → Type*}

theorem query_closed (d : Nat) (c : AuxiliaryComponent α Nat (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (ancestors) :
    ∃ openReads queryReads closeReads openCost queryCost closeCost,
      SourcePointer.Trace ⟨closed c,ancestors⟩ openReads ⟨c.tree,ancestors⟩ openCost ∧
      SourcePointer.Trace ⟨c.tree,ancestors⟩ queryReads ⟨c.tree,ancestors⟩ queryCost ∧
      SourcePointer.Trace ⟨c.tree,ancestors⟩ closeReads ⟨closed c,ancestors⟩ closeCost ∧
      parseNeighbors d queryReads = some (neighbors d c.core,[]) ∧
      openCost + queryCost + closeCost ≤ 9 * Nat.clog 2 (c.core.size + 1) + 5 := by
  obtain ⟨ro,co,tOpen,bo⟩ := open_charged c hc hp ancestors
  obtain ⟨rq,cq,tq,pq,bq⟩ := observeNeighbors_component d c hc hp ancestors
  obtain ⟨rc,cc,tc,bc⟩ := close_charged c ancestors
  exact ⟨ro,rq,rc,co,cq,cc,tOpen,tq,tc,by simpa only [List.append_nil] using pq [],by omega⟩

theorem query_closed_charged (d : Nat) (c : AuxiliaryComponent α Nat (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) :
    SourcePointer.Rearranges (closed c) (closed c) (9 * Nat.clog 2 (c.core.size + 1) + 5) := by
  intro ancestors
  obtain ⟨ro,rq,rc,co,cq,cc,tOpen,tq,tc,parsed,bound⟩ := query_closed d c hc hp ancestors
  exact ⟨_,_,(tOpen.append tq).append tc,bound⟩

theorem query_three (d lo hi : Nat) (c : AuxiliaryComponent α Nat (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (ancestors) :
    ∃ openReads firstReads lowerReads upperReads closeReads openCost firstCost lowerCost upperCost closeCost,
      SourcePointer.Trace ⟨closed c,ancestors⟩ openReads ⟨c.tree,ancestors⟩ openCost ∧
      SourcePointer.Trace ⟨c.tree,ancestors⟩ firstReads ⟨c.tree,ancestors⟩ firstCost ∧
      SourcePointer.Trace ⟨c.tree,ancestors⟩ lowerReads ⟨c.tree,ancestors⟩ lowerCost ∧
      SourcePointer.Trace ⟨c.tree,ancestors⟩ upperReads ⟨c.tree,ancestors⟩ upperCost ∧
      SourcePointer.Trace ⟨c.tree,ancestors⟩ closeReads ⟨closed c,ancestors⟩ closeCost ∧
      parseNeighbors d firstReads = some (neighbors d c.core,[]) ∧
      parseNeighbors lo lowerReads = some (neighbors lo c.core,[]) ∧
      parseNeighbors hi upperReads = some (neighbors hi c.core,[]) ∧
      openCost + firstCost + lowerCost + upperCost + closeCost ≤ 27 * Nat.clog 2 (c.core.size + 1) + 7 := by
  obtain ⟨ro,co,tOpen,bo⟩ := open_charged c hc hp ancestors
  obtain ⟨rf,cf,tf,pf,bf⟩ := observeNeighbors_component d c hc hp ancestors
  obtain ⟨rl,cl,tl,pl,bl⟩ := observeNeighbors_component lo c hc hp ancestors
  obtain ⟨ru,cu,tu,pu,bu⟩ := observeNeighbors_component hi c hc hp ancestors
  obtain ⟨rc,cc,tc,bc⟩ := close_charged c ancestors
  refine ⟨ro,rf,rl,ru,rc,co,cf,cl,cu,cc,tOpen,tf,tl,tu,tc,?_,?_,?_,by omega⟩
  · simpa only [List.append_nil] using pf []
  · simpa only [List.append_nil] using pl []
  · simpa only [List.append_nil] using pu []

theorem query_three_charged (d lo hi : Nat) (c : AuxiliaryComponent α Nat (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) :
    SourcePointer.Rearranges (closed c) (closed c) (27 * Nat.clog 2 (c.core.size + 1) + 7) := by
  intro ancestors
  obtain ⟨ro,rf,rl,ru,rc,co,cf,cl,cu,cc,tOpen,tf,tl,tu,tc,pf,pl,pu,bound⟩ := query_three d lo hi c hc hp ancestors
  exact ⟨_,_,(((tOpen.append tf).append tl).append tu).append tc,bound⟩

end TangoSquared.Paper20261030.BoundaryObservations
