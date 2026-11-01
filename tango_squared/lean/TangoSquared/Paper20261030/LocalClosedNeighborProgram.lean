import TangoSquared.Paper20261030.LocalNeighborProgram
import TangoSquared.Paper20261030.PathDecomposition

/-! Local neighbor queries on closed represented components. A physical
leaf is a terminal component. Otherwise the program opens the reached
root marker, runs the verified search, and restores the marker. The
terminal test is proved from the maintained representation invariant. -/

namespace TangoSquared.Paper20261030.BoundaryObservations.ClosedNeighborController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourcePointer SourceLocalProgram

variable {α : Type*} {β : Nat → Type*}

inductive State (β : Nat → Type*) where
  | start
  | openWrite (record : Record (β := β))
  | querying (state : NeighborController.State β)
  | closeRead (result : NeighborPair (β := β))
  | closeWrite (result : NeighborPair (β := β)) (record : Record (β := β))
  | done (result : NeighborPair (β := β))

def querying : NeighborController.State β → State β
  | .returning 0 result => .closeRead result
  | state => .querying state

def program (request : Nat) : Program (State β) (Record (β := β))
  | .start => .read (fun record leaf => if leaf then .done (none,none) else .openWrite (tag false record))
  | .openWrite record => .write record (.querying (.search 0 (none,none)))
  | .querying state => (NeighborController.program request state).mapState querying
  | .closeRead result => .read (fun record _ => .closeWrite result (tag true record))
  | .closeWrite result record => .write record (.done result)
  | .done _ => .halt

theorem querying_code (request : Nat) (state : NeighborController.State β)
    (active : NeighborController.program request state ≠ .halt) :
    program request (querying state) = (NeighborController.program request state).mapState querying := by
  cases state with
  | search | down => rfl
  | returning depth result => cases depth with
    | zero => exact False.elim (active rfl)
    | succ => rfl

theorem initial_read (request : Nat) (source : Source α (Record (β := β))) (outside) :
    Step (program request) .start ⟨source,outside⟩
      (if isLeaf source then .done (none,none) else .openWrite (tag false source.rootRecord))
      ⟨source,outside⟩ (some source.rootRecord) := by
  apply Step.read (next := fun record leaf => if leaf then State.done (none,none) else .openWrite (tag false record))
  rfl

theorem close_prefix (request : Nat) (result : NeighborPair (β := β))
    (source : Source α (Record (β := β))) (outside) :
    Steps (program request) (.closeRead result) ⟨source,outside⟩ (.done result)
      ⟨source.setRoot (tag true source.rootRecord),outside⟩ [source.rootRecord] 2 := by
  have read : Step (program request) (.closeRead result) ⟨source,outside⟩
      (.closeWrite result (tag true source.rootRecord)) ⟨source,outside⟩ (some source.rootRecord) := by
    apply Step.read (next := fun record _ => State.closeWrite result (tag true record)); rfl
  have write : Step (program request) (.closeWrite result (tag true source.rootRecord))
      ⟨source,outside⟩ (.done result) ⟨source.setRoot (tag true source.rootRecord),outside⟩ none := .write rfl
  exact .next read (.next write (.nil _ _))

theorem isLeaf_setRoot (source : Source α (Record (β := β))) (record : Record (β := β)) :
    isLeaf (source.setRoot record) = isLeaf source := by cases source <;> rfl

theorem open_root (component : AuxiliaryComponent α Nat (Tagged β)) (clean : Clean component.core)
    (nonempty : component.core ≠ .leaf) :
    (closed component).setRoot (tag false (closed component).rootRecord) = component.tree := by
  have bit := open_entry component clean nonempty
  have unchanged : tag false component.tree.rootRecord = component.tree.rootRecord := by rw [← bit,tag_same]
  unfold closed
  cases shape : component.tree <;>
    simpa only [shape,Source.setRoot,Source.rootRecord,tag_tag] using
      congrArg (fun record => component.tree.setRoot record) unchanged

theorem query_component (request : Nat) (component : AuxiliaryComponent α Nat (Tagged β))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (terminal : component.core = .leaf → isLeaf component.tree = true) (outside) :
    ∃ reads cost, Run (program request) .start ⟨closed component,outside⟩
      (.done (neighbors request component.core)) ⟨closed component,outside⟩ reads cost ∧
      cost ≤ 9*Nat.clog 2 (component.core.size+1)+5 := by
  by_cases empty : component.core = .leaf
  · have physicalLeaf : isLeaf (closed component) = true := by
      rw [closed,isLeaf_setRoot]
      exact terminal empty
    have read := initial_read request (closed component) outside
    simp only [physicalLeaf,ite_true] at read
    refine ⟨[(closed component).rootRecord],1,?_,by omega⟩
    simpa only [empty,neighbors,Option.toList_some] using read.prefix.run (by rfl)
  · have physicalFork : isLeaf (closed component) = false := by
      rw [closed,isLeaf_setRoot]
      cases shape : component.core with
      | leaf => exact False.elim (empty shape)
      | inner => simp only [AuxiliaryComponent.tree,shape,recordTree,GapSource.encode,isLeaf]
    have read := initial_read request (closed component) outside
    simp only [physicalFork,Bool.false_eq_true,ite_false] at read
    have write : Step (program request) (.openWrite (tag false (closed component).rootRecord))
        ⟨closed component,outside⟩ (.querying (.search 0 (none,none))) ⟨component.tree,outside⟩ none := by
      rw [← open_root component clean empty]
      apply SourceLocalProgram.Step.write
      rfl
    obtain ⟨queryReads,queryCost,queryRun,queryBound⟩ := NeighborController.query_component request component clean marked outside
    have queried := queryRun.map_prefix querying (querying_code request)
    have final := close_prefix request (neighbors request component.core) component.tree outside
    have complete := ((read.prefix.append write.prefix).append queried).append final
    exact ⟨_,_,complete.run rfl,by omega⟩

theorem represented_terminal {right : Record (β := β) → Bool} {reference : Source α (Record (β := β))}
    {component : AuxiliaryComponent α Nat (Tagged β)}
    (represented : PathDecomposition.Represents right reference component) (empty : component.core = .leaf) :
    isLeaf component.tree = true := by
  cases represented with
  | leaf marked same =>
    have port := same.ports 0 (Nat.zero_le _)
    simp only [AuxiliaryComponent.tree,empty,recordTree,GapSource.encode]
    rw [port]
    rfl
  | left direction clean childLeft childRight same =>
    have size := same.size
    rw [empty,Impl.size_leaf,append_size] at size
    omega
  | right direction clean childLeft childRight same =>
    have size := same.size
    rw [empty,Impl.size_leaf,prepend_size] at size
    omega

theorem query_represented (request : Nat) {right : Record (β := β) → Bool} {reference : Source α (Record (β := β))}
    (component : AuxiliaryComponent α Nat (Tagged β))
    (represented : PathDecomposition.Represents right reference component) (outside) :
    ∃ reads cost, Run (program request) .start ⟨closed component,outside⟩
      (.done (neighbors request component.core)) ⟨closed component,outside⟩ reads cost ∧
      cost ≤ 9*Nat.clog 2 (component.core.size+1)+5 :=
  query_component request component represented.invariant.1 represented.invariant.2 (represented_terminal represented) outside

end TangoSquared.Paper20261030.BoundaryObservations.ClosedNeighborController
