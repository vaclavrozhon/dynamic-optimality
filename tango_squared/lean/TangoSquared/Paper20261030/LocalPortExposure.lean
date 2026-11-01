import TangoSquared.Paper20261030.LocalNeighborProgram
import TangoSquared.Paper20261030.AuxiliaryPortSearch

/-! Exposing a selected gap port without entering its payload or walking
back to the auxiliary root. The first read can ignore the root's entry
marker; every later read stops at an entry marker. Only the reached
separator, one direction bit, and finite control are used.
-/

namespace TangoSquared.Paper20261030.BoundaryObservations.PortExposureController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata SourcePointer SourceLocalProgram

variable {α : Type*} {β : Nat → Type*}

inductive State where
  | search (first : Bool)
  | down (right : Bool)
  | done

def next (request : Nat) (first : Bool) (record : Record (β := β)) (leaf : Bool) : State :=
  if (if first then leaf else entry record) then .done else .down (decide (record.2.1 < request))

def program (request : Nat) : Program State (Record (β := β))
  | .search first => .read (next request first)
  | .down right => .nav (if right then .right else .left) (.search false)
  | .done => .halt

theorem expose_core (request : Nat) (core : Impl Nat (Tagged β)) (balanced : core.Balanced) (clean : Clean core)
    (ports : Nat → Source α (Record (β := β))) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base+(recordTree core).size → entry (ports i).rootRecord = true)
    (outside : List (Frame α (Record (β := β)))) :
    ∃ targetContext reads cost,
      Run (program request) (.search false) ⟨GapSource.encode (recordTree core) ports base,outside⟩
        .done ⟨ports (base+gapIndex request core),targetContext⟩ reads cost ∧
      (Cursor.mk (ports (base+gapIndex request core)) targetContext).tree =
        (Cursor.mk (GapSource.encode (recordTree core) ports base) outside).tree ∧
      cost ≤ 2*height core+1 := by
  induction core generalizing base outside with
  | leaf =>
    have atEntry := marked base le_rfl (by simp [recordTree,MTR.Tree.size])
    have read : Step (program request) (.search false) ⟨ports base,outside⟩ .done ⟨ports base,outside⟩
        (some (ports base).rootRecord) := by
      have actual := Step.read (program := program request) (state := .search false) (next := next request false)
        (cursor := ⟨ports base,outside⟩) rfl
      simpa only [next,Bool.false_eq_true,if_false,atEntry,if_true] using actual
    exact ⟨outside,_,1,by simpa only [recordTree,GapSource.encode,gapIndex,Nat.add_zero] using read.prefix.run rfl,
      rfl,by simp [height]⟩
  | inner size key value left right ihl ihr =>
    have coreEntry : entry (size,⟨key,value⟩) = false := clean.1
    have read : Step (program request) (.search false)
        ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩
        (next request false (size,⟨key,value⟩) false)
        ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩
        (some (size,⟨key,value⟩)) := .read rfl
    by_cases direction : request ≤ key
    · have childMarked : ∀ i, base ≤ i → i ≤ base+(recordTree left).size → entry (ports i).rootRecord = true := by
        intro i lower upper
        exact marked i lower (by simp only [recordTree,MTR.Tree.size]; omega)
      obtain ⟨target,reads,cost,child,same,bounded⟩ := ihl balanced.left clean.2.1 base childMarked
        (.left (size,⟨key,value⟩) (GapSource.encode (recordTree right) ports (base+(recordTree left).size+1))::outside)
      simp only [next,Bool.false_eq_true,if_false,coreEntry,_root_.not_lt.mpr direction,decide_false] at read
      have down : Step (program request) (.down false)
          ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩ (.search false)
          ⟨GapSource.encode (recordTree left) ports base,
            .left (size,⟨key,value⟩) (GapSource.encode (recordTree right) ports (base+(recordTree left).size+1))::outside⟩ none := .nav rfl rfl
      refine ⟨target,(size,⟨key,value⟩)::reads,cost+2,?_,?_,by simp only [height]; omega⟩
      · simpa only [gapIndex,if_pos direction,Option.toList_none,Option.toList_some,List.nil_append,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using read.prefix.then_run (.next down child)
      · simpa only [gapIndex,if_pos direction,Cursor.tree,plug,recordTree,GapSource.encode] using same
    · have childMarked : ∀ i, base+(recordTree left).size+1 ≤ i →
          i ≤ base+(recordTree left).size+1+(recordTree right).size → entry (ports i).rootRecord = true := by
        intro i lower upper
        exact marked i (by omega) (by simp only [recordTree,MTR.Tree.size]; omega)
      obtain ⟨target,reads,cost,child,same,bounded⟩ := ihr balanced.right clean.2.2 (base+(recordTree left).size+1) childMarked
        (.right (GapSource.encode (recordTree left) ports base) (size,⟨key,value⟩)::outside)
      simp only [next,Bool.false_eq_true,if_false,coreEntry,lt_of_not_ge direction,decide_true] at read
      have down : Step (program request) (.down true)
          ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩ (.search false)
          ⟨GapSource.encode (recordTree right) ports (base+(recordTree left).size+1),
            .right (GapSource.encode (recordTree left) ports base) (size,⟨key,value⟩)::outside⟩ none := .nav rfl rfl
      refine ⟨target,(size,⟨key,value⟩)::reads,cost+2,?_,?_,by simp only [height]; omega⟩
      · simpa only [gapIndex,if_neg direction,recordTree_size_of_balanced left balanced.left,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Option.toList_none,Option.toList_some,List.nil_append,List.singleton_append] using read.prefix.then_run (.next down child)
      · simpa only [gapIndex,if_neg direction,recordTree_size_of_balanced left balanced.left,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Option.toList_none,Option.toList_some,List.nil_append,List.singleton_append,Cursor.tree,plug,recordTree,GapSource.encode] using same

end TangoSquared.Paper20261030.BoundaryObservations.PortExposureController
