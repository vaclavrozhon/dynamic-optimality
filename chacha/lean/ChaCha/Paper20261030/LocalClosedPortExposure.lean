import ChaCha.Paper20261030.LocalPortExposure
import ChaCha.Paper20261030.LocalClosedNeighborLeafRead

/-! Endpoint exposure in a closed secondary auxiliary. The root marker
is left intact: the initial read ignores that marker, while subsequent
reads stop at marked gap ports. No metadata is written and no payload
interior is traversed.
-/

namespace ChaCha.Paper20261030.BoundaryObservations.PortExposureController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata SourcePointer SourceLocalProgram

variable {α : Type*} {β : Nat → Type*}

theorem expose_fork (request key : Nat) (left right : Impl Nat (Tagged β))
    (balancedLeft : left.Balanced) (balancedRight : right.Balanced) (cleanLeft : Clean left) (cleanRight : Clean right)
    (ports : Nat → Source α (Record (β := β))) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base+left.size+right.size+1 → entry (ports i).rootRecord = true)
    (record : Record (β := β)) (sameKey : record.2.1 = key) (outside : List (Frame α (Record (β := β)))) :
    ∃ targetContext reads cost,
      Run (program request) (.search true)
        ⟨.fork record (GapSource.encode (recordTree left) ports base)
          (GapSource.encode (recordTree right) ports (base+left.size+1)),outside⟩ .done
        ⟨ports (if request ≤ key then base+gapIndex request left else base+left.size+1+gapIndex request right),targetContext⟩ reads cost ∧
      (Cursor.mk (ports (if request ≤ key then base+gapIndex request left else base+left.size+1+gapIndex request right)) targetContext).tree =
        (Cursor.mk (.fork record (GapSource.encode (recordTree left) ports base)
          (GapSource.encode (recordTree right) ports (base+left.size+1))) outside).tree ∧
      cost ≤ 2*(max (height left) (height right)+1)+1 := by
  have read : Step (program request) (.search true)
      ⟨.fork record (GapSource.encode (recordTree left) ports base)
        (GapSource.encode (recordTree right) ports (base+left.size+1)),outside⟩
      (.down (decide (key < request)))
      ⟨.fork record (GapSource.encode (recordTree left) ports base)
        (GapSource.encode (recordTree right) ports (base+left.size+1)),outside⟩ (some record) := by
    have actual := Step.read (program := program request) (state := .search true) (next := next request true)
      (cursor := ⟨.fork record (GapSource.encode (recordTree left) ports base)
        (GapSource.encode (recordTree right) ports (base+left.size+1)),outside⟩) rfl
    simpa only [next,if_true,SourceLocalProgram.isLeaf,Source.rootRecord,Bool.false_eq_true,if_false,sameKey] using actual
  by_cases direction : request ≤ key
  · have childMarked : ∀ i, base ≤ i → i ≤ base+(recordTree left).size → entry (ports i).rootRecord = true := by
      intro i lower upper
      rw [recordTree_size_of_balanced left balancedLeft] at upper
      exact marked i lower (by omega)
    obtain ⟨target,reads,cost,child,same,bounded⟩ := expose_core request left balancedLeft cleanLeft ports base childMarked
      (.left record (GapSource.encode (recordTree right) ports (base+left.size+1))::outside)
    simp only [_root_.not_lt.mpr direction,decide_false] at read
    have down : Step (program request) (.down false)
        ⟨.fork record (GapSource.encode (recordTree left) ports base)
          (GapSource.encode (recordTree right) ports (base+left.size+1)),outside⟩ (.search false)
        ⟨GapSource.encode (recordTree left) ports base,
          .left record (GapSource.encode (recordTree right) ports (base+left.size+1))::outside⟩ none := .nav rfl rfl
    refine ⟨target,record::reads,cost+2,?_,?_,by omega⟩
    · simpa only [if_pos direction,Option.toList_none,Option.toList_some,List.nil_append,List.singleton_append,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using read.prefix.then_run (.next down child)
    · simpa only [if_pos direction,Cursor.tree,plug] using same
  · have childMarked : ∀ i, base+left.size+1 ≤ i →
        i ≤ base+left.size+1+(recordTree right).size → entry (ports i).rootRecord = true := by
      intro i lower upper
      rw [recordTree_size_of_balanced right balancedRight] at upper
      exact marked i (by omega) (by omega)
    obtain ⟨target,reads,cost,child,same,bounded⟩ := expose_core request right balancedRight cleanRight ports (base+left.size+1) childMarked
      (.right (GapSource.encode (recordTree left) ports base) record::outside)
    simp only [lt_of_not_ge direction,decide_true] at read
    have down : Step (program request) (.down true)
        ⟨.fork record (GapSource.encode (recordTree left) ports base)
          (GapSource.encode (recordTree right) ports (base+left.size+1)),outside⟩ (.search false)
        ⟨GapSource.encode (recordTree right) ports (base+left.size+1),
          .right (GapSource.encode (recordTree left) ports base) record::outside⟩ none := .nav rfl rfl
    refine ⟨target,record::reads,cost+2,?_,?_,by omega⟩
    · simpa only [if_neg direction,Option.toList_none,Option.toList_some,List.nil_append,List.singleton_append,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using read.prefix.then_run (.next down child)
    · simpa only [if_neg direction,Cursor.tree,plug] using same

end ChaCha.Paper20261030.BoundaryObservations.PortExposureController
