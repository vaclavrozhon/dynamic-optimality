import TangoSquared.Paper20261030.ObservedNeighbors
import TangoSquared.Paper20261030.SourceProgramComposition

/-! A local program for both neighboring separators of a depth query.
It stores two candidate records and a depth counter, stops at the first
marked port, and walks back to its entry. It observes no payload interior.
The returned pair is exactly the existing `neighbors` specification. -/

namespace TangoSquared.Paper20261030.BoundaryObservations.NeighborController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary SourcePointer SourceLocalProgram

variable {α : Type*} {β : Nat → Type*}

def prefer {τ : Type*} (fresh old : Option τ) : Option τ :=
  match fresh with | none => old | some value => some value

def merge (old fresh : NeighborPair (β := β)) : NeighborPair (β := β) :=
  (prefer fresh.1 old.1,prefer fresh.2 old.2)

theorem merge_left (old fresh : NeighborPair (β := β)) (pivot : Sigma (Tagged β)) :
    merge (old.1,some pivot) fresh = merge old (fresh.1,some (fresh.2.getD pivot)) := by
  rcases old with ⟨lower,upper⟩
  rcases fresh with ⟨lo,hi⟩
  cases hi <;> rfl

theorem merge_right (old fresh : NeighborPair (β := β)) (pivot : Sigma (Tagged β)) :
    merge (some pivot,old.2) fresh = merge old (some (fresh.1.getD pivot),fresh.2) := by
  rcases old with ⟨lower,upper⟩
  rcases fresh with ⟨lo,hi⟩
  cases lo <;> rfl

theorem merge_empty (fresh : NeighborPair (β := β)) : merge (none,none) fresh = fresh := by
  rcases fresh with ⟨lo,hi⟩
  cases lo <;> cases hi <;> rfl

inductive State (β : Nat → Type*) where
  | search (depth : Nat) (candidates : NeighborPair (β := β))
  | down (depth : Nat) (left : Bool) (candidates : NeighborPair (β := β))
  | returning (depth : Nat) (candidates : NeighborPair (β := β))

def next (request depth : Nat) (candidates : NeighborPair (β := β)) (record : Record (β := β)) : State β :=
  if entry record then .returning depth candidates
  else if request ≤ record.2.1 then .down depth true (candidates.1,some record.2)
  else .down depth false (some record.2,candidates.2)

def program (request : Nat) : Program (State β) (Record (β := β))
  | .search depth candidates => .read (fun record _ => next request depth candidates record)
  | .down depth left candidates => .nav (if left then .left else .right) (.search (depth+1) candidates)
  | .returning 0 _ => .halt
  | .returning (depth+1) candidates => .nav .up (.returning depth candidates)

theorem query_prefix (request : Nat) (core : Impl Nat (Tagged β)) (clean : Clean core)
    (ports : Nat → Source α (Record (β := β))) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base+(recordTree core).size → entry (ports i).rootRecord = true)
    (depth : Nat) (candidates : NeighborPair (β := β)) (outside) :
    ∃ reads cost, Steps (program request) (.search depth candidates)
      ⟨GapSource.encode (recordTree core) ports base,outside⟩ (.returning depth (merge candidates (neighbors request core)))
      ⟨GapSource.encode (recordTree core) ports base,outside⟩ reads cost ∧ cost ≤ 3*height core+1 := by
  induction core generalizing base depth candidates outside with
  | leaf =>
    have atEntry := marked base le_rfl (by simp [recordTree,MTR.Tree.size])
    have read : Step (program request) (.search depth candidates) ⟨ports base,outside⟩
        (next request depth candidates (ports base).rootRecord) ⟨ports base,outside⟩ (some (ports base).rootRecord) := by
      apply Step.read (next := fun (record : Record (β := β)) (_ : Bool) => next request depth candidates record)
      rfl
    simp only [next,atEntry,ite_true] at read
    exact ⟨_,1,read.prefix,by simp [height]⟩
  | inner size key value left right ihl ihr =>
    have coreEntry : entry (size,⟨key,value⟩) = false := clean.1
    have read : Step (program request) (.search depth candidates)
        ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩
        (next request depth candidates (size,⟨key,value⟩))
        ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩ (some (size,⟨key,value⟩)) := by
      apply Step.read (next := fun (record : Record (β := β)) (_ : Bool) => next request depth candidates record)
      rfl
    by_cases direction : request ≤ key
    · have childMarked : ∀ i, base ≤ i → i ≤ base+(recordTree left).size → entry (ports i).rootRecord = true := by
        intro i lower upper
        exact marked i lower (by simp only [recordTree,MTR.Tree.size]; omega)
      obtain ⟨reads,cost,child,bound⟩ := ihl clean.2.1 base childMarked (depth+1) (candidates.1,some ⟨key,value⟩)
        (.left (size,⟨key,value⟩) (GapSource.encode (recordTree right) ports (base+(recordTree left).size+1))::outside)
      have result : merge (candidates.1,some ⟨key,value⟩) (neighbors request left) =
          merge candidates (neighbors request (.inner size key value left right)) := by
        simpa only [neighbors,direction,ite_true] using merge_left candidates (neighbors request left) ⟨key,value⟩
      rw [result] at child
      simp only [next,coreEntry,Bool.false_eq_true,ite_false,direction,ite_true] at read
      have down : Step (program request) (.down depth true (candidates.1,some ⟨key,value⟩))
          ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩
          (.search (depth+1) (candidates.1,some ⟨key,value⟩))
          ⟨GapSource.encode (recordTree left) ports base,
            .left (size,⟨key,value⟩) (GapSource.encode (recordTree right) ports (base+(recordTree left).size+1))::outside⟩ none := .nav rfl rfl
      have up : Step (program request) (.returning (depth+1) (merge candidates (neighbors request (.inner size key value left right))))
          ⟨GapSource.encode (recordTree left) ports base,
            .left (size,⟨key,value⟩) (GapSource.encode (recordTree right) ports (base+(recordTree left).size+1))::outside⟩
          (.returning depth (merge candidates (neighbors request (.inner size key value left right))))
          ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩ none := .nav rfl rfl
      exact ⟨_,_,((read.prefix.append down.prefix).append child).append up.prefix,by simp only [height]; omega⟩
    · have childMarked : ∀ i, base+(recordTree left).size+1 ≤ i →
          i ≤ base+(recordTree left).size+1+(recordTree right).size → entry (ports i).rootRecord = true := by
        intro i lower upper
        exact marked i (by omega) (by simp only [recordTree,MTR.Tree.size]; omega)
      obtain ⟨reads,cost,child,bound⟩ := ihr clean.2.2 (base+(recordTree left).size+1) childMarked
        (depth+1) (some ⟨key,value⟩,candidates.2)
        (.right (GapSource.encode (recordTree left) ports base) (size,⟨key,value⟩)::outside)
      have result : merge (some ⟨key,value⟩,candidates.2) (neighbors request right) =
          merge candidates (neighbors request (.inner size key value left right)) := by
        simpa only [neighbors,direction,ite_false] using merge_right candidates (neighbors request right) ⟨key,value⟩
      rw [result] at child
      simp only [next,coreEntry,Bool.false_eq_true,ite_false,direction] at read
      have down : Step (program request) (.down depth false (some ⟨key,value⟩,candidates.2))
          ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩
          (.search (depth+1) (some ⟨key,value⟩,candidates.2))
          ⟨GapSource.encode (recordTree right) ports (base+(recordTree left).size+1),
            .right (GapSource.encode (recordTree left) ports base) (size,⟨key,value⟩)::outside⟩ none := .nav rfl rfl
      have up : Step (program request) (.returning (depth+1) (merge candidates (neighbors request (.inner size key value left right))))
          ⟨GapSource.encode (recordTree right) ports (base+(recordTree left).size+1),
            .right (GapSource.encode (recordTree left) ports base) (size,⟨key,value⟩)::outside⟩
          (.returning depth (merge candidates (neighbors request (.inner size key value left right))))
          ⟨GapSource.encode (recordTree (.inner size key value left right)) ports base,outside⟩ none := .nav rfl rfl
      exact ⟨_,_,((read.prefix.append down.prefix).append child).append up.prefix,by simp only [height]; omega⟩

theorem query_component (request : Nat) (component : AuxiliaryComponent α Nat (Tagged β))
    (clean : Clean component.core) (marked : MarkedPorts component) (outside) :
    ∃ reads cost, Run (program request) (.search 0 (none,none)) ⟨component.tree,outside⟩
      (.returning 0 (neighbors request component.core)) ⟨component.tree,outside⟩ reads cost ∧
      cost ≤ 9*Nat.clog 2 (component.core.size+1)+1 := by
  obtain ⟨reads,cost,run,bound⟩ := query_prefix request component.core clean component.ports 0
    (fun i _ upper => marked i (by
      simpa only [Nat.zero_add,Metadata.recordTree_size_of_balanced component.core component.balanced] using upper))
    0 (none,none) outside
  rw [merge_empty] at run
  have heightBound := balanced_height_log component.balanced
  exact ⟨reads,cost,run.run rfl,by omega⟩

end TangoSquared.Paper20261030.BoundaryObservations.NeighborController
