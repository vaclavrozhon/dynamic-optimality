import ChaCha.Paper20261030.ComponentMarkers

/-!
# Reading both neighboring separators on one actual search path

The lower neighbor is the greatest separator below the query; the upper
neighbor is the least separator at least the query. `neighbors` specifies
the pair selected by binary search. The decoder `parseNeighbors` recovers
that pair using only the actual read word, stopping at the first marked
port. No hanging subtree is entered. The exact extremal characterization
of the result in an ordered core is proved separately.
-/

namespace ChaCha.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata SourcePointer

variable {α : Type*} {β : Nat → Type*}

abbrev NeighborPair := Option (Sigma (Tagged β)) × Option (Sigma (Tagged β))

def neighbors (d : Nat) : Impl Nat (Tagged β) → NeighborPair (β := β)
  | .leaf => (none,none)
  | .inner _ key value l r =>
      if d ≤ key then
        let next := neighbors d l
        (next.1,some (next.2.getD ⟨key,value⟩))
      else
        let next := neighbors d r
        (some (next.1.getD ⟨key,value⟩),next.2)

def parseNeighbors (d : Nat) : List (Record (β := β)) →
    Option (NeighborPair (β := β) × List (Record (β := β)))
  | [] => none
  | record :: records =>
      if entry record then some ((none,none),records)
      else do
        let (next,rest) ← parseNeighbors d records
        if d ≤ record.2.1 then return ((next.1,some (next.2.getD record.2)),rest)
        else return ((some (next.1.getD record.2),next.2),rest)

theorem observeNeighbors (d : Nat) (t : Impl Nat (Tagged β)) (clean : Clean t)
    (ports : Nat → Source α (Record (β := β))) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base + (recordTree t).size → entry (ports i).rootRecord = true)
    (ancestors : List (SourcePointer.Frame α (Record (β := β)))) :
    ∃ (reads : List (Record (β := β))) (cost : Nat),
      SourcePointer.Trace ⟨GapSource.encode (recordTree t) ports base,ancestors⟩ reads
        ⟨GapSource.encode (recordTree t) ports base,ancestors⟩ cost ∧
      (∀ tail, parseNeighbors d (reads ++ tail) = some (neighbors d t,tail)) ∧
      cost ≤ 3 * height t + 1 := by
  induction t generalizing base ancestors with
  | leaf =>
    have hm := marked base le_rfl (by simp [recordTree,MTR.Tree.size])
    exact ⟨[(ports base).rootRecord],1,.read (.nil _),
      fun tail => by simp only [List.singleton_append,parseNeighbors,hm,if_true,neighbors],by simp [height]⟩
  | inner cached key value l r ihl ihr =>
    have he : entry (cached,⟨key,value⟩) = false := clean.1
    by_cases direction : d ≤ key
    · have hl : ∀ i, base ≤ i → i ≤ base + (recordTree l).size → entry (ports i).rootRecord = true := by
        intro i hlo hhi
        exact marked i hlo (by simp only [recordTree,MTR.Tree.size]; omega)
      obtain ⟨reads,cost,trace,parsed,bound⟩ := ihl clean.2.1 base hl
        (.left (cached,⟨key,value⟩)
          (GapSource.encode (recordTree r) ports (base + (recordTree l).size + 1)) :: ancestors)
      have full := SourcePointer.Trace.read (.step (.left _ _ _ _)
        (trace.append (.step (.upLeft _ _ _ _) (.nil _))))
      refine ⟨(cached,⟨key,value⟩) :: reads,cost + 3,?_,?_,?_⟩
      · simpa only [recordTree,GapSource.encode,Source.rootRecord,List.append_nil,Nat.add_assoc] using full
      · intro tail
        simp [parseNeighbors,he,parsed,neighbors,direction]
      · simp only [height]
        omega
    · have hr : ∀ i, base + (recordTree l).size + 1 ≤ i →
          i ≤ base + (recordTree l).size + 1 + (recordTree r).size → entry (ports i).rootRecord = true := by
        intro i hlo hhi
        exact marked i (by omega) (by simp only [recordTree,MTR.Tree.size]; omega)
      obtain ⟨reads,cost,trace,parsed,bound⟩ := ihr clean.2.2
        (base + (recordTree l).size + 1) hr
        (.right (GapSource.encode (recordTree l) ports base) (cached,⟨key,value⟩) :: ancestors)
      have full := SourcePointer.Trace.read (.step (.right _ _ _ _)
        (trace.append (.step (.upRight _ _ _ _) (.nil _))))
      refine ⟨(cached,⟨key,value⟩) :: reads,cost + 3,?_,?_,?_⟩
      · simpa only [recordTree,GapSource.encode,Source.rootRecord,List.append_nil,Nat.add_assoc] using full
      · intro tail
        simp [parseNeighbors,he,parsed,neighbors,direction]
      · simp only [height]
        omega

theorem observeNeighbors_component (d : Nat) (c : AuxiliaryComponent α Nat (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (ancestors) :
    ∃ reads cost,
      SourcePointer.Trace ⟨c.tree,ancestors⟩ reads ⟨c.tree,ancestors⟩ cost ∧
      (∀ tail, parseNeighbors d (reads ++ tail) = some (neighbors d c.core,tail)) ∧
      cost ≤ 9 * Nat.clog 2 (c.core.size + 1) + 1 := by
  obtain ⟨reads,cost,trace,parsed,bound⟩ := observeNeighbors d c.core hc c.ports 0
    (fun i _ hi => hp i (by simpa only [Nat.zero_add,recordTree_size_of_balanced c.core c.balanced] using hi))
    ancestors
  exact ⟨reads,cost,trace,parsed,by have := balanced_height_log c.balanced; omega⟩

end ChaCha.Paper20261030.BoundaryObservations
