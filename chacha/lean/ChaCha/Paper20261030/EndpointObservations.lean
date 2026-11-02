import ChaCha.Paper20261030.ExtremeSearch

/-!
# Finding an extreme using only reached records

Follow the requested fixed direction until the first marked port. The
parser stops on its entry bit and returns the preceding core record.
It never inspects the hanging subtree. The complete root-to-root tour
costs at most three operations per auxiliary level plus one boundary
read; its returned key is the actual minimum or maximum separator.
-/

namespace ChaCha.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata SourcePointer

variable {α κ : Type*} {β : κ → Type*}

def parseEndpoint : List (Record (β := β)) →
    Option (Option (Sigma (Tagged β)) × List (Record (β := β)))
  | [] => none
  | record :: records =>
      if entry record then some (none,records)
      else do
        let (result,rest) ← parseEndpoint records
        return (some (result.getD record.2),rest)

theorem observeEndpoint (direction : Bool) (t : Impl κ (Tagged β)) (clean : Clean t)
    (ports : Nat → Source α (Record (β := β))) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base + (recordTree t).size → entry (ports i).rootRecord = true)
    (ancestors : List (SourcePointer.Frame α (Record (β := β)))) :
    ∃ (reads : List (Record (β := β))) (cost : Nat),
      SourcePointer.Trace ⟨GapSource.encode (recordTree t) ports base,ancestors⟩ reads
        ⟨GapSource.encode (recordTree t) ports base,ancestors⟩ cost ∧
      (∀ tail, parseEndpoint (reads ++ tail) = some (extreme direction t,tail)) ∧
      cost ≤ 3 * height t + 1 := by
  induction t generalizing base ancestors with
  | leaf =>
    have hm := marked base le_rfl (by simp [recordTree,MTR.Tree.size])
    exact ⟨[(ports base).rootRecord],1,.read (.nil _),
      fun tail => by simp only [List.singleton_append,parseEndpoint,hm,if_true,extreme],by simp [height]⟩
  | inner cached key value l r ihl ihr =>
    have he : entry (cached,⟨key,value⟩) = false := clean.1
    cases direction
    · have hl : ∀ i, base ≤ i → i ≤ base + (recordTree l).size → entry (ports i).rootRecord = true := by
        intro i hlo hhi
        exact marked i hlo (by simp only [recordTree,MTR.Tree.size]; omega)
      obtain ⟨reads,cost,trace,parsed,bound⟩ := ihl clean.2.1 base hl
        (.left (cached,⟨key,value⟩)
          (GapSource.encode (recordTree r) ports (base + (recordTree l).size + 1)) :: ancestors)
      have full := SourcePointer.Trace.read (.step (.left _ _ _ _)
        (trace.append (.step (.upLeft _ _ _ _) (.nil _))))
      refine ⟨(cached,⟨key,value⟩) :: reads,cost + 3,?_,?_,?_⟩
      · simpa only [recordTree,GapSource.encode,Source.rootRecord,List.append_nil,
          Nat.add_assoc] using full
      · intro tail
        simp [parseEndpoint,he,parsed,extreme]
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
      · simpa only [recordTree,GapSource.encode,Source.rootRecord,List.append_nil,
          Nat.add_assoc] using full
      · intro tail
        simp [parseEndpoint,he,parsed,extreme]
      · simp only [height]
        omega

theorem observeEndpoint_component (direction : Bool) (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (ancestors) :
    ∃ reads cost,
      SourcePointer.Trace ⟨c.tree,ancestors⟩ reads ⟨c.tree,ancestors⟩ cost ∧
      (∀ tail, parseEndpoint (reads ++ tail) = some (extreme direction c.core,tail)) ∧
      cost ≤ 9 * Nat.clog 2 (c.core.size + 1) + 1 := by
  obtain ⟨reads,cost,trace,parsed,bound⟩ := observeEndpoint direction c.core hc c.ports 0
    (fun i _ hi => hp i (by simpa only [Nat.zero_add,recordTree_size_of_balanced c.core c.balanced] using hi))
    ancestors
  exact ⟨reads,cost,trace,parsed,by have := balanced_height_log c.balanced; omega⟩

end ChaCha.Paper20261030.BoundaryObservations
