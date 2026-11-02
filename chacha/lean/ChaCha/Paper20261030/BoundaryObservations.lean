import ChaCha.Paper20261030.AuxiliaryComponents

/-!
# Reading auxiliary boundaries from actual port-entry records

Open auxiliary records have entry bit false; each hanging port root has
entry bit true. The observation parser reads this bit before deciding
whether to descend. A marked port is reported as a logical empty child,
and its interior is never inspected. The checked tour returns the exact
bounded auxiliary snapshot using only the records it actually reads.
-/

namespace ChaCha.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata SourcePointer

variable {α κ : Type*} {β : κ → Type*}

abbrev Tagged (β : κ → Type*) (key : κ) := β key × Bool
abbrev Record := NodeRecord κ (Tagged β)

def entry (r : Record (β := β)) : Bool := r.2.2.2

def Clean : Impl κ (Tagged β) → Prop
  | .leaf => True
  | .inner _ _ value l r => value.2 = false ∧ Clean l ∧ Clean r

def parse : Nat → List (Record (β := β)) → Option (Snapshot κ (Tagged β) × List (Record (β := β)))
  | 0,records => some (.unseen,records)
  | _ + 1,[] => none
  | depth + 1,record :: records =>
      if entry record then some (.empty,records)
      else do
        let (left,rest) ← parse depth records
        let (right,rest') ← parse depth rest
        return (.node record.1 record.2.1 record.2.2 left right,rest')

theorem observe (depth : Nat) (t : Impl κ (Tagged β)) (clean : Clean t)
    (ports : Nat → Source α (Record (β := β))) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base + (recordTree t).size → entry (ports i).rootRecord = true)
    (ancestors : List (SourcePointer.Frame α (Record (β := β)))) :
    ∃ (reads : List (Record (β := β))) (cost : Nat),
      SourcePointer.Trace ⟨GapSource.encode (recordTree t) ports base,ancestors⟩ reads
        ⟨GapSource.encode (recordTree t) ports base,ancestors⟩ cost ∧
      (∀ tail, parse depth (reads ++ tail) = some (capture depth t,tail)) ∧
      cost ≤ 5 * (2 ^ depth - 1) := by
  induction depth generalizing t base ancestors with
  | zero => exact ⟨[],0,.nil _,fun _ => rfl,by simp⟩
  | succ depth ih =>
    have hpower : 0 < 2 ^ depth := Nat.two_pow_pos depth
    cases t with
    | leaf =>
      have hm := marked base le_rfl (by simp [recordTree,MTR.Tree.size])
      refine ⟨[(ports base).rootRecord],1,.read (.nil _),?_,?_⟩
      · intro tail
        simp only [List.singleton_append,parse,hm,if_true,capture]
      · rw [pow_succ]
        omega
    | inner cached key value l r =>
      have hl : ∀ i, base ≤ i → i ≤ base + (recordTree l).size → entry (ports i).rootRecord = true := by
        intro i hlo hhi
        exact marked i hlo (by simp only [recordTree,MTR.Tree.size]; omega)
      have hr : ∀ i, base + (recordTree l).size + 1 ≤ i →
          i ≤ base + (recordTree l).size + 1 + (recordTree r).size → entry (ports i).rootRecord = true := by
        intro i hlo hhi
        exact marked i (by omega) (by simp only [recordTree,MTR.Tree.size]; omega)
      obtain ⟨leftReads,leftCost,leftTrace,leftParse,leftBound⟩ := ih l clean.2.1 base hl
        (.left (cached,⟨key,value⟩)
          (GapSource.encode (recordTree r) ports (base + (recordTree l).size + 1)) :: ancestors)
      obtain ⟨rightReads,rightCost,rightTrace,rightParse,rightBound⟩ := ih r clean.2.2
        (base + (recordTree l).size + 1) hr
        (.right (GapSource.encode (recordTree l) ports base) (cached,⟨key,value⟩) :: ancestors)
      have leftRound := SourcePointer.Trace.step (SourcePointer.Step.left _ _ _ _)
        (leftTrace.append (.step (.upLeft _ _ _ _) (.nil _)))
      have rightRound := SourcePointer.Trace.step (SourcePointer.Step.right _ _ _ _)
        (rightTrace.append (.step (.upRight _ _ _ _) (.nil _)))
      have full := SourcePointer.Trace.read (leftRound.append rightRound)
      refine ⟨(cached,⟨key,value⟩) :: (leftReads ++ rightReads),leftCost + rightCost + 5,?_,?_,?_⟩
      · simpa only [recordTree,GapSource.encode,Source.rootRecord,List.append_nil,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full
      · intro tail
        have he : entry (cached,⟨key,value⟩) = false := clean.1
        simp [List.append_assoc,parse,he,leftParse,rightParse,capture]
      · rw [pow_succ]
        omega

end ChaCha.Paper20261030.BoundaryObservations
