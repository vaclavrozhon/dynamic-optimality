import MultiSplay.ComparatorStableSplice
import MultiSplay.ComparatorPrimaryAccess
import ChaCha.Paper20261030.DormantMemoryFrame

/-! # A complete persistent suffix transaction

Preparing the old component, exposing its two depth boundaries, exchanging
the tails, and restoring the one structural boundary gives two literal
source traces. The original prefix is the same opaque source on both sides.
-/

namespace MultiSplay.ComparatorStableSuffix

open ChaCha
open Paper20261030
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition ComparatorSuffix
open Secondary (intervalUpdate spliceBits)

def prefixPlug (kept : Option (Source Nat Unit)) (rest : Source Nat Unit) : Source Nat Unit :=
  match kept with
  | none => rest
  | some left => .fork () left rest

def exchangeShape (kept : Option (Source Nat Unit)) (d : Nat) (tail : Source Nat Unit) : Source Nat Unit :=
  prefixPlug kept (.fork () (.leaf d ()) tail)

def seamFactor {a b : Nat} (reference : DepthTree a b) : Nat :=
  Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 1

theorem prepared_exchange {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (lo : a ≤ start) (earlier : start ≤ d) (upper : d < b)
    (old incoming : DepthSplit → Bool)
    (component incomingTail : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (intervalUpdate d (bits start old)) start ⟨lo,by omega⟩) component)
    (incomingRep : Represents followsRight
      (suffixSource reference (bits (d+1) incoming) (d+1) ⟨by omega,by omega⟩) incomingTail) :
    ∃ (kept : Option (Source Nat Unit)) (oldTail result : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Represents followsRight
        (suffixSource reference (bits (d+1) old) (d+1) ⟨by omega,by omega⟩) oldTail ∧
      Represents followsRight
        (suffixSource reference (intervalUpdate d (bits start (spliceBits d old incoming)))
          start ⟨lo,by omega⟩) result ∧
      SourcePointer.Rearranges (ComparatorRecords.erase (closed component))
        (exchangeShape kept d (ComparatorRecords.erase (closed oldTail))) (20000 * seamFactor reference) ∧
      SourcePointer.Rearranges
        (exchangeShape kept d (ComparatorRecords.erase (closed incomingTail)))
        (ComparatorRecords.erase (closed result)) (20000 * seamFactor reference) := by
  by_cases minimum : start = d
  · subst start
    obtain ⟨oldTail,boundary,_,oldRep,detach⟩ := detach_stable_charged reference d d le_rfl
      ⟨lo,upper⟩ old component represented
    obtain ⟨pivot,result,_,_,_,resultRep,attach⟩ := attach_stable_charged reference d d le_rfl
      ⟨lo,upper⟩ incoming incomingTail incomingRep
    have same := prepared_suffix_congr reference (bits d (spliceBits d old incoming))
      (bits d incoming) d ⟨lo,by omega⟩ (by
        intro split _ after
        simp only [bits,spliceBits,if_neg (by omega : ¬split.lo < d),
          if_neg (by omega : ¬split.lo ≤ d)])
    rw [← same] at resultRep
    have first := detach.mapRecords (fun _ => ())
    have second := attach.mapRecords (fun _ => ())
    refine ⟨none,oldTail,result,oldRep,resultRep,?_,?_⟩
    · exact first.mono (by unfold seamFactor; omega)
    · exact second.mono (by unfold seamFactor; omega)
  · obtain ⟨kept,oldTail,result,oldRep,resultRep,first,second⟩ :=
      prepared_exchange_interior reference start d lo (by omega) upper old incoming
        component incomingTail represented incomingRep
    exact ⟨some kept,oldTail,result,oldRep,resultRep,first,second⟩

/-- No genuine record is reset. The old tail retains its old memory, and
the new main component reads the updated old prefix and the incoming tail. -/
theorem stable_exchange {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (lo : a ≤ start) (earlier : start ≤ d) (upper : d < b)
    (old incoming : DepthSplit → Bool)
    (component incomingTail : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits start old) start ⟨lo,by omega⟩) component)
    (incomingRep : Represents followsRight
      (suffixSource reference (bits (d+1) incoming) (d+1) ⟨by omega,by omega⟩) incomingTail) :
    ∃ (kept : Option (Source Nat Unit)) (oldTail result : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Represents followsRight
        (suffixSource reference (bits (d+1) old) (d+1) ⟨by omega,by omega⟩) oldTail ∧
      Represents followsRight
        (suffixSource reference (bits start (spliceBits d (writeGenuine start d old) incoming))
          start ⟨lo,by omega⟩) result ∧
      SourcePointer.Rearranges (ComparatorRecords.erase (closed component))
        (exchangeShape kept d (ComparatorRecords.erase (closed oldTail)))
        (40000 * (genuineCost reference start d old + 1) * seamFactor reference) ∧
      SourcePointer.Rearranges
        (exchangeShape kept d (ComparatorRecords.erase (closed incomingTail)))
        (ComparatorRecords.erase (closed result)) (40000 * seamFactor reference) := by
  obtain ⟨prepared,preparedRep,preparation⟩ := prepare_erased_charged reference start lo (by omega)
    d earlier old component represented
  obtain ⟨kept,oldTail,joined,oldRep,joinedRep,first,second⟩ :=
    prepared_exchange reference start d lo earlier upper old incoming prepared incomingTail
      preparedRep incomingRep
  obtain ⟨result,resultRep,restoration⟩ := restore_erased_charged reference start ⟨lo,by omega⟩
    d earlier (spliceBits d old incoming) joined joinedRep
  rw [write_splice] at resultRep
  have repair : repairBound reference ≤ 20000 * seamFactor reference := by
    unfold repairBound seamFactor
    omega
  have paid := Nat.mul_le_mul_left (genuineCost reference start d old + 1) repair
  refine ⟨kept,oldTail,result,oldRep,resultRep,(preparation.trans first).mono ?_,
    (second.trans restoration).mono ?_⟩
  · nlinarith [Nat.zero_le (genuineCost reference start d old * seamFactor reference)]
  · omega

theorem rearranges_leaf_word {α ρ : Type*} {before after : Source α ρ} {budget : Nat}
    (run : SourcePointer.Rearranges before after budget) : before.shape.leaves = after.shape.leaves := by
  obtain ⟨_,_,trace,_⟩ := run []
  exact trace.leaves

theorem prefix_word {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (lo : a ≤ start) (earlier : start ≤ d) (upper : d < b)
    (old : DepthSplit → Bool) (component oldTail : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits start old) start ⟨lo,by omega⟩) component)
    (tailRep : Represents followsRight
      (suffixSource reference (bits (d+1) old) (d+1) ⟨by omega,by omega⟩) oldTail)
    (kept : Option (Source Nat Unit)) {budget : Nat}
    (run : SourcePointer.Rearranges (ComparatorRecords.erase (closed component))
      (exchangeShape kept d (ComparatorRecords.erase (closed oldTail))) budget) :
    (kept.toList.flatMap fun t => t.shape.leaves) = List.range' start (d-start) := by
  have whole := rearranges_leaf_word run
  rw [ComparatorPrimary.stable_leaf_word reference start _ old component represented] at whole
  have tailWord := ComparatorPrimary.stable_leaf_word reference (d+1) _ old oldTail tailRep
  have expanded : (exchangeShape kept d (ComparatorRecords.erase (closed oldTail))).shape.leaves =
      (kept.toList.flatMap fun t => t.shape.leaves) ++ List.range' d (b+1-d) := by
    have last : d :: List.range' (d+1) (b+1-(d+1)) = List.range' d (b+1-d) := by
      rw [show b+1-d = (b+1-(d+1))+1 by omega,List.range'_succ]
    cases kept <;> simp only [exchangeShape,prefixPlug,Source.shape,RouterProjection.Router.leaves,
      tailWord,Option.toList,List.flatMap_nil,List.flatMap_cons,List.nil_append,List.append_nil,
      List.singleton_append,last]
  rw [expanded] at whole
  have range : List.range' start (b+1-start) =
      List.range' start (d-start) ++ List.range' d (b+1-d) := by
    simpa only [show start+(d-start)=d by omega,
      show d-start+(b+1-d)=b+1-start by omega] using
      (List.range'_append_1 (s := start) (m := d-start) (n := b+1-d)).symm
  rw [range] at whole
  exact (List.append_cancel_right whole).symm

end MultiSplay.ComparatorStableSuffix
