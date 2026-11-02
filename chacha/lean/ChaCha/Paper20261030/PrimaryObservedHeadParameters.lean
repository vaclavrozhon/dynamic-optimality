import ChaCha.Paper20261030.ObservedHeadParameters
import ChaCha.Paper20261030.PreparedLeafIntervals
import ChaCha.Paper20261030.AnnotatedVirtualHeadPackets
import ChaCha.Paper20261030.PrimaryExitDistinctness
import ChaCha.Paper20261030.LocalComponentCompiler
import ChaCha.Paper20261030.HeadVirtualOutputShapes

set_option autoImplicit false

/-! Success and meaning of the computation from the seven acquired values.
The primary exit decomposition and the preserved depth words determine
the boundary colors and both virtual shapes. No successful repair or
successful virtual-header exchange is assumed. -/

namespace ChaCha.Paper20261030.PrimaryObservedHeadParameters

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata
open PreferredProjection PrimaryWings PackedPrimary

variable {α ρ η : Type*} [DecidableEq α]

local instance primaryObservedHeadParametersColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem computed (before after old incoming : PrefRouter α) (common : List (Exit α)) (side : Bool)
    (beforeWord : exits before = common ++ ⟨side,incoming⟩ :: exits old)
    (afterWord : exits after = common ++ ⟨!side,old⟩ :: exits incoming)
    (identifier : ρ → η) (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ)
    (headPart oldTail incomingTail : Source Nat ρ)
    (activeWord : headPart.shape.leaves ++ common.length::oldTail.shape.leaves =
      List.range' 0 ((exits before).length+1))
    (incomingWord : common.length::incomingTail.shape.leaves =
      List.range' common.length ((exits incoming).length+2))
    (activeForest incomingForest : TaggedForest (Option Bool) Nat (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (activeRep : ProjectionForest.Represents (color 0 before)
      ⟨annotate identifier (color 0 before) none
        (.fork low headPart (.fork oldHigh (.leaf common.length oldTerminal) oldTail)),[]⟩ (erase activeForest))
    (incomingRep : ProjectionForest.Represents (color (common.length+1) incoming)
      ⟨annotate identifier (color (common.length+1) incoming) none
        (.fork incomingHigh (.leaf common.length incomingTerminal) incomingTail),[]⟩ (erase incomingForest)) :
    ∃ (data : ObservedHeadParameters.Data Nat ρ η) (oldPacket incomingPacket : List (HeadBoundary.Record ρ η (Option Bool))),
      ObservedHeadParameters.compute identifier
        (BoundaryReadController.activeResult identifier (color 0 before) low oldHigh oldTerminal common.length headPart oldTail)
        (BoundaryReadController.sentinelResult identifier (color (common.length+1) incoming)
          incomingHigh incomingTerminal common.length incomingTail)
        (ForestMirrorController.transform LocalComponentCompiler.wingOrientation (encode activeForest) none)
        (ForestMirrorController.transform LocalComponentCompiler.wingOrientation (encode incomingForest) none) = some data ∧
      data.direction = side ∧
      data.old = observed identifier (color 0 before) (color (common.length+1) incoming)
        low oldHigh incomingHigh oldTerminal incomingTerminal common.length headPart oldTail incomingTail ∧
      data.activeHeader = ForestMirrorController.transform LocalComponentCompiler.wingOrientation (encode activeForest) none ∧
      data.incomingHeader = ForestMirrorController.transform LocalComponentCompiler.wingOrientation (encode incomingForest) none ∧
      activeTree data.fresh common.length
        (annotate identifier (color 0 before) (some (identifier low)) headPart)
        (annotate identifier (color (common.length+1) incoming) (some (identifier incomingHigh)) incomingTail) =
        annotate identifier (color 0 after) none
          (.fork low headPart (.fork incomingHigh (.leaf common.length incomingTerminal) incomingTail)) ∧
      dormantTree data.fresh common.length
        (annotate identifier (color 0 before) (some (identifier oldHigh)) oldTail) =
        annotate identifier (color (common.length+1) old) none
          (.fork oldHigh (.leaf common.length oldTerminal) oldTail) ∧
      data.newHeader = VirtualPhysicalPackets.encode
        (.leaf (common.length+1+(exits incoming).length)
          (VirtualHeadPackets.prefixes data.fresh.low data.fresh.incomingHigh ++ incomingPacket)) ∧
      data.dormantHeader = VirtualPhysicalPackets.encode
        (.fork [data.fresh.oldHigh] (.leaf common.length [data.fresh.oldTerminal])
          (.leaf (exits before).length oldPacket)) ∧
      VirtualPhysicalPackets.decode data.newHeader =
        (packed (color 0 after) none (annotate identifier (color 0 after) none
          (.fork low headPart (.fork incomingHigh (.leaf common.length incomingTerminal) incomingTail)))).map
          (fun source => ⟨source,[]⟩) ∧
      VirtualPhysicalPackets.decode data.dormantHeader =
        (packed (color (common.length+1) old) none (annotate identifier (color (common.length+1) old) none
          (.fork oldHigh (.leaf common.length oldTerminal) oldTail))).map (fun source => ⟨source,[]⟩) := by
  have intervals := PreparedLeafIntervals.split_range 0 (exits before).length common.length
    headPart.shape.leaves oldTail.shape.leaves (by simpa only [Nat.sub_zero] using activeWord)
  have prefixDepths := PreparedLeafIntervals.below intervals.1
  have oldDepths := PreparedLeafIntervals.above intervals.2
  have incomingInterval : incomingTail.shape.leaves = List.range' (common.length+1) ((exits incoming).length+1) := by
    simpa only [show (exits incoming).length+2-1 = (exits incoming).length+1 by omega] using (List.range'_eq_cons_iff.mp incomingWord.symm).2.2
  have incomingDepths : ∀ key ∈ incomingTail.shape.leaves, common.length < key := by
    intro key member
    rw [incomingInterval,List.mem_range'_1] at member
    omega
  have oldExit : color 0 before common.length = some side := by
    simp only [color,beforeWord,portAt_boundary,Option.map_some]
  have sentinel : color (common.length+1) incoming common.length = none := by simp [color,portAt]
  have newExit : color 0 after common.length = some (!side) := by
    simp only [color,afterWord,portAt_boundary,Option.map_some]
  have newSentinel : color (common.length+1) old common.length = none := by simp [color,portAt]
  have prefixColors : ∀ key ∈ headPart.shape.leaves, color 0 before key = color 0 after key := by
    intro key member
    simp only [color,beforeWord,afterWord,portAt_prefix common _ key (prefixDepths key member)]
  have oldColors : ∀ key ∈ oldTail.shape.leaves, color 0 before key = color (common.length+1) old key := by
    intro key member
    simp only [color,beforeWord,portAt_tail common _ _ key (oldDepths key member)]
  have incomingColors : ∀ key ∈ incomingTail.shape.leaves,
      color (common.length+1) incoming key = color 0 after key := by
    intro key member
    simp only [color,afterWord,portAt_tail common _ _ key (incomingDepths key member)]
  obtain ⟨fresh,repaired,activeView,dormantView⟩ := observed_views identifier (color 0 before)
    (color (common.length+1) incoming) (color 0 after) (color (common.length+1) old)
    low oldHigh incomingHigh oldTerminal incomingTerminal common.length headPart oldTail incomingTail side
    oldExit sentinel newExit newSentinel prefixColors oldColors incomingColors
  have beforeBottom : common.length < (exits before).length := by
    rw [beforeWord,List.length_append,List.length_cons]
    omega
  have prefixAbsent := PrimaryVirtualPackets.prefix_absent before
    (annotate identifier (color 0 before) (some (identifier low)) headPart)
    (by rw [annotate_shape]; exact fun key member => (prefixDepths key member).trans beforeBottom)
  obtain ⟨oldPacket,oldTailPacked⟩ := PrimaryVirtualPackets.interval_packet 0 before (common.length+1)
    (annotate identifier (color 0 before) (some (identifier oldHigh)) oldTail) (Nat.zero_le _) (by omega)
    (by rw [annotate_shape,intervals.2]; congr 1 <;> omega)
  simp only [Nat.zero_add] at oldTailPacked
  have activePacked := AnnotatedVirtualHeadPackets.active identifier (color 0 before) low oldHigh oldTerminal
    common.length (exits before).length side headPart oldTail oldExit prefixAbsent oldPacket oldTailPacked
  obtain ⟨incomingPacket,incomingTailPacked⟩ := PrimaryVirtualPackets.interval_packet (common.length+1) incoming (common.length+1)
    (annotate identifier (color (common.length+1) incoming) (some (identifier incomingHigh)) incomingTail) le_rfl (by omega)
    (by rw [annotate_shape,incomingInterval]; congr 1 <;> omega)
  have incomingPacked := AnnotatedVirtualHeadPackets.dormant identifier (color (common.length+1) incoming)
    incomingHigh incomingTerminal common.length (common.length+1+(exits incoming).length) incomingTail sentinel incomingPacket incomingTailPacked
  have afterBottom : common.length < (exits after).length := by
    rw [afterWord,List.length_append,List.length_cons]
    omega
  have newPrefixAbsent := PrimaryVirtualPackets.prefix_absent after
    (annotate identifier (color 0 after) (some (identifier low)) headPart)
    (by rw [annotate_shape]; exact fun key member => (prefixDepths key member).trans afterBottom)
  have newTailPacked := (CanonicalRetainedPortFacts.annotation_color_congr identifier
    (color (common.length+1) incoming) (color 0 after) none (some (identifier incomingHigh)) incomingTail incomingColors).symm.trans incomingTailPacked
  have dormantTailPacked := (CanonicalRetainedPortFacts.annotation_color_congr identifier
    (color 0 before) (color (common.length+1) old) none (some (identifier oldHigh)) oldTail oldColors).symm.trans oldTailPacked
  have newPacked := HeadVirtualOutputShapes.active identifier (color 0 before) (color (common.length+1) incoming)
    (color 0 after) low incomingHigh incomingTerminal common.length (common.length+1+(exits incoming).length) (!side)
    headPart incomingTail fresh activeView newExit newPrefixAbsent incomingPacket newTailPacked
  have dormantPacked := HeadVirtualOutputShapes.dormant identifier (color 0 before) (color (common.length+1) old)
    oldHigh oldTerminal common.length (exits before).length oldTail fresh dormantView newSentinel oldPacket dormantTailPacked
  let records := observed identifier (color 0 before) (color (common.length+1) incoming)
    low oldHigh incomingHigh oldTerminal incomingTerminal common.length headPart oldTail incomingTail
  have exchanged := VirtualHeadPacketController.computed_from_forests records fresh
    (color 0 before) (color (common.length+1) incoming) _ _ activeForest incomingForest activeRep incomingRep
    LocalComponentCompiler.wingOrientation rfl common.length (exits before).length
    (common.length+1+(exits incoming).length) oldPacket incomingPacket activePacked incomingPacked
  have calculation := ObservedHeadParameters.computed identifier (color 0 before) (color (common.length+1) incoming)
    low oldHigh incomingHigh oldTerminal incomingTerminal common.length headPart oldTail incomingTail side oldExit fresh repaired
    _ _ _ _ exchanged
  refine ⟨_,oldPacket,incomingPacket,calculation,rfl,rfl,rfl,rfl,activeView,dormantView,rfl,rfl,?_,?_⟩
  · rw [VirtualPhysicalPackets.decode_encode _ (by change 1 ≤ 2; decide),newPacked]
    rfl
  · rw [VirtualPhysicalPackets.decode_encode _ (by change 1+1 ≤ 2; decide),dormantPacked]
    rfl

end ChaCha.Paper20261030.PrimaryObservedHeadParameters
