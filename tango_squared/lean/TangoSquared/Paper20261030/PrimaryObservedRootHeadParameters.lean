import TangoSquared.Paper20261030.ObservedRootHeadParameters
import TangoSquared.Paper20261030.PrimaryObservedHeadParameters
import TangoSquared.Paper20261030.RootHeadVirtualOutputShapes

set_option autoImplicit false

/-! Correctness of the minimum-depth computation from the six acquired
values. The primary exit words imply every repair condition and identify
the replacement virtual projections; no successful exchange is assumed. -/

namespace TangoSquared.Paper20261030.PrimaryObservedRootHeadParameters

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata
open PreferredProjection PrimaryWings PackedPrimary

variable {α ρ η : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem computed (before after old incoming : PrefRouter α) (side : Bool) (depth : Nat) (minimum : depth = 0)
    (beforeWord : exits before = ⟨side,incoming⟩ :: exits old)
    (afterWord : exits after = ⟨!side,old⟩ :: exits incoming)
    (identifier : ρ → η) (oldHigh incomingHigh oldTerminal incomingTerminal : ρ)
    (oldTail incomingTail : Source Nat ρ)
    (activeWord : depth :: oldTail.shape.leaves = List.range' 0 ((exits before).length+1))
    (incomingWord : depth :: incomingTail.shape.leaves = List.range' depth ((exits incoming).length+2))
    (activeForest incomingForest : TaggedForest (Option Bool) Nat (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (activeRep : ProjectionForest.Represents (color 0 before)
      ⟨annotate identifier (color 0 before) none
        (.fork oldHigh (.leaf depth oldTerminal) oldTail),[]⟩ (erase activeForest))
    (incomingRep : ProjectionForest.Represents (color (depth+1) incoming)
      ⟨annotate identifier (color (depth+1) incoming) none
        (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail),[]⟩ (erase incomingForest)) :
    ∃ (data : ObservedHeadParameters.Data Nat ρ η) (fresh : RootRecords ρ η)
      (oldPacket incomingPacket : List (HeadBoundary.Record ρ η (Option Bool))),
      ObservedRootHeadParameters.compute identifier
        (BoundaryReadController.sentinelResult identifier (color 0 before) oldHigh oldTerminal depth oldTail)
        (BoundaryReadController.sentinelResult identifier (color (depth+1) incoming) incomingHigh incomingTerminal depth incomingTail)
        (ForestMirrorController.transform LocalComponentCompiler.wingOrientation (encode activeForest) none)
        (ForestMirrorController.transform LocalComponentCompiler.wingOrientation (encode incomingForest) none) = some data ∧
      data.direction = side ∧
      data.old = RootMixedHeadExchange.lift (ObservedRootHeadParameters.observed identifier
        (color 0 before) (color (depth+1) incoming) oldHigh incomingHigh oldTerminal incomingTerminal depth oldTail incomingTail) ∧
      data.fresh = RootMixedHeadExchange.lift fresh ∧
      data.activeHeader = ForestMirrorController.transform LocalComponentCompiler.wingOrientation (encode activeForest) none ∧
      data.incomingHeader = ForestMirrorController.transform LocalComponentCompiler.wingOrientation (encode incomingForest) none ∧
      Source.fork data.fresh.incomingHigh (.leaf depth data.fresh.incomingTerminal)
        (annotate identifier (color (depth+1) incoming) (some (identifier incomingHigh)) incomingTail) =
        annotate identifier (color 0 after) none
          (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail) ∧
      dormantTree data.fresh depth
        (annotate identifier (color 0 before) (some (identifier oldHigh)) oldTail) =
        annotate identifier (color (depth+1) old) none (.fork oldHigh (.leaf depth oldTerminal) oldTail) ∧
      data.newHeader = VirtualPhysicalPackets.encode
        (.leaf (depth+1+(exits incoming).length)
          (ObservedHeadBlueprint.owned none data.fresh.incomingHigh ++ incomingPacket)) ∧
      data.dormantHeader = VirtualPhysicalPackets.encode
        (.fork [data.fresh.oldHigh] (.leaf depth [data.fresh.oldTerminal])
          (.leaf (exits before).length oldPacket)) ∧
      VirtualPhysicalPackets.decode data.newHeader =
        (packed (color 0 after) none (annotate identifier (color 0 after) none
          (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))).map (fun source => ⟨source,[]⟩) ∧
      VirtualPhysicalPackets.decode data.dormantHeader =
        (packed (color (depth+1) old) none (annotate identifier (color (depth+1) old) none
          (.fork oldHigh (.leaf depth oldTerminal) oldTail))).map (fun source => ⟨source,[]⟩) := by
  subst depth
  have oldInterval : oldTail.shape.leaves = List.range' 1 (exits before).length := by
    simpa only [Nat.add_sub_cancel] using (List.range'_eq_cons_iff.mp activeWord.symm).2.2
  have incomingInterval : incomingTail.shape.leaves = List.range' 1 ((exits incoming).length+1) := by
    simpa only [show (exits incoming).length+2-1 = (exits incoming).length+1 by omega] using
      (List.range'_eq_cons_iff.mp incomingWord.symm).2.2
  have oldDepths : ∀ key ∈ oldTail.shape.leaves, 0 < key := by
    intro key member
    rw [oldInterval,List.mem_range'_1] at member
    omega
  have incomingDepths : ∀ key ∈ incomingTail.shape.leaves, 0 < key := by
    intro key member
    rw [incomingInterval,List.mem_range'_1] at member
    omega
  have oldExit : color 0 before 0 = some side := by simp [color,beforeWord,portAt]
  have sentinel : color 1 incoming 0 = none := by simp [color,portAt]
  have newExit : color 0 after 0 = some (!side) := by simp [color,afterWord,portAt]
  have newSentinel : color 1 old 0 = none := by simp [color,portAt]
  have oldColors : ∀ key ∈ oldTail.shape.leaves, color 0 before key = color 1 old key := by
    intro key member
    have tail := portAt_tail ([] : List (Exit α)) (exits old) ⟨side,incoming⟩ key (oldDepths key member)
    simp only [List.nil_append,List.length_nil] at tail
    simp only [color,beforeWord,tail]
  have incomingColors : ∀ key ∈ incomingTail.shape.leaves, color 1 incoming key = color 0 after key := by
    intro key member
    have tail := portAt_tail ([] : List (Exit α)) (exits incoming) ⟨!side,old⟩ key (incomingDepths key member)
    simp only [List.nil_append,List.length_nil] at tail
    simp only [color,afterWord,tail]
  obtain ⟨fresh,repaired,activeView,dormantView⟩ := root_observed_views identifier
    (color 0 before) (color 1 incoming) (color 0 after) (color 1 old)
    oldHigh incomingHigh oldTerminal incomingTerminal 0 oldTail incomingTail side
    oldExit sentinel newExit newSentinel oldColors incomingColors
  have beforeBottom : 0 < (exits before).length := by rw [beforeWord]; simp
  obtain ⟨oldPacket,oldTailPacked⟩ := PrimaryVirtualPackets.interval_packet 0 before 1
    (annotate identifier (color 0 before) (some (identifier oldHigh)) oldTail) (Nat.zero_le _) (by omega)
    (by rw [annotate_shape,oldInterval]; congr 1 <;> omega)
  simp only [Nat.zero_add] at oldTailPacked
  have activePacked := AnnotatedVirtualHeadPackets.root_active identifier (color 0 before) oldHigh oldTerminal
    0 (exits before).length side oldTail oldExit oldPacket oldTailPacked
  obtain ⟨incomingPacket,incomingTailPacked⟩ := PrimaryVirtualPackets.interval_packet 1 incoming 1
    (annotate identifier (color 1 incoming) (some (identifier incomingHigh)) incomingTail) le_rfl (by omega)
    (by rw [annotate_shape,incomingInterval]; congr 1 <;> omega)
  have incomingPacked := AnnotatedVirtualHeadPackets.dormant identifier (color 1 incoming)
    incomingHigh incomingTerminal 0 (1+(exits incoming).length) incomingTail sentinel incomingPacket incomingTailPacked
  have newTailPacked := (CanonicalRetainedPortFacts.annotation_color_congr identifier
    (color 1 incoming) (color 0 after) none (some (identifier incomingHigh)) incomingTail incomingColors).symm.trans incomingTailPacked
  have dormantTailPacked := (CanonicalRetainedPortFacts.annotation_color_congr identifier
    (color 0 before) (color 1 old) none (some (identifier oldHigh)) oldTail oldColors).symm.trans oldTailPacked
  have newPacked := HeadVirtualOutputShapes.root_active identifier (color 1 incoming) (color 0 after)
    incomingHigh incomingTerminal 0 (1+(exits incoming).length) (!side) incomingTail (RootMixedHeadExchange.lift fresh)
    activeView newExit incomingPacket newTailPacked
  have dormantPacked := HeadVirtualOutputShapes.dormant identifier (color 0 before) (color 1 old)
    oldHigh oldTerminal 0 (exits before).length oldTail (RootMixedHeadExchange.lift fresh)
    dormantView newSentinel oldPacket dormantTailPacked
  let records := ObservedRootHeadParameters.observed identifier (color 0 before) (color 1 incoming)
    oldHigh incomingHigh oldTerminal incomingTerminal 0 oldTail incomingTail
  have exchanged := VirtualHeadPacketController.computed_root_from_forests records fresh
    (color 0 before) (color 1 incoming) _ _ activeForest incomingForest activeRep incomingRep
    LocalComponentCompiler.wingOrientation rfl 0 (exits before).length
    (1+(exits incoming).length) oldPacket incomingPacket activePacked incomingPacked
  have calculation := ObservedRootHeadParameters.computed identifier (color 0 before) (color 1 incoming)
    oldHigh incomingHigh oldTerminal incomingTerminal 0 oldTail incomingTail side oldExit fresh repaired
    _ _ _ _ exchanged
  refine ⟨_,fresh,oldPacket,incomingPacket,calculation,rfl,rfl,rfl,rfl,rfl,activeView,dormantView,rfl,rfl,?_,?_⟩
  · rw [VirtualPhysicalPackets.decode_encode _ (by change 1 ≤ 2; decide),newPacked]
    rfl
  · rw [VirtualPhysicalPackets.decode_encode _ (by change 1+1 ≤ 2; decide),dormantPacked]
    rfl

end TangoSquared.Paper20261030.PrimaryObservedRootHeadParameters
