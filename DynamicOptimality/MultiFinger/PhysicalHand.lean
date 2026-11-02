import DynamicOptimality.MultiFinger.MarkedTendon
import DynamicOptimality.MultiFinger.SteinerMarked

/-! Persistent physical representation of an exact source hand.
All suppressed paths have their own two concrete deques. The top skeleton
contains at most five times as many real keys as the reduced source hand.
Subsequent top splays may change this skeleton shape while retaining its
word and its exact holes. -/

namespace DynamicOptimality.MultiFinger.PhysicalHand

open ChaCha.MTR
open Pointer (MarkedTree)
open TendonContents

variable {α : Type*}

inductive Realizes : Hand α → MarkedTree α → Nat → Prop
  | stump (tree : RawTree α) : Realizes (.stump tree) (.hole tree) 0
  | node {frames : List (Pointer.Frame α)} {left right : Hand α} {key : α}
      {a b : MarkedTree α} {leftPotential rightPotential : Nat}
      (tendon : Tendon α) (valid : tendon.Represents frames)
      (leftRep : Realizes left a leftPotential) (rightRep : Realizes right b rightPotential) :
      Realizes (.node frames left key right) (tendon.marked (.node a key b))
        (leftPotential+rightPotential+tendon.potential)

theorem Realizes.word {hand : Hand α} {physical : MarkedTree α} {potential : Nat}
    (valid : Realizes hand physical potential) : physical.erase.inorder = hand.source.inorder := by
  induction valid with
  | stump => rfl
  | @node frames left right key a b lp rp tendon valid leftRep rightRep leftIH rightIH =>
    simp only [Tendon.marked_erase,MarkedTree.erase,Hand.source]
    rw [tendon.word valid,TendonSource.split_word,TendonSource.split_word]
    simp only [Tree.inorder,leftIH,rightIH]

theorem Realizes.size {hand : Hand α} {physical : MarkedTree α} {potential : Nat}
    (valid : Realizes hand physical potential) : physical.skeleton.size ≤ 5*hand.core.size := by
  induction valid with
  | stump => simp [MarkedTree.skeleton,Hand.core,Tree.size]
  | @node frames left right key a b lp rp tendon valid leftRep rightRep leftIH rightIH =>
    have localBound := tendon.marked_size (MarkedTree.node a key b)
    simp only [MarkedTree.skeleton,Tree.size,Hand.core] at localBound ⊢
    omega

private theorem rightMarked_mem (port : GeometricOnlineSimulation.RightPort α)
    (inside : MarkedTree α) {key : α} (member : key ∈ inside.skeleton.inorder) :
    key ∈ (rightMarked port inside).skeleton.inorder := by
  cases shape : port.middle <;>
    simp only [rightMarked,shape,MarkedTree.skeleton,Tree.inorder,List.mem_append,List.mem_singleton,List.not_mem_nil] <;> tauto

private theorem leftMarked_mem (port : GeometricOnlineSimulation.LeftPort α)
    (inside : MarkedTree α) {key : α} (member : key ∈ inside.skeleton.inorder) :
    key ∈ (leftMarked port inside).skeleton.inorder := by
  cases shape : port.middle <;>
    simp only [leftMarked,shape,MarkedTree.skeleton,Tree.inorder,List.mem_append,List.mem_singleton,List.not_mem_nil] <;> tauto

theorem tendon_marked_mem (tendon : Tendon α) (inside : MarkedTree α) {key : α}
    (member : key ∈ inside.skeleton.inorder) : key ∈ (tendon.marked inside).skeleton.inorder := by
  have upper : key ∈ (highMarked tendon.highQueue inside).skeleton.inorder := by
    cases shape : tendon.highQueue with
    | none => exact member
    | some queue => exact leftMarked_mem queue.port inside member
  change key ∈ (lowMarked tendon.lowQueue (highMarked tendon.highQueue inside)).skeleton.inorder
  cases shape : tendon.lowQueue with
  | none => exact upper
  | some queue => exact rightMarked_mem queue.port _ upper

theorem Realizes.core_mem {hand : Hand α} {physical : MarkedTree α} {potential : Nat}
    (valid : Realizes hand physical potential) {key : α}
    (member : key ∈ hand.core.inorder) : key ∈ physical.skeleton.inorder := by
  induction valid with
  | stump => simp [Hand.core,Tree.inorder] at member
  | @node frames left right pivot a b lp rp tendon valid leftRep rightRep leftIH rightIH =>
    apply tendon_marked_mem tendon
    simp only [Hand.core,Tree.inorder,List.mem_append,List.mem_singleton] at member
    simp only [MarkedTree.skeleton,Tree.inorder,List.mem_append,List.mem_singleton]
    rcases member with (inside | equal) | inside
    · exact Or.inl (Or.inl (leftIH inside))
    · exact Or.inl (Or.inr equal)
    · exact Or.inr (rightIH inside)

def framesCount : Hand α → Nat
  | .stump _ => 0
  | .node frames left _ right => frames.length+framesCount left+framesCount right

theorem plug_size (frames : List (Pointer.Frame α)) (inside : RawTree α) :
    inside.size+frames.length ≤ (Pointer.plug inside frames).size := by
  induction frames generalizing inside with
  | nil => simp [Pointer.plug]
  | cons frame frames ih =>
    cases frame with
    | left key right =>
      have deeper := ih (ChaCha.MTR.Tree.node inside key right)
      simp only [Pointer.plug,List.length_cons,Tree.size] at deeper ⊢
      omega
    | right left key =>
      have deeper := ih (ChaCha.MTR.Tree.node left key inside)
      simp only [Pointer.plug,List.length_cons,Tree.size] at deeper ⊢
      omega

theorem framesCount_le (hand : Hand α) : framesCount hand+hand.core.size ≤ hand.source.size := by
  induction hand with
  | stump tree => simp [framesCount,Hand.core,Tree.size]
  | node frames left key right leftIH rightIH =>
    have sourceSize := plug_size frames (ChaCha.MTR.Tree.node left.source key right.source)
    simp only [framesCount,Hand.core,Tree.size,Hand.source] at sourceSize ⊢
    omega

theorem initialization (hand : Hand α) :
    ∃ (physical : MarkedTree α) (potential : Nat), Realizes hand physical potential ∧
      potential ≤ 4*framesCount hand := by
  induction hand with
  | stump tree => exact ⟨.hole tree,0,.stump tree,by simp [framesCount]⟩
  | node frames left key right leftIH rightIH =>
    obtain ⟨a,lp,leftRep,leftPaid⟩ := leftIH
    obtain ⟨b,rp,rightRep,rightPaid⟩ := rightIH
    obtain ⟨tendon,valid,paid⟩ := TendonContents.initialization frames
    refine ⟨tendon.marked (.node a key b),lp+rp+tendon.potential,.node tendon valid leftRep rightRep,?_⟩
    simp only [framesCount]
    omega

/-- The initialized compressed hand has linear total queue potential and
only O(k) top markers for k (possibly coincident) finger positions. -/
theorem initialize_fingers [DecidableEq α] (reference : RawTree α) (fingers : List α)
    (distinct : reference.inorder.Nodup) :
    ∃ (physical : MarkedTree α) (potential : Nat),
      Realizes (Hand.compress (fun key => decide (key ∈ fingers)) reference) physical potential ∧
      physical.erase.inorder = reference.inorder ∧
      physical.skeleton.size ≤ 10*fingers.length ∧ potential ≤ 4*reference.size := by
  let hand := Hand.compress (fun key => decide (key ∈ fingers)) reference
  obtain ⟨physical,potential,valid,paid⟩ := initialization hand
  have word := valid.word
  rw [show hand.source = reference from Hand.compress_source _ _] at word
  have core : hand.core.size ≤ 2*fingers.length := by
    rw [show hand.core = Steiner.skeleton (fun key => decide (key ∈ fingers)) reference from
      Hand.compress_core _ _]
    exact Steiner.size_le_fingers fingers reference distinct
  have markers := valid.size
  have total := framesCount_le hand
  rw [show hand.source = reference from Hand.compress_source _ _] at total
  exact ⟨physical,potential,valid,word,by omega,by omega⟩

end DynamicOptimality.MultiFinger.PhysicalHand
