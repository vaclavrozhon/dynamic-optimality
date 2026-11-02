import DynamicOptimality.SingleFinger.SourceOpenDeque
import DynamicOptimality.SingleFinger.SourceOpenLeftDeque
import DynamicOptimality.SingleFinger.BoundedScanPositions

/-! Physical skeleton with two compressed deque contexts on each edge.

`stump` is an unchanged subtree containing no represented skeleton vertex.
`key` and `fork` represent skeleton vertices. A compressed edge first nests
the increasing queue at its maximum gap, then the decreasing queue at its
minimum gap. Every child skeleton root is therefore at physical depth at
most five from its parent, regardless of the number of queued vertices.

This module proves the physical depth and branching counts. Correspondence
with source fingers and preservation by source instructions is a separate
obligation; a value of this datatype alone is not a simulator invariant.
-/

namespace DynamicOptimality.SingleFinger.Skeleton

open ChaCha.Paper20261030 ColoredStorage SourcePointer
open SourceSpine SourceOpenDeque SourceBoundary

variable {α ρ : Type*}

structure Tendon (α ρ : Type*) where
  low : Option (Right α ρ)
  high : Option (Left α ρ)

def Tendon.fill (tendon : Tendon α ρ) (gap : Source α ρ) : Source α ρ :=
  let inner := match tendon.high with
    | none => gap
    | some queue => (queue.fill gap).tree
  match tendon.low with
  | none => inner
  | some queue => (queue.fill inner).tree

inductive Hand (α ρ : Type*) where
  | stump (tree : Source α ρ)
  | key (key : α) (record : ρ)
  | fork (record : ρ) (leftEdge : Tendon α ρ) (left : Hand α ρ)
      (rightEdge : Tendon α ρ) (right : Hand α ρ)

def Hand.physical : Hand α ρ → Source α ρ
  | .stump tree => tree
  | .key atom record => .leaf atom record
  | .fork record leftEdge left rightEdge right =>
      .fork record (leftEdge.fill left.physical) (rightEdge.fill right.physical)

def Hand.vertices : Hand α ρ → List ρ
  | .stump _ => []
  | .key _ record => [record]
  | .fork record _ left _ right => record::(left.vertices++right.vertices)

def Hand.size : Hand α ρ → Nat
  | .stump _ => 0
  | .key _ _ => 1
  | .fork _ _ left _ right => 1+left.size+right.size

def Hand.nonempty : Hand α ρ → Bool
  | .stump _ => false
  | _ => true

def Hand.markedCount (marked : ρ → Bool) : Hand α ρ → Nat
  | .stump _ => 0
  | .key _ record => if marked record then 1 else 0
  | .fork record _ left _ right =>
      (if marked record then 1 else 0)+left.markedCount marked+right.markedCount marked

def Hand.Reduced (marked : ρ → Bool) : Hand α ρ → Prop
  | .stump _ => True
  | .key _ record => marked record = true
  | .fork record _ left _ right => left.Reduced marked ∧ right.Reduced marked ∧
      (marked record = true ∨ (left.nonempty = true ∧ right.nonempty = true))

theorem Hand.branching_bound (marked : ρ → Bool) (hand : Hand α ρ) (reduced : hand.Reduced marked) :
    hand.size+(if hand.nonempty then 1 else 0) ≤ 2*hand.markedCount marked := by
  induction hand with
  | stump => simp [Hand.size,Hand.nonempty,Hand.markedCount]
  | key key record => simp_all [Hand.Reduced,Hand.size,Hand.nonempty,Hand.markedCount]
  | fork record leftEdge left rightEdge right leftIH rightIH =>
    rcases reduced with ⟨leftReduced,rightReduced,root⟩
    have leftBound := leftIH leftReduced
    have rightBound := rightIH rightReduced
    simp only [Hand.size,Hand.nonempty,ite_true,Hand.markedCount]
    rcases root with markedRoot | ⟨leftPresent,rightPresent⟩
    · rw [if_pos markedRoot]
      split_ifs at leftBound rightBound <;> omega
    · rw [leftPresent] at leftBound
      rw [rightPresent] at rightBound
      split_ifs <;> simp only [ite_true] at leftBound rightBound <;> omega

theorem contains_mono (test : ρ → Bool) {small large : Nat} (less : small ≤ large)
    (tree : Source α ρ) (found : BoundedScan.contains test small tree = true) :
    BoundedScan.contains test large tree = true := by
  induction small generalizing large tree with
  | zero => exact BoundedScan.contains_root test large tree found
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      cases tree with
      | leaf key record => exact found
      | fork record left right =>
        simp only [BoundedScan.contains,Bool.or_eq_true] at found ⊢
        rcases found with (root | leftHit) | rightHit
        · exact Or.inl (Or.inl root)
        · exact Or.inl (Or.inr (ih (by omega) left leftHit))
        · exact Or.inr (ih (by omega) right rightHit)

theorem rightPort_contains (test : ρ → Bool) (port : RightPort α ρ) (gap : Source α ρ)
    (depth : Nat) (found : BoundedScan.contains test depth gap = true) :
    BoundedScan.contains test (depth+2) (port.fill gap) = true := by
  cases port with | mk left pivot middle => cases middle with
    | none =>
      have deeper := contains_mono test (Nat.le_succ depth) gap found
      simpa only [RightPort.fill,BoundedScan.contains,deeper,Bool.or_true] using
        (show true = true from rfl)
    | some cell =>
      rcases cell with ⟨inside,entry⟩
      simp only [RightPort.fill,BoundedScan.contains,found,Bool.or_true]

theorem leftPort_contains (test : ρ → Bool) (port : LeftPort α ρ) (gap : Source α ρ)
    (depth : Nat) (found : BoundedScan.contains test depth gap = true) :
    BoundedScan.contains test (depth+2) (port.fill gap) = true := by
  cases port with | mk pivot right middle => cases middle with
    | none =>
      have deeper := contains_mono test (Nat.le_succ depth) gap found
      simp only [LeftPort.fill,BoundedScan.contains,deeper,Bool.or_true,Bool.true_or]
    | some cell =>
      rcases cell with ⟨entry,inside⟩
      simp only [LeftPort.fill,BoundedScan.contains,found,Bool.or_true,Bool.true_or]

theorem Tendon.contains (test : ρ → Bool) (tendon : Tendon α ρ) (gap : Source α ρ)
    (depth : Nat) (found : BoundedScan.contains test depth gap = true) :
    BoundedScan.contains test (depth+4) (tendon.fill gap) = true := by
  let inner := match tendon.high with
    | none => gap
    | some queue => (queue.fill gap).tree
  have high : BoundedScan.contains test (depth+2) inner = true := by
    cases equal : tendon.high with
    | none =>
      simpa only [inner,equal] using contains_mono test (show depth ≤ depth+2 by omega) gap found
    | some queue =>
      simpa only [inner,equal,Left.fill_tree] using leftPort_contains test queue.port gap depth found
  cases equal : tendon.low with
  | none =>
    simpa only [Tendon.fill,equal,inner] using
      contains_mono test (show depth+2 ≤ depth+4 by omega) inner high
  | some queue =>
    simpa only [Tendon.fill,equal,inner,Right.fill_tree,Nat.add_assoc] using
      rightPort_contains test queue.port inner (depth+2) high

theorem Hand.contains_vertex (test : ρ → Bool) (hand : Hand α ρ) {record : ρ}
    (member : record ∈ hand.vertices) (hit : test record = true) :
    BoundedScan.contains test (5*hand.size) hand.physical = true := by
  induction hand with
  | stump => simp [Hand.vertices] at member
  | key key entry =>
    simp only [Hand.vertices,List.mem_singleton] at member
    subst record
    exact BoundedScan.contains_root test _ _ hit
  | fork entry leftEdge left rightEdge right leftIH rightIH =>
    simp only [Hand.vertices,List.mem_cons,List.mem_append] at member
    rcases member with root | leftMember | rightMember
    · subst record
      exact BoundedScan.contains_root test _ _ hit
    · have child := leftEdge.contains test left.physical (5*left.size) (leftIH leftMember)
      have deeper := contains_mono test (tree := leftEdge.fill left.physical)
        (show 5*left.size+4 ≤ 5*(left.size+right.size)+4 by omega) child
      have depthEq : 5*(1+left.size+right.size) = (5*(left.size+right.size)+4)+1 := by omega
      simp only [Hand.physical,Hand.size,depthEq,BoundedScan.contains,deeper,Bool.or_true,Bool.true_or]
    · have child := rightEdge.contains test right.physical (5*right.size) (rightIH rightMember)
      have deeper := contains_mono test (tree := rightEdge.fill right.physical)
        (show 5*right.size+4 ≤ 5*(left.size+right.size)+4 by omega) child
      have depthEq : 5*(1+left.size+right.size) = (5*(left.size+right.size)+4)+1 := by omega
      simp only [Hand.physical,Hand.size,depthEq,BoundedScan.contains,deeper,Bool.or_true]

end DynamicOptimality.SingleFinger.Skeleton
