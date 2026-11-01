import MultiSplay.PackedPhysicalTrees

/-! # Both physical executions follow exactly the same common event word -/

namespace MultiSplay.PackedSplay

open Splay.Interface (Element Parameters)
open TangoSquared.MTR.Tree (inorder)
open CommonForest (Event Step Trace)

variable {m : Nat} {params : Parameters} {slack depth : Nat}

namespace Move

variable {before after : List (Trees m)}

def events : Move params slack depth before after → List (Event (Element m))
  | .request _ tree _ key element _ _ _ _ _ _ => [.search (inorder (physical element tree)) (label element key.val)]
  | .split (l := l) (r := r) _ _ sl sr element _ _ =>
      [.split (inorder (physical (element ∘ JoinIntervals.leftEmbedding l r) sl)) (element (JoinRanks.pivot l r))
        (inorder (physical (element ∘ JoinIntervals.rightEmbedding l r) sr))]
  | .join (l := l) (r := r) _ _ sl sr element _ _ _ _ _ =>
      [.join (inorder (physical (element ∘ JoinIntervals.leftEmbedding l r) sl)) (element (JoinRanks.pivot l r))
        (inorder (physical (element ∘ JoinIntervals.rightEmbedding l r) sr))]
  | .rotation .. | .reorder .. => []

def comparisonCost : Move params slack depth before after → Nat
  | .rotation (actualDepth := actualDepth) .. => actualDepth + 1
  | .request .. | .split .. | .join .. => 1
  | .reorder .. => 0

theorem volume_le_comparisonCost (move : Move params slack depth before after) :
    move.requests + move.rotations + move.boundaries ≤ move.comparisonCost := by
  cases move <;> simp [requests, rotations, boundaries, comparisonCost]

theorem splay_trace (move : Move params slack depth before after) :
    CommonForest.SplayTrace (before.map Trees.physical) move.events (after.map Trees.physical)
      (move.splayCost + move.boundaries) := by
  cases move with
  | request comparison before after key element injective tail root execution cap normal =>
      have step := Trace.single (Step.search (prepare := CommonForest.idle)
        ((Auxiliary.Splay.of_indexed execution).map (label element)))
      simpa [Trees.physical, physical, events, splayCost, boundaries] using step.context [] (tail.map Trees.physical)
  | rotation before after splay element injective tail rotation normal => exact .nil _
  | split left right sl sr element injective tail =>
      have step := Trace.single (Step.split (Auxiliary.Splay.done (key := element (JoinRanks.pivot _ _))
        (physical (element ∘ JoinIntervals.leftEmbedding _ _) sl)
        (physical (element ∘ JoinIntervals.rightEmbedding _ _) sr)) (prepare := CommonForest.idle))
      simpa [Trees.physical, physical_join, events, splayCost, boundaries] using step.context [] (tail.map Trees.physical)
  | join left right sl sr element injective tail disjoint growing valueCap =>
      have step := Trace.single (Step.join (access := Auxiliary.Splay) (prepare := CommonForest.idle)
        (physical (element ∘ JoinIntervals.leftEmbedding _ _) sl)
        (physical (element ∘ JoinIntervals.rightEmbedding _ _) sr) (element (JoinRanks.pivot _ _)))
      simpa [Trees.physical, physical_join, events, splayCost, boundaries] using step.context [] (tail.map Trees.physical)
  | reorder order => exact Trace.single (.reorder (order.map Trees.physical))

theorem comparison_trace (move : Move params slack depth before after) :
    CommonForest.Program (before.map Trees.comparator) move.events (after.map Trees.comparator) move.comparisonCost := by
  cases move with
  | request comparison before after key element injective tail root execution cap normal =>
      have service : CommonForest.RootAccess (label element key.val) (physical element comparison) (physical element comparison) 0 := by
        obtain ⟨left, right, rfl⟩ := root
        exact .root _ _ _
      have step := Trace.single (Step.search (prepare := CommonForest.RotationPreparation) service)
      have domain := physical_inorder element before comparison
      simpa [Trees.comparator, events, comparisonCost, domain] using step.context [] (tail.map Trees.comparator)
  | rotation before after splay element injective tail rotation normal =>
      have step := Trace.single (Step.prepare (access := CommonForest.RootAccess)
        (prepare := CommonForest.RotationPreparation) ⟨_, rotation_physical rotation (label element), rfl⟩)
      simpa [Trees.comparator, physical, events, comparisonCost] using step.context [] (tail.map Trees.comparator)
  | split left right sl sr element injective tail =>
      have service := CommonForest.RootAccess.root
        (physical (element ∘ JoinIntervals.leftEmbedding _ _) left) (element (JoinRanks.pivot _ _))
        (physical (element ∘ JoinIntervals.rightEmbedding _ _) right)
      have step := Trace.single (Step.split (prepare := CommonForest.RotationPreparation) service)
      have leftDomain := physical_inorder (element ∘ JoinIntervals.leftEmbedding _ _) sl left
      have rightDomain := physical_inorder (element ∘ JoinIntervals.rightEmbedding _ _) sr right
      simpa [Trees.comparator, physical_join, events, comparisonCost, leftDomain, rightDomain] using step.context [] (tail.map Trees.comparator)
  | join left right sl sr element injective tail disjoint growing valueCap =>
      have step := Trace.single (Step.join (access := CommonForest.RootAccess) (prepare := CommonForest.RotationPreparation)
        (physical (element ∘ JoinIntervals.leftEmbedding _ _) left)
        (physical (element ∘ JoinIntervals.rightEmbedding _ _) right) (element (JoinRanks.pivot _ _)))
      have leftDomain := physical_inorder (element ∘ JoinIntervals.leftEmbedding _ _) sl left
      have rightDomain := physical_inorder (element ∘ JoinIntervals.rightEmbedding _ _) sr right
      simpa [Trees.comparator, physical_join, events, comparisonCost, leftDomain, rightDomain] using step.context [] (tail.map Trees.comparator)
  | reorder order => exact Trace.single (.reorder (order.map Trees.comparator))

end Move

namespace Program

def events : {before after : List (Trees m)} → Program params slack depth before after → List (Event (Element m))
  | _, _, .done _ => []
  | _, _, .next move tail => move.events ++ tail.events

abbrev comparisonCost {before after : List (Trees m)} (program : Program params slack depth before after) :=
  program.sum Move.comparisonCost

theorem structural_events {before after : List (Trees m)} (program : Program params slack depth before after) :
    CommonForest.structuralCount program.events = program.boundaries := by
  induction program with
  | done => rfl
  | next move tail ih =>
      cases move <;> simp_all [events, Move.events, CommonForest.structuralCount, CommonForest.Event.structural,
        boundaries, sum, Move.boundaries]

theorem volume_le_comparisonCost {before after : List (Trees m)} (program : Program params slack depth before after) :
    program.requests + program.rotations + program.boundaries ≤ program.comparisonCost := by
  induction program with
  | done => exact Nat.le_refl _
  | next move tail ih =>
      have paid := move.volume_le_comparisonCost
      change (move.requests + tail.requests) + (move.rotations + tail.rotations) +
        (move.boundaries + tail.boundaries) ≤ move.comparisonCost + tail.comparisonCost
      omega

theorem splay_trace {before after : List (Trees m)} (program : Program params slack depth before after) :
    CommonForest.SplayTrace (before.map Trees.physical) program.events (after.map Trees.physical)
      (program.splayCost + program.boundaries) := by
  induction program with
  | done => exact .nil _
  | next move tail ih =>
      simpa [events, splayCost, boundaries, sum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using move.splay_trace.append ih

theorem comparison_trace {before after : List (Trees m)} (program : Program params slack depth before after) :
    CommonForest.Program (before.map Trees.comparator) program.events (after.map Trees.comparator) program.comparisonCost := by
  induction program with
  | done => exact .nil _
  | next move tail ih => exact move.comparison_trace.append ih

end Program
end MultiSplay.PackedSplay
