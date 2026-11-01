import MultiSplay.MacroGeometry
import MultiSplay.SharedSplayBound

/-!
# The bend telescope for changing component forests

A forest stores the actual comparison tree, splay tree, and rich state of every
component, with each component's own size. `BoundaryChange` permits common-root
splits and joins. `Evolution` ties every article macro in the shared interface
history to exactly one component of this forest.
-/

noncomputable section

namespace MultiSplay.SharedSplay

open Splay.Accounting
open Splay.Interface (Parameters)

abbrev Forest := List (Sigma ArticleCheckpoint)

namespace Forest

def potential (forest : Forest) : Nat := (forest.map (fun component => MacroGeometry.potential component.2)).sum

def keys (forest : Forest) : Nat := (forest.map Sigma.fst).sum

@[simp] theorem potential_append (first second : Forest) : (first ++ second).potential = first.potential + second.potential := by
  simp [potential]

@[simp] theorem potential_cons (head : Sigma ArticleCheckpoint) (tail : Forest) :
    potential (head :: tail) = MacroGeometry.potential head.2 + tail.potential := rfl

@[simp] theorem potential_nil : potential ([] : Forest) = 0 := rfl

theorem potential_le_keys (forest : Forest) : forest.potential ≤ forest.keys := by
  induction forest with
  | nil => exact Nat.le_refl 0
  | cons head tail ih =>
      have bound : MacroGeometry.potential head.2 ≤ head.1 :=
        (Finset.card_le_univ _).trans (by simp)
      simp only [potential_cons, keys, List.map_cons, List.sum_cons]
      change potential tail ≤ (tail.map Sigma.fst).sum at ih
      omega

end Forest

/-- Pure component-boundary changes, independently of the strict operations
which realize them in the actual global history. -/
inductive BoundaryChange : Forest → Forest → Prop
  | same (forest : Forest) : BoundaryChange forest forest
  | reorder {before after : Forest} (order : before.Perm after) : BoundaryChange before after
  | split {l r : Nat} (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
      (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r)
      (source : Splay.Lazy.State (0+l+1+r)) (a : Splay.Lazy.State l) (b : Splay.Lazy.State r)
      (front back : Forest) :
      BoundaryChange
        (front ++ [⟨_, ⟨JoinRanks.tree left right, JoinRanks.tree sl sr, source⟩⟩] ++ back)
        (front ++ [⟨l, ⟨left, sl, a⟩⟩, ⟨r, ⟨right, sr, b⟩⟩] ++ back)
  | join {l r : Nat} (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
      (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r)
      (source : Splay.Lazy.State (0+l+1+r)) (a : Splay.Lazy.State l) (b : Splay.Lazy.State r)
      (front back : Forest) :
      BoundaryChange
        (front ++ [⟨l, ⟨left, sl, a⟩⟩, ⟨r, ⟨right, sr, b⟩⟩] ++ back)
        (front ++ [⟨_, ⟨JoinRanks.tree left right, JoinRanks.tree sl sr, source⟩⟩] ++ back)
  | trans {first middle last : Forest} : BoundaryChange first middle → BoundaryChange middle last → BoundaryChange first last

theorem BoundaryChange.potential {first last : Forest} (change : BoundaryChange first last) :
    first.potential = last.potential := by
  induction change with
  | same forest => rfl
  | reorder order => exact (order.map (fun component => MacroGeometry.potential component.2)).sum_eq
  | split left right sl sr source a b front back =>
      simp [MacroGeometry.potential, CommonBends.join_card, Nat.add_assoc]
  | join left right sl sr source a b front back =>
      simp [MacroGeometry.potential, CommonBends.join_card, Nat.add_assoc]
  | trans first second ih₁ ih₂ => exact ih₁.trans ih₂

namespace Segment

variable {m : Nat} {params : Parameters} {first last : Splay.Interface.State m}

def requests : Segment params first last → Nat
  | .article step _ _ _ => step.requests.length
  | .maintenance _ => 0

def zigZags : Segment params first last → Nat
  | .article step _ _ _ => step.kinds.count .zigZag
  | .maintenance _ => 0

def splayCost : Segment params first last → Nat
  | .article step _ _ _ => MacroGeometry.splayCost step
  | .maintenance _ => 0

theorem splayCost_le (segment : Segment params first last) :
    segment.splayCost ≤ 2 * segment.zigZigs + 2 * segment.zigZags + 2 * segment.requests := by
  cases segment with
  | article step unbroken framed run => exact MacroGeometry.splayCost_le step
  | maintenance execution => exact Nat.le_refl 0

end Segment

variable {m : Nat} {params : Parameters}

inductive SegmentEvolution (slack depth : Nat) : {first last : Splay.Interface.State m} →
    Segment params first last → Forest → Forest → Prop
  | article {n : Nat} {before after : ArticleCheckpoint n} {whole : Splay.Interface.State m}
      (step : ArticleMacro params before after)
      (unbroken : PassedBlocksUnbroken (Splay.Rank.Snapshot.ofTree before.comparison).withTruePriority before.splay before.state)
      (framed : InterfaceFramedTrace.Framed params before.state.toInterface whole)
      (run : FramedSplay.Realization step whole framed) (normal : MacroGeometry.Normal slack depth step)
      (front back : Forest) :
      SegmentEvolution slack depth (.article step unbroken framed run)
        (front ++ [⟨n, before⟩] ++ back) (front ++ [⟨n, after⟩] ++ back)
  | maintenance {first last : Splay.Interface.State m} {word : List (Splay.Interface.Operation m)}
      (execution : Splay.Interface.Trace params first word last) {before after : Forest}
      (change : BoundaryChange before after) :
      SegmentEvolution slack depth (.maintenance execution) before after

namespace SegmentEvolution

variable {slack depth : Nat} {first last : Splay.Interface.State m}
  {segment : Segment params first last} {before after : Forest}

theorem bend_charge (evolution : SegmentEvolution slack depth segment before after) :
    after.potential + segment.zigZags ≤ before.potential + segment.zigZigs +
      (2+6*(slack+1)) * segment.requests + 3 * segment.rotations := by
  cases evolution with
  | article step unbroken framed run normal front back =>
      have paid := MacroGeometry.bend_charge step normal
      simp only [Forest.potential_append, Forest.potential_cons, Forest.potential_nil, Nat.add_zero,
        Segment.zigZags, Segment.zigZigs, Segment.requests, Segment.rotations]
      omega
  | maintenance execution change =>
      simpa [Segment.zigZags, Segment.zigZigs, Segment.requests, Segment.rotations] using Nat.le_of_eq change.potential.symm

theorem births (evolution : SegmentEvolution slack depth segment before after) :
    segment.births ≤ articleRequestBirthBudget slack * segment.requests +
      articleFullComparisonBirthBudget depth * segment.rotations := by
  cases evolution with
  | article step unbroken framed run normal front back => exact MacroGeometry.births step normal
  | maintenance execution change => simp [Segment.births, Segment.requests, Segment.rotations]

end SegmentEvolution

inductive Evolution (slack depth : Nat) : {first last : Splay.Interface.State m} →
    History params first last → Forest → Forest → Prop
  | done (state : Splay.Interface.State m) (forest : Forest) : Evolution slack depth (.done state) forest forest
  | next {first middle last : Splay.Interface.State m} {head : Segment params first middle} {tail : History params middle last}
      {before middleForest after : Forest}
      (headGeometry : SegmentEvolution slack depth head before middleForest)
      (tailGeometry : Evolution slack depth tail middleForest after) :
      Evolution slack depth (.next head tail) before after

namespace History

variable {first last : Splay.Interface.State m}

abbrev requests (history : History params first last) := history.sum Segment.requests
abbrev zigZags (history : History params first last) := history.sum Segment.zigZags
abbrev splayCost (history : History params first last) := history.sum Segment.splayCost

theorem splayCost_le (history : History params first last) :
    history.splayCost ≤ 2 * history.zigZigs + 2 * history.zigZags + 2 * history.requests := by
  induction history with
  | done state => simp [sum]
  | next head tail ih =>
      have paid := head.splayCost_le
      simp only [splayCost, zigZigs, zigZags, requests, sum]
      dsimp only [splayCost, zigZigs, zigZags, requests] at ih
      omega

end History

namespace Evolution

variable {slack depth : Nat} {first last : Splay.Interface.State m}
  {history : History params first last} {before after : Forest}

theorem bend_charge (evolution : Evolution slack depth history before after) :
    after.potential + history.zigZags ≤ before.potential + history.zigZigs +
      (2+6*(slack+1)) * history.requests + 3 * history.rotations := by
  induction evolution with
  | done state forest => simp [History.sum]
  | next head tail ih =>
      have paid := head.bend_charge
      simp only [History.zigZags, History.zigZigs, History.requests, History.rotations, History.sum] at *
      nlinarith

theorem births (evolution : Evolution slack depth history before after) :
    history.births ≤ articleRequestBirthBudget slack * history.requests +
      articleFullComparisonBirthBudget depth * history.rotations := by
  induction evolution with
  | done state forest => simp [History.sum]
  | next head tail ih =>
      have paid := head.births
      simp only [History.births, History.requests, History.rotations, History.sum] at *
      nlinarith

/-- Physical splay cost is controlled by the actual interface activity and
boundary pairs, plus linear initial and structural work. -/
theorem cost_le_pairings (evolution : Evolution slack depth history before after) :
    history.splayCost ≤ 4 * (Splay.Interface.totalActivity history.operations + history.boundary) +
      2 * before.keys + (6+12*(slack+1)) * history.requests +
        8 * history.rotations + 2 * history.maintenanceCost := by
  have cost := history.splayCost_le
  have bends := evolution.bend_charge
  have initial := before.potential_le_keys
  have zig := history.zigZigs_paid
  have inserts := history.inserts
  nlinarith

end Evolution
end MultiSplay.SharedSplay
