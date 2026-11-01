import DynamicOptimality.SingleFinger.SourceDequeCatenate
import DynamicOptimality.SingleFinger.SourceDequeCatenateLeft
import DynamicOptimality.SingleFinger.SourcePortInterchange

/-! Join neighboring deques by transferring the smaller one.

The choice depends only on four stored spine lengths. If the outer queue is
smaller, a constant-size sequence of rotations interchanges the external gap
contexts first. Thus no traversal of the larger queue is charged to joining.
The persistent imbalance potential is retained in the output inequality.
-/

namespace DynamicOptimality.SingleFinger.SourceDequeJoin

open TangoSquared.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open SourceSpine SourceCounted SourceBoundary SourceOpenDeque

variable {α ρ : Type*}

def size (front back : Nat) : Nat := front+back+1

def plan (frontA backA frontB backB : Nat) (rest : Schedule) : Schedule :=
  if size frontB backB ≤ size frontA backA then
    SourceDequeCatenate.plan (decide (0 < backA)) frontB backB rest
  else
    interchangePlan (decide (0 < backA)) (decide (0 < frontB))
      (SourceDequeCatenateLeft.plan (decide (0 < frontB)) frontA backA rest)

theorem Right.tag_count (layout : Right α ρ) :
    layout.back.isSome = decide (0 < layout.backLength) := by
  cases layout with | mk gap front pivot back => cases back <;> simp [Right.backLength]

theorem Left.tag_count (layout : Left α ρ) :
    layout.doubled = decide (0 < layout.front.length) := by
  cases layout with | mk front pivot afterGap back => cases front <;> simp [Left.doubled]

theorem Right.fill_counts (layout : Right α ρ) (gap : Source α ρ) :
    (layout.fill gap).front.length = layout.front.length ∧
    (layout.fill gap).back.length = layout.backLength := by
  cases layout with | mk first front pivot back => cases back <;> simp [Right.fill,Right.backLength]

theorem Right.fill_size (layout : Right α ρ) (gap : Source α ρ) :
    (layout.fill gap).cells.length = size layout.front.length layout.backLength := by
  have lengths := Right.fill_counts layout gap
  simp only [SourceDeque.Layout.cells,List.length_append,List.length_cons,size]
  omega

def asLeft (layout : SourceDeque.Layout α ρ) : Left α ρ :=
  ⟨layout.front,layout.pivot,layout.afterGap,layout.back⟩

theorem asLeft_fill (layout : SourceDeque.Layout α ρ) :
    (asLeft layout).fill layout.gap = layout := by cases layout; rfl

theorem execute (outer : Right α ρ) (inner : SourceDeque.Layout α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    ∃ (after : SourceDeque.Layout α ρ) (cost : Nat),
      Steps code (plan outer.front.length outer.backLength inner.front.length inner.back.length rest)
        ⟨(outer.fill inner.tree).tree,outside⟩ rest ⟨after.tree,outside⟩ [] cost ∧
      cost+after.potential ≤ outer.potential+inner.potential+
        28*min (size outer.front.length outer.backLength) inner.cells.length+10 := by
  have innerSize : inner.cells.length = size inner.front.length inner.back.length := by
    simp [SourceDeque.Layout.cells,size,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  by_cases small : size inner.front.length inner.back.length ≤ size outer.front.length outer.backLength
  · obtain ⟨after,cost,run,bound,afterSame⟩ := SourceDequeCatenate.execute outer inner outside rest
    refine ⟨after.fill inner.terminal,cost,?_,?_⟩
    · simpa only [plan,if_pos small,← Right.tag_count outer] using run
    · rw [Right.fill_potential,Nat.min_eq_right (by omega)]
      omega
  · let high := asLeft inner
    let low := outer.fill inner.gap
    let finish := SourceDequeCatenateLeft.plan high.doubled low.front.length low.back.length rest
    have first := interchange outer.port high.port inner.gap outside finish
    have lowTree : low.tree = outer.port.fill inner.gap := outer.fill_tree inner.gap
    have highTree : high.port.fill inner.gap = inner.tree := by
      rw [← Left.fill_tree,asLeft_fill]
    rw [highTree,← lowTree,← outer.fill_tree inner.tree,← high.fill_tree low.tree] at first
    obtain ⟨after,cost,run,bound,afterSame⟩ := SourceDequeCatenateLeft.execute high low outside rest
    have full := first.append run
    refine ⟨after.fill low.gap,interchangeCost outer.port.middle.isSome high.port.middle.isSome+cost,?_,?_⟩
    · have counts := Right.fill_counts outer inner.gap
      simpa only [plan,if_neg small,finish,high,low,asLeft,Right.port_tag,Right.tag_count,
        Left.port_tag,Left.tag_count,counts.1,counts.2,List.nil_append] using full
    · have transport := interchangeCost_bound outer.port.middle.isSome high.port.middle.isSome
      have lowPotential : low.potential = outer.potential := outer.fill_potential inner.gap
      have highPotential : high.potential = inner.potential := rfl
      have lowSize : low.cells.length = size outer.front.length outer.backLength :=
        Right.fill_size outer inner.gap
      rw [Left.fill_potential,Nat.min_eq_left (by omega)]
      omega

end DynamicOptimality.SingleFinger.SourceDequeJoin
