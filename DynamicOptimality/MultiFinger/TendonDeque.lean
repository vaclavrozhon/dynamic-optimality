import DynamicOptimality.GeometricOnlineSimulation.OpenDeque
import DynamicOptimality.MultiFinger.Deque

/-! Reopening a physical deque at its actual first or last hanging subtree.
The whole layout is retained exactly: reopening does not rebuild a queue,
change its imbalance potential, or replace a source subtree by another one.
-/

namespace DynamicOptimality.MultiFinger.TendonDeque

open ChaCha.MTR SingleFinger
open DynamicOptimality.GeometricOnlineSimulation.OpenDeque

variable {α : Type*}

def trailing (gap : RawTree α) : List (Spine.Cell α) → RawTree α
  | [] => gap
  | (_,next)::cells => trailing next cells

def terminal (layout : SingleFinger.Deque.Layout α) : RawTree α := trailing layout.gap layout.cells

theorem trailing_append (gap : RawTree α) (first last : List (Spine.Cell α)) :
    trailing gap (first++last) = trailing (trailing gap first) last := by
  induction first generalizing gap with
  | nil => rfl
  | cons cell cells ih => cases cell; exact ih _

theorem terminal_back (layout : SingleFinger.Deque.Layout α) :
    terminal layout = trailing layout.afterGap layout.back := by
  simp only [terminal,SingleFinger.Deque.Layout.cells,trailing_append,trailing]

theorem terminal_pop_min {before after : SingleFinger.Deque.Layout α} {key : α}
    (cells : before.cells = (key,after.gap)::after.cells) : terminal before = terminal after := by
  simp only [terminal,cells,trailing]

theorem terminal_pop_max {before after : SingleFinger.Deque.Layout α} {key : α} {gap : RawTree α}
    (cells : before.cells = after.cells++[(key,gap)]) : terminal before = gap := by
  simp only [terminal,cells,trailing_append,trailing]

@[simp] theorem right_terminal (layout : Right α) (gap : RawTree α) :
    terminal (layout.fill gap) = gap := by
  cases layout with
  | mk initial front pivot back =>
    cases back with
    | none => simp only [Right.fill,terminal_back,trailing]
    | some data =>
      rcases data with ⟨afterGap,back,last⟩
      simp only [Right.fill,terminal_back,trailing_append,trailing]

/-- The first gap was already an explicit layout field. -/
def asLeft (layout : SingleFinger.Deque.Layout α) : Left α :=
  ⟨layout.front,layout.pivot,layout.afterGap,layout.back⟩

@[simp] theorem asLeft_fill (layout : SingleFinger.Deque.Layout α) :
    (asLeft layout).fill layout.gap = layout := by cases layout; rfl

@[simp] theorem asLeft_potential (layout : SingleFinger.Deque.Layout α) :
    (asLeft layout).potential = layout.potential := rfl

/-- Reopen the literal last gap, with equality of the complete old layout.
This directly supplies exact cells, exact physical tree, and exact potential. -/
theorem open_right (layout : SingleFinger.Deque.Layout α) :
    ∃ openLayout : Right α, openLayout.fill (terminal layout) = layout ∧
      openLayout.potential = layout.potential := by
  rcases layout with ⟨gap,front,pivot,afterGap,back⟩
  by_cases empty : back = []
  · subst back
    refine ⟨⟨gap,front,pivot,none⟩,?_,rfl⟩
    simp only [terminal_back,trailing]
    rfl
  · have split : ∃ rest last, back = rest++[last] :=
      ⟨back.dropLast,back.getLast empty,(List.dropLast_concat_getLast empty).symm⟩
    obtain ⟨rest,last,same⟩ := split
    rcases last with ⟨lastKey,lastGap⟩
    subst back
    let opened : Right α := ⟨gap,front,pivot,some (afterGap,rest,lastKey)⟩
    have term : terminal (SingleFinger.Deque.Layout.mk gap front pivot afterGap (rest++[(lastKey,lastGap)])) = lastGap := by
      simp only [terminal_back,trailing_append,trailing]
    refine ⟨opened,?_,?_⟩
    · rw [term]
      rfl
    · simp only [opened,Right.potential,Right.fill,SingleFinger.Deque.Layout.potential,List.length_append,List.length_cons,List.length_nil]

/-- The final gap remains the same actual subtree after a minimum pop. -/
theorem pop_min_reopen (layout : SingleFinger.Deque.Layout α)
    (enough : 2 ≤ layout.cells.length) :
    ∃ (after : Right α) (key : α) (count : Nat),
      layout.cells = (key,after.gap)::(after.fill (terminal layout)).cells ∧
      SearchRotation.Rotations layout.tree
        (.node layout.gap key (after.fill (terminal layout)).tree) count ∧
      count+after.potential ≤ layout.potential+14 := by
  obtain ⟨remaining,key,count,cells,rotations,paid⟩ := MultiFinger.Deque.pop_min layout enough
  obtain ⟨after,filled,potential⟩ := open_right remaining
  have same := terminal_pop_min cells
  rw [← same] at filled
  refine ⟨after,key,count,?_,?_,?_⟩
  · have gapSame : after.gap = remaining.gap := by
      have fields := congrArg SingleFinger.Deque.Layout.gap filled
      cases shape : after.back <;> simpa only [Right.fill,shape] using fields
    simpa only [filled,gapSame] using cells
  · simpa only [filled] using rotations
  · simpa only [potential] using paid

end DynamicOptimality.MultiFinger.TendonDeque
