import TangoSquared.Paper20261030.StructuralCursor

/-!
# Complete charged execution with maintained structural fields

Every source instruction lifts at arbitrary depth, including repairing the
external parent's child descriptor. Rotations include an actual read tour
of both pivots. Even a payload write that changes its identifier is handled
by updating the two immediate children's parent fields; identifier-preserving
application writes are a special case. The uniform factor is twenty-one.
-/

namespace TangoSquared.Paper20261030.Structural

open ColoredStorage SourcePointer

variable {α ρ ι C : Type*} [DecidableEq C]

theorem write_any (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (source : Source α ρ) (fresh : ρ) :
    Rearranges (annotate identifier color parent source)
      (annotate identifier color parent (source.setRoot fresh)) 10 := by
  cases source with
  | leaf key old => exact (replace_root _ _).mono (by decide)
  | fork old l r =>
    let oldRecord := (old,fields identifier color parent (.fork old l r))
    let newRecord := (fresh,fields identifier color parent (.fork fresh l r))
    have left := (change_parent identifier color (some (identifier old)) (some (identifier fresh)) l).left
      (r := annotate identifier color (some (identifier old)) r) (record := oldRecord)
    have right := (change_parent identifier color (some (identifier old)) (some (identifier fresh)) r).right
      (l := annotate identifier color (some (identifier fresh)) l) (record := oldRecord)
    have root := replace_root (.fork oldRecord (annotate identifier color (some (identifier fresh)) l)
      (annotate identifier color (some (identifier fresh)) r)) newRecord
    exact (left.trans right).trans root

theorem observed_right_kernel (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) :
    Rearranges (annotate identifier color parent (.fork q (.fork p u v) w))
      (annotate identifier color parent (.fork p u (.fork q v w))) 17 := by
  intro outside
  obtain ⟨reads,cost,trace,bounded⟩ := observed_rotate_right identifier color parent u v w p q outside
  exact ⟨_,cost,trace,bounded⟩

theorem observed_left_kernel (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) :
    Rearranges (annotate identifier color parent (.fork p u (.fork q v w)))
      (annotate identifier color parent (.fork q (.fork p u v) w)) 17 := by
  intro outside
  have tour : Trace ⟨annotate identifier color parent (.fork p u (.fork q v w)),outside⟩
      [(annotate identifier color parent (.fork p u (.fork q v w))).rootRecord,
       (annotate identifier color (some (identifier p)) (.fork q v w)).rootRecord]
      ⟨annotate identifier color parent (.fork p u (.fork q v w)),outside⟩ 4 :=
    .read (.step (.right _ _ _ _) (.read (.step (.upRight _ _ _ _) (.nil _))))
  obtain ⟨reads,cost,trace,bounded⟩ := rotate_left identifier color parent u v w p q outside
  exact ⟨_,4+cost,tour.append trace,by omega⟩

theorem step (identifier : ρ → ι) (color : α → C) {before after : Cursor α ρ}
    (instruction : Step before after) :
    ∃ reads cost, Trace (cursor identifier color before) reads (cursor identifier color after) cost ∧ cost ≤ 21 := by
  cases instruction with
  | left l r record rest =>
    exact ⟨[],1,.step (move identifier color (.left l r record rest)).step (.nil _),by decide⟩
  | right l r record rest =>
    exact ⟨[],1,.step (move identifier color (.right l r record rest)).step (.nil _),by decide⟩
  | upLeft l r record rest =>
    exact ⟨[],1,.step (move identifier color (.upLeft l r record rest)).step (.nil _),by decide⟩
  | upRight l r record rest =>
    exact ⟨[],1,.step (move identifier color (.upRight l r record rest)).step (.nil _),by decide⟩
  | rotateRight u v w p q rest =>
    exact lift_rearrangement identifier color _ _ (by simp only [Source.support,Finset.union_assoc]) 17
      (fun parent => observed_right_kernel identifier color parent u v w p q) rest
  | rotateLeft u v w p q rest =>
    exact lift_rearrangement identifier color _ _ (by simp only [Source.support,Finset.union_assoc]) 17
      (fun parent => observed_left_kernel identifier color parent u v w p q) rest
  | write source fresh rest =>
    obtain ⟨reads,cost,trace,bounded⟩ := lift_rearrangement identifier color source (source.setRoot fresh)
      (by cases source <;> rfl) 10 (fun parent => write_any identifier color parent source fresh) rest
    exact ⟨reads,cost,trace,by omega⟩

theorem trace (identifier : ρ → ι) (color : α → C) {before after : Cursor α ρ}
    {observations : List ρ} {cost : Nat} (execution : Trace before observations after cost) :
    ∃ reads actualCost, Trace (cursor identifier color before) reads (cursor identifier color after) actualCost ∧
      actualCost ≤ 21 * cost := by
  induction execution with
  | nil => exact ⟨[],0,.nil _,Nat.zero_le _⟩
  | step instruction rest ih =>
    obtain ⟨firstReads,firstCost,first,firstBound⟩ := step identifier color instruction
    obtain ⟨lastReads,lastCost,last,lastBound⟩ := ih
    exact ⟨_,_,first.append last,by omega⟩
  | read rest ih =>
    obtain ⟨reads,actualCost,actual,bounded⟩ := ih
    exact ⟨_,_,.read actual,by omega⟩

theorem rearranges (identifier : ρ → ι) (color : α → C) {before after : Source α ρ} {budget : Nat}
    (execution : Rearranges before after budget) :
    Rearranges (annotate identifier color none before) (annotate identifier color none after) (21*budget) := by
  intro outside
  obtain ⟨observations,cost,actual,bounded⟩ := execution []
  obtain ⟨reads,actualCost,compiled,compileBound⟩ := trace identifier color actual
  exact ⟨reads,actualCost,compiled.extend outside,by omega⟩

end TangoSquared.Paper20261030.Structural
