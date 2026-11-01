import TangoSquared.Paper20261030.ForestLocalProgram

/-! A fixed local program moves a specified list of distinct color
fingers, one adjacent edge each. The list will be computed from the
intersection of two child color masks. No target cursor is a runtime input.
-/

namespace TangoSquared.Paper20261030.ForestNavigationController

open ColoredStorage SourcePointer ForestLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ C : Type*} [DecidableEq C]

def program (action : Move) : Program (List C) C ρ
  | [] => .halt
  | q::rest => .nav q action rest

theorem move (action : Move) (colors : List C) (before after : ProjectionForest.State C α ρ)
    (distinct : colors.Nodup)
    (selected : ∀ q ∈ colors, ∃ old fresh, before q = some old ∧ after q = some fresh ∧
      SourceLocalProgram.navigate action old = some fresh)
    (unchanged : ∀ q ∉ colors, before q = after q) :
    Run (program action) colors before [] after [] colors.length := by
  induction colors generalizing before with
  | nil =>
    have equal : before = after := by funext q; exact unchanged q (by simp)
    subst before
    exact .halt rfl
  | cons q rest ih =>
    obtain ⟨old,fresh,oldAt,freshAt,moved⟩ := selected q List.mem_cons_self
    let middle := Function.update before q (some fresh)
    have restSelected : ∀ i ∈ rest, ∃ old fresh, middle i = some old ∧ after i = some fresh ∧
        SourceLocalProgram.navigate action old = some fresh := by
      intro i member
      have different : i ≠ q := by intro equal; subst i; exact (List.nodup_cons.mp distinct).1 member
      simpa only [middle,Function.update_of_ne different] using selected i (List.mem_cons_of_mem _ member)
    have restUnchanged : ∀ i ∉ rest, middle i = after i := by
      intro i absent
      by_cases equal : i = q
      · subst i; simpa only [middle,Function.update_self] using freshAt.symm
      · simpa only [middle,Function.update_of_ne equal] using unchanged i (by simp only [List.mem_cons,not_or]; exact ⟨equal,absent⟩)
    have tail := ih middle (List.nodup_cons.mp distinct).2 restSelected restUnchanged
    exact Run.next (program := program action) (.nav rfl oldAt moved) tail

end TangoSquared.Paper20261030.ForestNavigationController
