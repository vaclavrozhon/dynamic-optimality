import Splay.Accounting.RibStackUpperContext
import Splay.Accounting.RibStackClassFrontier
import Splay.Accounting.RibStackExactPop

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport FrontierFolding Digits

namespace UpperContext

theorem frontier_next {lower root inner upper : ℕ} (context : UpperContext inner upper)
    (left : BST lower root) (tail : SupportFrontier (root + 1) inner) :
    context.frontier (.next left tail) = .next left (context.frontier tail) := by
  induction context with
  | hole => rfl
  | node initial right ih => simp [frontier, ih, SupportFrontier.append]

theorem lift_path {lower inner upper support rotations : ℕ} (context : UpperContext inner upper)
    {before after : BST lower inner} (path : HasSupportedPath before after support rotations) :
    HasSupportedPath (context.plug before) (context.plug after) (support + context.length) rotations := by
  induction context with
  | hole => simpa [plug, length] using path
  | node initial right ih =>
      simpa only [plug, length, Nat.add_assoc] using ih.leftContext right

theorem moveLow_path {lower root inner upper : ℕ} (context : UpperContext inner upper)
    (left : BST lower root) (core : BST (root + 1) inner) :
    HasSupportedPath (.node left (context.plug core)) (context.plug (.node left core))
      (context.length + 1) context.length :=
  ⟨_, _, context.moveLow left core, (context.moveLow_support left core).le,
    (context.moveLow_length left core).le⟩

end UpperContext

namespace ClassFrontier

/-- Reattach the fixed upper chunk after any update that preserves the
number of lower classes and the literal terminal class tree. -/
theorem attach_upper {terminalLower firstLower lower inner upper level : ℕ}
    {terminal : BST terminalLower upper} {first : BST firstLower inner}
    {digits : List Digit} {last : Digit} {frontier : SupportFrontier lower inner}
    (initial : ClassFrontier first level digits frontier) (context : UpperContext inner upper)
    (lastChunk : ClassFrontier terminal (level + digits.length) [last] (context.frontier (.last first))) :
    ClassFrontier terminal level (digits ++ [last]) (context.frontier frontier) := by
  induction initial with
  | empty => simpa using lastChunk
  | one first rest ih =>
      rw [UpperContext.frontier_next]
      exact .one first (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lastChunk))
  | two first second rest ih =>
      rw [UpperContext.frontier_next, UpperContext.frontier_next]
      exact .two first second (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lastChunk))
  | three first second third rest ih =>
      rw [UpperContext.frontier_next, UpperContext.frontier_next, UpperContext.frontier_next]
      exact .three first second third (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lastChunk))

set_option backward.isDefEq.respectTransparency false in
/-- Detach the final class as one concrete reversed upper chunk. Its first
class tree becomes the fixed terminal payload of the remaining open spine. -/
theorem exists_upperChunk {terminalLower lower upper level : ℕ}
    {terminal : BST terminalLower upper} {initial : List Digit} {last : Digit}
    {frontier : SupportFrontier lower upper}
    (classes : ClassFrontier terminal level (initial ++ [last]) frontier) :
    ∃ (firstLower inner : ℕ) (first : BST firstLower inner) (context : UpperContext inner upper)
      (core : SupportFrontier lower inner),
      ClassFrontier first level initial core ∧
      ClassFrontier terminal (level + initial.length) [last] (context.frontier (.last first)) ∧
      context.length = last.value ∧ context.frontier core = frontier := by
  induction initial generalizing lower level with
  | nil =>
      cases classes with
      | one first rest =>
          cases rest
          rename_i root a
          exact ⟨_, _, a, .node (.hole root) terminal, .last a, .empty _, .one first (.empty _), rfl, rfl⟩
      | two first second rest =>
          cases rest
          rename_i x y b a
          refine ⟨_, _, a, .node (.node (.hole x) b) terminal, .last a, .empty _, ?_, rfl, rfl⟩
          exact .two first second (.empty _)
      | three first second third rest =>
          cases rest
          rename_i x y z b c a
          refine ⟨_, _, a, .node (.node (.node (.hole x) b) c) terminal, .last a, .empty _, ?_, rfl, rfl⟩
          exact .three first second third (.empty _)
  | cons digit initial ih =>
      cases classes with
      | one first rest =>
          obtain ⟨firstLower, inner, terminal', context, core, shaped, lastChunk, length, same⟩ := ih rest
          refine ⟨firstLower, inner, terminal', context, .next _ core, .one first shaped, ?_, length, ?_⟩
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lastChunk
          · rw [UpperContext.frontier_next, same]
      | two first second rest =>
          obtain ⟨firstLower, inner, terminal', context, core, shaped, lastChunk, length, same⟩ := ih rest
          refine ⟨firstLower, inner, terminal', context, .next _ (.next _ core), .two first second shaped, ?_, length, ?_⟩
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lastChunk
          · rw [UpperContext.frontier_next, UpperContext.frontier_next, same]
      | three first second third rest =>
          obtain ⟨firstLower, inner, terminal', context, core, shaped, lastChunk, length, same⟩ := ih rest
          refine ⟨firstLower, inner, terminal', context, .next _ (.next _ (.next _ core)),
            .three first second third shaped, ?_, length, ?_⟩
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lastChunk
          · rw [UpperContext.frontier_next, UpperContext.frontier_next, UpperContext.frontier_next, same]

end ClassFrontier

end Splay.Accounting.OfflineNormalForm.RibStack
