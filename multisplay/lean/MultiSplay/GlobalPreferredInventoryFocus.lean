import MultiSplay.GlobalPreferredInventoryCore
import MultiSplay.GlobalPreferredReplacement

/-! # Retaining the inventory outside one physical opaque subtree -/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open TangoSquared.MTR
open Pointer (MarkedTree)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch

variable {α : Type*}

/-- Focus an existing child inventory, retaining a reconstruction operation
for the exact indexed physical hole. No choice of a new representation is
made for any unchanged child. -/
theorem Branches.focus {state : State} {entries : List (Key × RawTree α)}
    {physical trees : List (RawTree α)} (children : Branches state entries physical trees)
    (unique : entries.Nodup) (index : Nat) (entry : Key × RawTree α)
    (found : entries[index]? = some entry) :
    ∃ front child back, trees = front ++ child ++ back ∧
      Core (restrict state entry.1) entry.2 (physical[index]?.getD .empty) child ∧
      ∀ (nextState : State) (replacement : RawTree α) (nextChild : List (RawTree α)),
        Core (restrict nextState entry.1) entry.2 replacement nextChild →
        (∀ other ∈ entries, other ≠ entry → restrict nextState other.1 = restrict state other.1) →
        Branches nextState entries (physical.set index replacement) (front ++ nextChild ++ back) := by
  induction entries generalizing physical trees index with
  | nil => simp at found
  | cons first entries ih =>
      cases children with
      | @cons _ _ tree _ physical head rest child children =>
          obtain ⟨absent,tailUnique⟩ := List.nodup_cons.mp unique
          cases index with
          | zero =>
              cases Option.some.inj found
              refine ⟨[],head,rest,rfl,child,?_⟩
              intro nextState replacement nextChild next same
              apply Branches.cons next
              apply children.state_congr
              intro other member
              exact same other (by simp [member]) (by intro equal; subst other; exact absent member)
          | succ index =>
              have different : first ≠ entry := by
                intro equal
                subst first
                exact absent (List.mem_of_getElem? found)
              obtain ⟨front,selected,back,equation,selectedCore,replace⟩ :=
                ih children tailUnique index found
              refine ⟨head ++ front,selected,back,?_,selectedCore,?_⟩
              · rw [equation]
                simp only [List.append_assoc]
              · intro nextState replacement nextChild next same
                have updated := replace nextState replacement nextChild next
                  (fun other member different => same other (by simp [member]) different)
                have headCore : Core (restrict nextState first.1) first.2 tree head := by
                  rw [same first (by simp) different]
                  exact child
                simpa only [List.set_cons_succ, List.append_assoc] using
                  Branches.cons headCore updated

/-- Move a selected component pair through fixed inventory context. -/
theorem pair_context {before after front back : List (RawTree α)}
    {source incoming target parked : RawTree α} {remainder : List (RawTree α)}
    (first : before.Perm (rootPart source ++ rootPart incoming ++ remainder))
    (last : after.Perm (rootPart target ++ rootPart parked ++ remainder)) :
    ∃ rest,
      (front ++ before ++ back).Perm (rootPart source ++ rootPart incoming ++ rest) ∧
      (front ++ after ++ back).Perm (rootPart target ++ rootPart parked ++ rest) := by
  refine ⟨front ++ remainder ++ back,?_,?_⟩
  · have moved := (first.append_left front).append_right back
    have swapped := (List.perm_append_comm (l₁ := front)
      (l₂ := rootPart source ++ rootPart incoming)).append_right (remainder ++ back)
    exact moved.trans (by simpa only [List.append_assoc] using swapped)
  · have moved := (last.append_left front).append_right back
    have swapped := (List.perm_append_comm (l₁ := front)
      (l₂ := rootPart target ++ rootPart parked)).append_right (remainder ++ back)
    exact moved.trans (by simpa only [List.append_assoc] using swapped)

end MultiSplay.Global.Preferred
