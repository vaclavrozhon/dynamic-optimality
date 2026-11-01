import Splay.Lazy.SingletonDeletion
import Splay.Lazy.PartialBlockRelocation

namespace Splay.Lazy

theorem HeapView.parent_ne_none_iff_ne_root {n : ℕ} (view : HeapView n) (element : Element n) :
    view.parent element ≠ none ↔ element ≠ view.root := by
  constructor
  · intro parented equal
    subst element
    exact parented view.root_parent
  · exact view.parent_ne_none_of_ne_root

namespace State

/-- A canonical checkpoint with exactly one non-root element still detached. -/
def CompleteExcept {n : ℕ} (state : State n) (missing : Element n) : Prop :=
  ∀ element, element ∈ state.allElements ↔ state.view.parent element ≠ none ∧ element ≠ missing

/-- Deleting the future root and installing its view leaves only the old
root detached, provided payloads otherwise remain unchanged. -/
theorem Complete.completeExcept_of_root_swap {n : ℕ} {params : Interface.Parameters} {before after : State n}
    (complete : before.Complete) (valid : before.Valid params)
    (payloads : after.allElements = before.allElements.erase after.view.root) :
    after.CompleteExcept before.view.root := by
  intro element
  rw [payloads, after.view.parent_ne_none_iff_ne_root]
  by_cases atRoot : element = after.view.root
  · subst element
    simp [valid.allElements_nodup.not_mem_erase]
  · rw [List.mem_erase_of_ne atRoot, complete element, before.view.parent_ne_none_iff_ne_root]
    simp [atRoot]

theorem CompleteExcept.transport {n : ℕ} {before after : State n} {missing : Element n}
    (complete : before.CompleteExcept missing) (payloads : after.allElements = before.allElements)
    (root : after.view.root = before.view.root) : after.CompleteExcept missing := by
  intro element
  rw [payloads, complete element, after.view.parent_ne_none_iff_ne_root, before.view.parent_ne_none_iff_ne_root, root]

theorem CompleteExcept.insert {n : ℕ} {state : State n} {missing : Element n}
    (complete : state.CompleteExcept missing) (parented : state.view.parent missing ≠ none)
    {id : Interface.BlockId} {block : Block n} (found : state.blocks[id]? = some block) :
    (state.insert id missing).Complete := by
  intro element
  rw [Canonical.mem_insert_allElements_iff state id block missing element found, complete element]
  change element = missing ∨ state.view.parent element ≠ none ∧ element ≠ missing ↔ state.view.parent element ≠ none
  by_cases equal : element = missing
  · subst element
    simp [parented]
  · simp [equal]

end State
end Splay.Lazy
