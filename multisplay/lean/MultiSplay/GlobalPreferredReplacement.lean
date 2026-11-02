import MultiSplay.GlobalPreferredAttached

/-! # Replacing one actual opaque subtree beneath a preferred component -/

namespace MultiSplay.Global.Preferred

open DynamicOptimality DynamicOptimality.SearchRotation
open ChaCha.MTR
open Pointer (MarkedTree)
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch

variable {α : Type*}

theorem Attached.replace {before after : State} {entries : List (Key × RawTree α)}
    {physical : List (RawTree α)} (attached : Attached before entries physical)
    (unique : entries.Nodup) (index : Nat) (entry : Key × RawTree α)
    (found : entries[index]? = some entry) (replacement : RawTree α)
    (next : Realizes (restrict after entry.1) entry.2 replacement)
    (same : ∀ other ∈ entries, other ≠ entry → restrict after other.1 = restrict before other.1) :
    Attached after entries (physical.set index replacement) := by
  induction attached generalizing index with
  | nil => simp at found
  | @cons first tree entries physical head tail ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      cases index with
      | zero =>
          cases Option.some.inj found
          refine .cons next (Attached.state_congr tail ?_)
          intro other member
          exact same other (by simp [member]) (by intro equal; subst other; exact absent member)
      | succ index =>
          have different : first ≠ entry := by
            intro equal
            subst first
            exact absent (List.mem_of_getElem? found)
          refine .cons ?_ (ih tailUnique index found fun other member different =>
            same other (by simp [member]) different)
          rw [same first (by simp) different]
          exact head

theorem context_rotations (context : MarkedTree.Context α)
    {before after : RawTree α} {count : Nat} (run : Rotations before after count) :
    Rotations (context.plug (.hole before)).erase (context.plug (.hole after)).erase count := by
  induction context with
  | top => exact run
  | left key right context ih => exact ih.plug [.left key right.erase]
  | right left key context ih => exact ih.plug [.right left.erase key]

theorem context_hole_skeleton (context : MarkedTree.Context α) (before after : RawTree α) :
    (context.plug (.hole before)).skeleton = (context.plug (.hole after)).skeleton := by
  induction context <;> simp [MarkedTree.Context.plug, MarkedTree.skeleton, *]

theorem context_hole_list (context : MarkedTree.Context α) (before after : RawTree α) :
    (context.plug (.hole after)).holes =
      (context.plug (.hole before)).holes.set context.holesBefore.length after := by
  simp [MarkedTree.Context.holes_plug, MarkedTree.holes, List.singleton_append,
    List.set_append_right]

/-- A rotation trace inside one reference hole changes exactly that actual
physical subtree. Its outer preferred component and all other attachments
remain intact. -/
theorem Component.replace_hole_context {beforeState afterState : State} {reference : RawTree α}
    {before : MarkedTree α} (represented : Component beforeState reference before)
    (samePreferred : preferred afterState reference = preferred beforeState reference)
    (sameHoles : preferredHoles afterState reference = preferredHoles beforeState reference)
    (unique : (preferredHoles beforeState reference).Nodup)
    (index : Nat) (entry : Key × RawTree α)
    (found : (preferredHoles beforeState reference)[index]? = some entry)
    (replacement : RawTree α) {count : Nat}
    (child : Realizes (restrict afterState entry.1) entry.2 replacement)
    (run : Rotations (before.gapArray index) replacement count)
    (same : ∀ other ∈ preferredHoles beforeState reference, other ≠ entry →
      restrict afterState other.1 = restrict beforeState other.1) :
    ∃ after : MarkedTree α, ∃ context : MarkedTree.Context α,
      before = context.plug (.hole (before.gapArray index)) ∧
      context.holesBefore.length = index ∧
      after = context.plug (.hole replacement) ∧
      Component afterState reference after ∧
      Rotations before.erase after.erase count := by
  have attached := represented.attached
  have indexBound : index < before.holes.length := by
    rw [← attached.length_eq]
    exact (List.getElem?_eq_some_iff.mp found).choose
  obtain ⟨context, old, shape, position, oldFound⟩ := before.hole_context index indexBound
  let after := context.plug (.hole replacement)
  have oldGap : old = before.gapArray index := by
    simpa [MarkedTree.gapArray, List.getElem?_eq_getElem indexBound] using oldFound
  have afterHoles : after.holes = before.holes.set index replacement := by
    rw [shape, ← position]
    exact context_hole_list context old replacement
  refine ⟨after, context, by simpa only [oldGap] using shape, position, rfl,
    component_of_attached ?_ ?_, ?_⟩
  · rw [samePreferred, ← represented.1, shape]
    exact congrArg Tree.inorder (context_hole_skeleton context replacement old)
  · rw [sameHoles, afterHoles]
    exact attached.replace unique index entry found replacement child same
  · rw [shape]
    exact context_rotations context (oldGap ▸ run)

end MultiSplay.Global.Preferred
