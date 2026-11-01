import MultiSplay.ClassicalSwitchEventWord
import MultiSplay.ClassicalSwitchPartition

/-! # Selecting the actual current component of a switch

The selected reference subtree starts at `startDepth`. Its preferred path
contains the switched real node, and its spine is exactly the truncated
original ancestor spine used by `eventWord`. Thus the physical switch and
comparator receive one state-determined word, independently of their shapes.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder rootKey)
open TangoSquared.Primary (Key)
open EndpointEncoding CommonForest

variable {α : Type*}

theorem restrict_append (state : State) (first rest : Key) :
    restrict state (first ++ rest) = restrict (restrict state first) rest := by
  induction first generalizing state with
  | nil => rfl
  | cons edge first ih => exact ih (below state edge)

theorem referenceSpine_empty (address : Key) : referenceSpine (.empty : RawTree α) address = [] := by
  cases address <;> rfl

theorem referenceSpine_append (reference : RawTree α) (first rest : Key) :
    referenceSpine reference (first ++ rest) =
      referenceSpine (referenceAt reference first) rest ++ referenceSpine reference first := by
  induction first generalizing reference with
  | nil => simp [referenceAt, referenceSpine]
  | cons edge first ih =>
      cases reference with
      | empty => simp [referenceAt, referenceSpine, referenceSpine_empty]
      | node left key right =>
          simpa only [List.cons_append, referenceAt, referenceSpine, List.append_assoc] using
            congrArg (· ++ [(edge,key)]) (ih (if edge then right else left))

theorem referenceSpine_length {reference : RawTree α} {address : Key}
    (real : referenceAt reference address ≠ .empty) :
    (referenceSpine reference address).length = address.length := by
  induction address generalizing reference with
  | nil => rfl
  | cons edge rest ih =>
      cases reference with
      | empty => exact False.elim (real rfl)
      | node left key right =>
          simp only [referenceAt] at real
          simpa only [referenceSpine, List.length_append, List.length_singleton, List.length_cons, List.length_nil] using
            congrArg (· + 1) (ih real)

theorem path_at (state : State) (reference : RawTree α) (address : Key)
    (follows : RootPreferred state address) (real : referenceAt reference address ≠ .empty) :
    Path state reference address (referenceSpine reference address) (referenceAt reference address) := by
  induction address generalizing state reference with
  | nil => exact .here _ _
  | cons edge rest ih =>
      cases reference with
      | empty => exact False.elim (real rfl)
      | node left key right =>
          cases edge with
          | false => exact .left follows.head (ih (below state false) left follows.below real)
          | true => exact .right follows.head (ih (below state true) right follows.below real)

theorem componentSpine_suffix {reference : RawTree α} (state : State) (address : Key)
    (real : referenceAt reference address ≠ .empty) :
    componentSpine state reference address =
      referenceSpine (referenceAt reference (address.take (startDepth state address)))
        (address.drop (startDepth state address)) := by
  let depth := startDepth state address
  have alignedAt : referenceAt (referenceAt reference (address.take depth)) (address.drop depth) =
      referenceAt reference address := by rw [← referenceAt_append, List.take_append_drop]
  have length := referenceSpine_length (alignedAt ▸ real)
  rw [List.length_drop] at length
  unfold componentSpine
  have split := referenceSpine_append reference (address.take depth) (address.drop depth)
  rw [List.take_append_drop] at split
  rw [split]
  exact List.take_left' length

/-- The selected component and both nearest guards come from real reference
children. This theorem applies to every real emitted owner, not only to the
mandatory final switch in the root component. -/
theorem selected_path {reference : RawTree α} (state : State) (address : Key)
    (real : referenceAt reference address ≠ .empty) :
    Path (restrict state (address.take (startDepth state address)))
      (referenceAt reference (address.take (startDepth state address)))
      (address.drop (startDepth state address)) (componentSpine state reference address)
      (referenceAt reference address) := by
  have alignedAt : referenceAt (referenceAt reference (address.take (startDepth state address)))
      (address.drop (startDepth state address)) = referenceAt reference address := by
    rw [← referenceAt_append, List.take_append_drop]
  have path := path_at _ _ _ (startDepth_suffix state address) (alignedAt ▸ real)
  simpa only [alignedAt, componentSpine_suffix state address real] using path

theorem eventWord_selected {reference : RawTree α} (state : State) (address : Key)
    (real : referenceAt reference address ≠ .empty) :
    eventWord reference state address =
      eventWord (referenceAt reference (address.take (startDepth state address)))
        (restrict state (address.take (startDepth state address)))
        (address.drop (startDepth state address)) := by
  let depth := startDepth state address
  have alignedAt : referenceAt (referenceAt reference (address.take depth)) (address.drop depth) =
      referenceAt reference address := by rw [← referenceAt_append, List.take_append_drop]
  have path := selected_path state address real
  have spine := path.componentSpine
  have side : restrict state (address.take depth) (address.drop depth) = state address := by
    rw [restrict_eq, List.take_append_drop]
  have current : restrict (restrict state (address.take depth)) (address.drop depth) = restrict state address := by
    rw [← restrict_append, List.take_append_drop]
  dsimp only [depth] at alignedAt side current
  simp only [eventWord, alignedAt, spine, side, current]

/-- One actual standard switch at a selected preferred component executes the
state-determined word and preserves the exact post-toggle component domain. -/
theorem Path.eventWord_execution {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine (.node left pivot right))
    (whole incoming : RawTree α)
    (sourceKeys : inorder whole = inorder (preferred state reference))
    (incomingKeys : inorder incoming = inorder (tail (restrict state address) (!(state address)) (.node left pivot right)))
    (unique : (inorder whole).Nodup) :
    ∃ after parked rotations,
      Execution pivot incoming (state address) spine.lower spine.upper whole after parked rotations ∧
      SplayTrace [whole,incoming] (eventWord reference state address) [after,parked]
        (rotations + 2 + 2*spine.lower.count + 2*spine.upper.count) ∧
      inorder after = inorder (preferred (toggle state address) reference) ∧
      inorder parked = inorder (tail (restrict state address) (state address) (.node left pivot right)) := by
  obtain ⟨after,parked,rotations,run,oldKeys⟩ := Spine.execution_exists (state address) spine
    (tail (restrict state address) (state address) (.node left pivot right)) incoming whole pivot
    (by rw [sourceKeys, path.before]) unique
  refine ⟨after,parked,rotations,run,?_,?_,oldKeys⟩
  · simpa only [eventWord, path.referenceAt, path.componentSpine, oldKeys, incomingKeys] using run.trace
  · rw [run.after_keys, path.after, Spine.before_inorder]
    simp only [afterKeys, incomingKeys]

end MultiSplay.ClassicalSwitch
