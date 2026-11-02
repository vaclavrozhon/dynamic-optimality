import DynamicOptimality.MultiFinger.Static
import DynamicOptimality.ColoredWalks.EmbeddingCursors

/-! Interleaved short walks produce literal persistent-finger executions.
The positions of inactive fingers are retained exactly. This is the
metric-to-multifinger part of the shuffle construction; a separate theorem
must still simulate these fingers by an ordinary single BST. -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR ColoredWalks

variable {α : Type*} [LinearOrder α]

def Configuration.At {reference : RawTree α} {count : Nat}
    (state : Configuration reference count) (positions : Fin count → α) : Prop :=
  ∀ index, (state.finger index).focus.rootKey = some (positions index)

/-- Each event advances only the named finger; equal consecutive positions
are allowed. Distances refer to edges of the fixed physical reference. -/
inductive ShortWalk (reference : RawTree α) (count bound : Nat) :
    (Fin count → α) → List (Fin count × α) → Prop
  | nil (positions : Fin count → α) : ShortWalk reference count bound positions []
  | cons {positions : Fin count → α} {events : List (Fin count × α)}
      (index : Fin count) (key : α)
      (close : DistanceLE reference (positions index) key bound)
      (rest : ShortWalk reference count bound (Function.update positions index key) events) :
      ShortWalk reference count bound positions ((index,key)::events)

theorem configuration_exists {reference : RawTree α} {count : Nat}
    (positions : Fin count → α) (present : ∀ index, positions index ∈ reference.inorder) :
    ∃ state : Configuration reference count, state.At positions := by
  have each : ∀ index, ∃ cursor : Pointer.Cursor α,
      cursor.tree = reference ∧ cursor.focus.rootKey = some (positions index) := by
    intro index
    obtain ⟨depth,path⟩ := exists_rootPath (present index)
    obtain ⟨cursor,key,tree,_,_⟩ := path.visit []
    exact ⟨cursor,tree,key⟩
  choose finger tree key using each
  exact ⟨⟨finger,tree⟩,key⟩

/-- An arbitrary interleaving of short walks costs one service plus the
actual adjacent-edge moves of the one selected persistent finger. -/
theorem ShortWalk.execute {reference : RawTree α} {count bound : Nat}
    {positions : Fin count → α} {events : List (Fin count × α)}
    (walk : ShortWalk reference count bound positions events)
    (ordered : reference.Ordered) (state : Configuration reference count)
    (atPositions : state.At positions) :
    ∃ (after : Configuration reference count) (cost : Nat),
      Execution state (events.map Prod.snd) after cost ∧ cost ≤ events.length*(bound+1) := by
  induction walk generalizing state with
  | nil positions => exact ⟨state,0,.done state,by simp⟩
  | @cons positions events index key close rest ih =>
    obtain ⟨a,b,distance,aTree,bTree,aKey,bKey,moves,paid⟩ := close.moves []
    have same : a = state.finger index := cursors_eq_of_key a (state.finger index)
      (positions index) (aTree.trans (state.valid index).symm)
      (aTree.symm ▸ ordered) aKey (atPositions index)
    have actual : Moves (state.finger index) b distance := same ▸ moves
    obtain ⟨middle,atLast,unchanged,front⟩ := state.move_path index actual
    have updated : middle.At (Function.update positions index key) := by
      intro other
      by_cases equal : other = index
      · subst other
        simpa only [atLast,Function.update_self] using bKey
      · simpa only [unchanged other equal,Function.update_of_ne equal] using atPositions other
    obtain ⟨after,cost,tail,bounded⟩ := ih middle updated
    have served : Execution middle (key::events.map Prod.snd) after (cost+1) :=
      .serve index key (by simpa only [atLast] using bKey) tail
    refine ⟨after,distance+(cost+1),?_,?_⟩
    · simpa only [List.nil_append,List.map_cons] using front.append served
    · simp only [List.length_cons]
      nlinarith

end DynamicOptimality.MultiFinger
