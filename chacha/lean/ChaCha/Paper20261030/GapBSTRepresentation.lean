import ChaCha.Paper20261030.SourceInitialization

/-!
# The manuscript's gap-key encoding in the existing ordinary BST model

An internal source vertex receives the last key of its left subtree.
Deleting source leaves gives the gap tree; its missing final key becomes
an additional root. The resulting inorder word is exactly the original
leaf word. A logical leaf cursor is parked at its physical parent.
Metadata storage and local access to it are separate from this routing
encoding.
-/

namespace ChaCha.Paper20261030.GapBST

open ColoredStorage RouterProjection

variable {α ρ : Type*}

def lastKey : Source α ρ → α
  | .leaf key _ => key
  | .fork _ _ right => lastKey right

def gaps : Source α ρ → MTR.Tree α
  | .leaf _ _ => .empty
  | .fork _ left right => .node (gaps left) (lastKey left) (gaps right)

def encode (tree : Source α ρ) : MTR.Tree α := .node (gaps tree) (lastKey tree) .empty

theorem gaps_word (tree : Source α ρ) :
    (gaps tree).inorder ++ [lastKey tree] = tree.shape.leaves := by
  induction tree with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [gaps,lastKey,MTR.Tree.inorder,Source.shape,Router.leaves]
    rw [← ihl,← ihr,List.append_assoc,List.append_assoc]

theorem encode_word (tree : Source α ρ) : (encode tree).inorder = tree.shape.leaves := by
  simpa only [encode,MTR.Tree.inorder,List.append_nil] using gaps_word tree

def frames (last : α) : List (SourcePointer.Frame α ρ) → List (MTR.Pointer.Frame α)
  | [] => [.left last .empty]
  | .left _ right :: rest => .left last (gaps right) :: frames (lastKey right) rest
  | .right left _ :: rest => .right (gaps left) (lastKey left) :: frames last rest

def park : MTR.Tree α → List (MTR.Pointer.Frame α) → MTR.Pointer.Cursor α
  | .empty,.left key right :: rest => ⟨.node .empty key right,rest⟩
  | .empty,.right left key :: rest => ⟨.node left key .empty,rest⟩
  | tree,rest => ⟨tree,rest⟩

def cursor (logical : SourcePointer.Cursor α ρ) : MTR.Pointer.Cursor α :=
  park (gaps logical.focus) (frames (lastKey logical.focus) logical.ancestors)

theorem park_tree (tree : MTR.Tree α) (rest : List (MTR.Pointer.Frame α)) :
    (park tree rest).tree = MTR.Pointer.plug tree rest := by
  cases tree with
  | empty => cases rest with
    | nil => rfl
    | cons frame rest => cases frame <;> rfl
  | node => rfl

theorem frames_tree (focus : Source α ρ) (rest : List (SourcePointer.Frame α ρ)) :
    MTR.Pointer.plug (gaps focus) (frames (lastKey focus) rest) = encode (SourcePointer.plug focus rest) := by
  induction rest generalizing focus with
  | nil => rfl
  | cons frame rest ih =>
    cases frame with
    | left record right => exact ih (.fork record focus right)
    | right left record => exact ih (.fork record left focus)

theorem cursor_tree (logical : SourcePointer.Cursor α ρ) : (cursor logical).tree = encode logical.tree :=
  (park_tree _ _).trans (frames_tree _ _)

theorem setRoot_gaps (tree : Source α ρ) (record : ρ) : gaps (tree.setRoot record) = gaps tree := by
  cases tree <;> rfl

theorem setRoot_lastKey (tree : Source α ρ) (record : ρ) : lastKey (tree.setRoot record) = lastKey tree := by
  cases tree <;> rfl

theorem step_trace {before after : SourcePointer.Cursor α ρ} (step : SourcePointer.Step before after) :
    ∃ cost, MTR.Pointer.Trace (cursor before) [] (cursor after) cost ∧ cost ≤ 1 := by
  cases step with
  | left left right record rest =>
    cases left with
    | leaf key old => exact ⟨0,.nil _,by decide⟩
    | fork old a b => exact ⟨1,.step (.left _ _ _ _ _ _) (.nil _),le_rfl⟩
  | right left right record rest =>
    cases right with
    | leaf key old => exact ⟨0,.nil _,by decide⟩
    | fork old a b => exact ⟨1,.step (.right _ _ _ _ _ _) (.nil _),le_rfl⟩
  | upLeft left right record rest =>
    cases left with
    | leaf key old => exact ⟨0,.nil _,by decide⟩
    | fork old a b => exact ⟨1,.step (.upLeft _ _ _ _) (.nil _),le_rfl⟩
  | upRight left right record rest =>
    cases right with
    | leaf key old => exact ⟨0,.nil _,by decide⟩
    | fork old a b => exact ⟨1,.step (.upRight _ _ _ _) (.nil _),le_rfl⟩
  | rotateRight => exact ⟨1,.step (.rotateRight _ _ _ _ _ _) (.nil _),le_rfl⟩
  | rotateLeft => exact ⟨1,.step (.rotateLeft _ _ _ _ _ _) (.nil _),le_rfl⟩
  | write focus record rest =>
    refine ⟨0,?_,by decide⟩
    simp only [cursor,setRoot_gaps,setRoot_lastKey]
    exact .nil _

theorem trace {before after : SourcePointer.Cursor α ρ} {reads : List ρ} {budget : Nat}
    (execution : SourcePointer.Trace before reads after budget) :
    ∃ cost, MTR.Pointer.Trace (cursor before) [] (cursor after) cost ∧ cost ≤ budget := by
  induction execution with
  | nil => exact ⟨0,.nil _,le_rfl⟩
  | step move rest ih =>
    obtain ⟨first,firstTrace,firstBound⟩ := step_trace move
    obtain ⟨last,lastTrace,lastBound⟩ := ih
    exact ⟨first+last,Auxiliary.trace_append firstTrace lastTrace,by omega⟩
  | read rest ih =>
    obtain ⟨cost,run,bound⟩ := ih
    exact ⟨cost,run,by omega⟩

end ChaCha.Paper20261030.GapBST
