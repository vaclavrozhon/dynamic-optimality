import DynamicOptimality.ConnectedPointer
import ChaCha.Paper20261030.GraftedPointer

/-!
# A competitor serving either of two copies of each key

The endpoint embedding for multi-splay replaces a reference node by two active
copies. `expand` replaces each node of an arbitrary competing BST by a two-node
gadget: the first copy keeps the left child, and the second keeps the right
child. `copies false x` and `copies true x` are its two labels.

The simulation below accepts either copy at each request. Copy choices need not
be fixed by the competitor, and may depend on the multi-splay history. The bound
is proved for the shared adjacent-pointer execution model, including searches
and requests; it has no initialization charge proportional to a larger alphabet.
-/

namespace MultiSplay.CopyComparator

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder rootKey)
open ChaCha.MTR.Pointer (Frame Cursor Step Trace Access Execution plug)
open ChaCha.Paper20261030.Auxiliary (trace_append)

variable {α β : Type*}

def expand (copies : Bool → α → β) : RawTree α → RawTree β
  | .empty => .empty
  | .node l key r =>
      .node (expand copies l) (copies false key) (.node .empty (copies true key) (expand copies r))

def expandFrames (copies : Bool → α → β) : List (Frame α) → List (Frame β)
  | [] => []
  | .left key r :: rest =>
      .left (copies false key) (.node .empty (copies true key) (expand copies r)) ::
        expandFrames copies rest
  | .right l key :: rest =>
      .right .empty (copies true key) :: .right (expand copies l) (copies false key) ::
        expandFrames copies rest

def expandCursor (copies : Bool → α → β) (cursor : Cursor α) : Cursor β :=
  ⟨expand copies cursor.focus, expandFrames copies cursor.ancestors⟩

def requestWord (copies : Bool → α → β) (choices : List (α × Bool)) : List β :=
  choices.map (fun choice => copies choice.2 choice.1)

theorem inorder_expand (copies : Bool → α → β) (tree : RawTree α) :
    inorder (expand copies tree) = (inorder tree).flatMap (fun x => [copies false x, copies true x]) := by
  induction tree <;> simp_all [expand, inorder, List.append_assoc]

theorem expand_ordered [LinearOrder α] [LinearOrder β]
    (copies : Bool → α → β) (tree : RawTree α)
    (ordered : ChaCha.MTR.Tree.Ordered tree)
    (within : ∀ x ∈ inorder tree, copies false x < copies true x)
    (between : ∀ x ∈ inorder tree, ∀ y ∈ inorder tree,
      x < y → copies true x < copies false y) :
    ChaCha.MTR.Tree.Ordered (expand copies tree) := by
  rw [ChaCha.MTR.Tree.Ordered, inorder_expand, List.pairwise_flatMap]
  constructor
  · intro x member
    simpa using within x member
  · apply ordered.imp_of_mem
    intro x y hx hy less a ha b hb
    have cross := between x hx y hy less
    have left := within x hx
    have right := within y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact left.trans cross
    · exact left.trans (cross.trans right)
    · exact cross
    · exact cross.trans right

theorem expand_plug (copies : Bool → α → β) (tree : RawTree α) (frames : List (Frame α)) :
    plug (expand copies tree) (expandFrames copies frames) = expand copies (plug tree frames) := by
  induction frames generalizing tree with
  | nil => rfl
  | cons frame rest ih =>
      cases frame <;> simpa [plug, expandFrames, expand] using ih (.node _ _ _)

theorem expandCursor_tree (copies : Bool → α → β) (cursor : Cursor α) :
    (expandCursor copies cursor).tree = expand copies cursor.tree :=
  expand_plug copies cursor.focus cursor.ancestors

/-- Each original rotation becomes two gadget rotations and two adjacent
moves. An original child or parent move becomes at most two moves. -/
theorem step_expand {before after : Cursor α} (step : Step before after)
    (copies : Bool → α → β) :
    ∃ cost ≤ 4, Trace (expandCursor copies before) [] (expandCursor copies after) cost := by
  cases step with
  | left a b c x y rest =>
      exact ⟨1, by decide, .step (.left _ _ _ _ _ _) (.nil _)⟩
  | right a b c x y rest =>
      exact ⟨2, by decide, .step (.right _ _ _ _ _ _)
        (.step (.right _ _ _ _ _ _) (.nil _))⟩
  | upLeft a b x rest =>
      exact ⟨1, by decide, .step (.upLeft _ _ _ _) (.nil _)⟩
  | upRight a b x rest =>
      exact ⟨2, by decide, .step (.upRight _ _ _ _)
        (.step (.upRight _ _ _ _) (.nil _))⟩
  | rotateRight a b c x y rest =>
      exact ⟨4, le_rfl, .step (.rotateRight _ _ _ _ _ _)
        (.step (.right _ _ _ _ _ _) (.step (.rotateRight _ _ _ _ _ _)
          (.step (.upRight _ _ _ _) (.nil _))))⟩
  | rotateLeft a b c x y rest =>
      exact ⟨4, le_rfl, .step (.right _ _ _ _ _ _)
        (.step (.rotateLeft _ _ _ _ _ _) (.step (.upRight _ _ _ _)
          (.step (.rotateLeft _ _ _ _ _ _) (.nil _))))⟩

/-- Serving the second copy moves to it and returns to the first copy, so
the next simulated operation starts at the same gadget cursor. -/
theorem serve_expand {cursor : Cursor α} {key : α} (atKey : rootKey cursor.focus = some key)
    (copies : Bool → α → β) (choice : Bool) :
    ∃ cost ≤ 3, Trace (expandCursor copies cursor) [copies choice key]
      (expandCursor copies cursor) cost := by
  rcases cursor with ⟨focus, ancestors⟩
  cases focus with
  | empty => simp [rootKey] at atKey
  | node l root r =>
      simp only [rootKey, Option.some.injEq] at atKey
      subst root
      cases choice with
      | false => exact ⟨1, by decide, .serve rfl (.nil _)⟩
      | true =>
          exact ⟨3, le_rfl, .step (.right _ _ _ _ _ _)
            (.serve rfl (.step (.upRight _ _ _ _) (.nil _)))⟩

theorem trace_expand {before after : Cursor α} {requests : List α} {cost : Nat}
    (trace : Trace before requests after cost) (copies : Bool → α → β)
    (choices : List (α × Bool)) (projects : choices.map Prod.fst = requests) :
    ∃ expandedCost ≤ 4 * cost,
      Trace (expandCursor copies before) (requestWord copies choices)
        (expandCursor copies after) expandedCost := by
  induction trace generalizing choices with
  | nil cursor =>
      have empty : choices = [] := List.map_eq_nil_iff.mp projects
      subst choices
      exact ⟨0, le_rfl, .nil _⟩
  | step move rest ih =>
      obtain ⟨firstCost, firstBound, firstTrace⟩ := step_expand move copies
      obtain ⟨restCost, restBound, restTrace⟩ := ih choices projects
      exact ⟨firstCost + restCost, by omega, by simpa using trace_append firstTrace restTrace⟩
  | @serve cursor next key requests cost atKey rest ih =>
      cases choices with
      | nil => simp at projects
      | cons choice choices =>
          rcases choice with ⟨original, side⟩
          simp only [List.map_cons, List.cons.injEq] at projects
          rcases projects with ⟨rfl, projects⟩
          obtain ⟨firstCost, firstBound, firstTrace⟩ := serve_expand atKey copies side
          obtain ⟨restCost, restBound, restTrace⟩ := ih choices projects
          refine ⟨firstCost + restCost, by omega, ?_⟩
          simpa [requestWord] using trace_append firstTrace restTrace

theorem access_expand {before after : RawTree α} {key : α} {cost : Nat}
    (access : Access key before after cost) (copies : Bool → α → β) (choice : Bool) :
    ∃ expandedCost ≤ 4 * cost,
      Access (copies choice key) (expand copies before) (expand copies after) expandedCost := by
  obtain ⟨final, finalTree, trace⟩ := access
  obtain ⟨expandedCost, bound, expanded⟩ := trace_expand trace copies [(key, choice)] rfl
  refine ⟨expandedCost, bound, expandCursor copies final, ?_, ?_⟩
  · rw [expandCursor_tree, finalTree]
  · exact expanded

/-- The result applies to every root-starting competing execution and every
per-request copy choice, including choices made by an unrelated online history. -/
theorem execution_expand {before after : RawTree α} {requests : List α} {cost : Nat}
    (execution : Execution before requests after cost) (copies : Bool → α → β)
    (choices : List (α × Bool)) (projects : choices.map Prod.fst = requests) :
    ∃ expandedCost ≤ 4 * cost,
      Execution (expand copies before) (requestWord copies choices)
        (expand copies after) expandedCost := by
  induction execution generalizing choices with
  | nil tree =>
      have empty : choices = [] := List.map_eq_nil_iff.mp projects
      subst choices
      exact ⟨0, le_rfl, .nil _⟩
  | cons access rest ih =>
      cases choices with
      | nil => simp at projects
      | cons choice choices =>
          rcases choice with ⟨original, side⟩
          simp only [List.map_cons, List.cons.injEq] at projects
          rcases projects with ⟨rfl, projects⟩
          obtain ⟨firstCost, firstBound, firstExecution⟩ := access_expand access copies side
          obtain ⟨restCost, restBound, restExecution⟩ := ih choices projects
          exact ⟨firstCost + restCost, by omega, .cons firstExecution restExecution⟩

/-- The inactive keys of the full leaf alphabet can be placed in the gaps of
the active skeleton. The competitor never enters their interiors. -/
theorem execution_graft {before after : RawTree β} {requests : List β} {cost : Nat}
    (execution : Execution before requests after cost) (gaps : Nat → RawTree β) (base : Nat) :
    Execution (before.graft gaps base) requests (after.graft gaps base) cost := by
  induction execution with
  | nil tree => exact .nil _
  | cons access rest ih =>
      obtain ⟨final, finalTree, trace⟩ := access
      refine .cons ⟨ChaCha.Paper20261030.PointerGraft.cursor gaps base final, ?_, ?_⟩ ih
      · rw [ChaCha.Paper20261030.PointerGraft.cursor_tree, finalTree]
      · simpa only [ChaCha.Paper20261030.PointerGraft.cursor,
          ChaCha.Paper20261030.PointerGraft.offset,
          ChaCha.Paper20261030.PointerGraft.frames, Cursor.atRoot, Nat.add_zero] using
          ChaCha.Paper20261030.PointerGraft.trace trace gaps base

theorem execution_expand_graft {before after : RawTree α} {requests : List α} {cost : Nat}
    (execution : Execution before requests after cost) (copies : Bool → α → β)
    (choices : List (α × Bool)) (projects : choices.map Prod.fst = requests)
    (gaps : Nat → RawTree β) (base : Nat) :
    ∃ expandedCost ≤ 4 * cost,
      Execution ((expand copies before).graft gaps base) (requestWord copies choices)
        ((expand copies after).graft gaps base) expandedCost := by
  obtain ⟨expandedCost, bound, expanded⟩ := execution_expand execution copies choices projects
  exact ⟨expandedCost, bound, execution_graft expanded gaps base⟩

/-- A concrete competitor for the copied endpoint word, bounded by the shared
attained optimum on the original requests. The estimate is independent of the
number of inactive keys placed in `gaps`. Ordering of a particular copy labeling
and its gap trees is a separate requirement of the endpoint embedding. -/
theorem exists_competitor_of_OPT {n : Nat} (requests : List (Fin n))
    (copies : Bool → Nat → β) (choices : List (Nat × Bool))
    (projects : choices.map Prod.fst = requests.map Fin.val)
    (gaps : Nat → RawTree β) :
    ∃ (initial : DynamicOptimality.BST 0 n) (final : RawTree Nat) (cost : Nat),
      Execution ((expand copies initial.toRaw).graft gaps 0) (requestWord copies choices)
        ((expand copies final).graft gaps 0) cost ∧
      cost ≤ 148 * DynamicOptimality.OPT requests := by
  obtain ⟨initial, final, originalCost, execution, bound⟩ :=
    DynamicOptimality.exists_pointer_of_OPT requests
  obtain ⟨cost, expandedBound, expanded⟩ :=
    execution_expand_graft execution copies choices projects gaps 0
  exact ⟨initial, final, cost, expanded, by omega⟩

end MultiSplay.CopyComparator
