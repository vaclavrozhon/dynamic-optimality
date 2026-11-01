import TangoSquared.PointerModel

/-!
# Exact pointer simulation of fixed exterior host blocks

Every macro node expands to a minimum cap, a maximum cap, and an opaque
internal body. Its two macro children occupy the exterior gaps. Macro
pointer moves and rotations have a constant-cost ordinary pointer trace;
no step enters any opaque body. This is a structural simulation, not a
proof that a recursive execution has only exterior host transitions.
-/

namespace TangoSquared.MTR.ExteriorHostBlocks

open Tree Pointer

variable {α β : Type*}

structure Host (α : Type*) where
  lo : α
  hi : α
  body : Tree α

def render (hosts : β → Host α) : Tree β → Tree α
  | .empty => .empty
  | .node l h r => .node (render hosts l) (hosts h).lo
      (.node (hosts h).body (hosts h).hi (render hosts r))

def frame (hosts : β → Host α) : Frame β → List (Frame α)
  | .left h r => [.left (hosts h).lo
      (.node (hosts h).body (hosts h).hi (render hosts r))]
  | .right l h => [.right (hosts h).body (hosts h).hi,
      .right (render hosts l) (hosts h).lo]

def frames (hosts : β → Host α) (fs : List (Frame β)) : List (Frame α) :=
  fs.flatMap (frame hosts)

def cursor (hosts : β → Host α) (c : Cursor β) : Cursor α :=
  ⟨render hosts c.focus, frames hosts c.ancestors⟩

theorem plug_render (hosts : β → Host α) (t : Tree β) (fs : List (Frame β)) :
    plug (render hosts t) (frames hosts fs) = render hosts (plug t fs) := by
  induction fs generalizing t with
  | nil => rfl
  | cons f fs ih =>
      cases f with
      | left h r =>
          change Pointer.plug (render hosts (.node t h r)) (frames hosts fs) =
            render hosts (Pointer.plug (.node t h r) fs)
          exact ih _
      | right l h =>
          change Pointer.plug (render hosts (.node l h t)) (frames hosts fs) =
            render hosts (Pointer.plug (.node l h t) fs)
          exact ih _

theorem cursor_tree (hosts : β → Host α) (c : Cursor β) :
    (cursor hosts c).tree = render hosts c.tree :=
  plug_render hosts c.focus c.ancestors

/-- A macro left move costs one real move, a right move costs two,
and either macro rotation costs four. Every opaque body is retained. -/
theorem step_simulation (hosts : β → Host α) {c d : Cursor β}
    (h : Step c d) :
    ∃ cost ≤ 4, Trace (cursor hosts c) [] (cursor hosts d) cost := by
  cases h with
  | left A B C x y rest =>
      refine ⟨1, by omega, ?_⟩
      exact .step (.left _ _ _ _ _ _) (.nil _)
  | right A B C x y rest =>
      refine ⟨2, by omega, ?_⟩
      exact .step (.right _ _ _ _ _ _)
        (.step (.right _ _ _ _ _ _) (.nil _))
  | upLeft A B x rest =>
      refine ⟨1, by omega, ?_⟩
      exact .step (.upLeft _ _ _ _) (.nil _)
  | upRight A B x rest =>
      refine ⟨2, by omega, ?_⟩
      exact .step (.upRight _ _ _ _) (.step (.upRight _ _ _ _) (.nil _))
  | rotateLeft A B C x y rest =>
      refine ⟨4, by omega, ?_⟩
      exact .step (.right _ _ _ _ _ _)
        (.step (.rotateLeft _ _ _ _ _ _)
          (.step (.upRight _ _ _ _)
            (.step (.rotateLeft _ _ _ _ _ _) (.nil _))))
  | rotateRight A B C x y rest =>
      refine ⟨4, by omega, ?_⟩
      exact .step (.rotateRight _ _ _ _ _ _)
        (.step (.right _ _ _ _ _ _)
          (.step (.rotateRight _ _ _ _ _ _)
            (.step (.upRight _ _ _ _) (.nil _))))

theorem trace_append {c d e : Cursor α} {xs ys : List α} {i j : Nat}
    (h : Trace c xs d i) (h' : Trace d ys e j) :
    Trace c (xs ++ ys) e (i + j) := by
  induction h with
  | nil => simpa using h'
  | step move rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.step move (ih h')
  | serve at_key rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.serve at_key (ih h')

theorem rootKey_render (hosts : β → Host α) (t : Tree β) :
    rootKey (render hosts t) = (rootKey t).map (fun h => (hosts h).lo) := by
  cases t <;> rfl

/-- Simulate an entire macro trace, serving each host at its minimum cap.
The cap visits are the interface events; serving an original query inside
a host is still the responsibility of its local backend. -/
theorem trace_simulation (hosts : β → Host α) {c d : Cursor β}
    {xs : List β} {cost : Nat} (h : Trace c xs d cost) :
    ∃ actual ≤ 4 * cost,
      Trace (cursor hosts c) (xs.map (fun h => (hosts h).lo)) (cursor hosts d) actual := by
  induction h with
  | nil c => exact ⟨0, by omega, .nil _⟩
  | step move rest ih =>
      obtain ⟨stepCost, hs, ht⟩ := step_simulation hosts move
      obtain ⟨restCost, hr, hu⟩ := ih
      exact ⟨stepCost + restCost, by omega, trace_append ht hu⟩
  | @serve c d x xs cost at_key rest ih =>
      obtain ⟨actual, ha, ht⟩ := ih
      refine ⟨actual + 1, by omega, .serve ?_ ht⟩
      change rootKey (render hosts c.focus) = some (hosts x).lo
      rw [rootKey_render, at_key]
      rfl

theorem access_simulation (hosts : β → Host α) {x : β}
    {before after : Tree β} {cost : Nat} (h : Access x before after cost) :
    ∃ actual ≤ 4 * cost,
      Access (hosts x).lo (render hosts before) (render hosts after) actual := by
  obtain ⟨final, hfinal, ht⟩ := h
  obtain ⟨actual, ha, hs⟩ := trace_simulation hosts ht
  refine ⟨actual, ha, cursor hosts final, ?_, ?_⟩
  · rw [cursor_tree, hfinal]
  · exact hs

/-- Two reached caps per macro node. Its internal body and all exterior
frontiers will be restored through the ordinary graft operation. -/
def caps (hosts : β → Host α) (t : Tree β) : Tree α :=
  render (fun h => { hosts h with body := .empty }) t

theorem inorder_caps (hosts : β → Host α) (t : Tree β) :
    inorder (caps hosts t) = (inorder t).flatMap (fun h => [(hosts h).lo, (hosts h).hi]) := by
  induction t with
  | empty => rfl
  | node l h r ihl ihr =>
      simp only [caps, render, inorder, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] at ihl ihr ⊢
      rw [ihl, ihr]
      simp [List.append_assoc]

theorem size_caps (hosts : β → Host α) (t : Tree β) :
    size (caps hosts t) = 2 * size t := by
  induction t with
  | empty => rfl
  | node l h r ihl ihr =>
      simp only [caps, render, size] at ihl ihr ⊢
      omega

/-- A reached macro hull can be rebuilt in linear actual work while
preserving every internal body AND every opaque exterior frontier.
In inorder, gaps at odd offsets from `start` are the host bodies and gaps
at even offsets are the macro frontiers. No ownership or ordering facts are hidden
in the cost: the same literal gap trees occur at both endpoints. -/
theorem hull_simulation (hosts : β → Host α) (s t : Tree β)
    (same : inorder s = inorder t) (gaps : Nat → Tree α) (start : Nat) :
    ∃ rotations ≤ 12 * size s,
      RestrictedSteps rotations (graft (caps hosts s) gaps start)
        (graft (caps hosts t) gaps start) := by
  have hc : inorder (caps hosts s) = inorder (caps hosts t) := by
    rw [inorder_caps, inorder_caps, same]
  obtain ⟨k, hk, hs⟩ := graft_simulation_linear (caps hosts s) (caps hosts t) hc gaps start
  have he : size s = size t := by
    rw [← length_inorder, same, length_inorder]
  rw [size_caps, size_caps, ← he] at hk
  exact ⟨k, by omega, hs⟩

end TangoSquared.MTR.ExteriorHostBlocks
