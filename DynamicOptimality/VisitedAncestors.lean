import DynamicOptimality.Basic

/-! A root-starting ordinary pointer trace has visited every ancestor of
its final cursor. Consequently any key on that ancestor path can be
served during the trace for one additional unit of cost. This uses the
shared pointer semantics, including rotations at the current cursor. -/

namespace DynamicOptimality

open TangoSquared.MTR TangoSquared.MTR.Pointer

variable {α : Type*}

def ancestorKeys : List (Frame α) → List α
  | [] => []
  | .left key _ :: rest => key :: ancestorKeys rest
  | .right _ key :: rest => key :: ancestorKeys rest

def pathKeys (cursor : Cursor α) : List α := cursor.focus.rootKey.toList ++ ancestorKeys cursor.ancestors

theorem step_ancestor_keys {before after : Cursor α} (step : Step before after) :
    ∀ key ∈ ancestorKeys after.ancestors, key ∈ pathKeys before := by
  cases step <;> intro key member <;>
    simp_all [pathKeys,ancestorKeys,Tree.rootKey,List.mem_cons]

theorem trace_serve_path_or_initial {before after : Cursor α} {cost : Nat}
    (execution : Trace before [] after cost) {key : α} (member : key ∈ pathKeys after) :
    key ∈ pathKeys before ∨ Trace before [key] after (cost+1) := by
  cases execution with
  | nil => exact .inl member
  | @step before middle after _ tailCost move rest =>
    obtain wasPresent | served := trace_serve_path_or_initial rest member
    · obtain atRoot | atAncestor := List.mem_append.mp wasPresent
      · have atKey : middle.focus.rootKey = some key := Option.mem_toList.mp atRoot
        exact .inr (.step move (.serve atKey rest))
      · exact .inl (step_ancestor_keys move key atAncestor)
    · exact .inr (.step move served)
termination_by cost

theorem trace_serve_ancestor {tree : RawTree α} {after : Cursor α} {cost : Nat}
    (execution : Trace (.atRoot tree) [] after cost) {key : α} (member : key ∈ pathKeys after) :
    Trace (.atRoot tree) [key] after (cost+1) := by
  obtain wasPresent | served := trace_serve_path_or_initial execution member
  · have atKey : tree.rootKey = some key := by
      simpa only [pathKeys,Cursor.atRoot,ancestorKeys,List.append_nil,Option.mem_toList] using wasPresent
    exact .serve atKey execution
  · exact served

end DynamicOptimality
