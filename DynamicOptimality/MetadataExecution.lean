import TangoSquared.Paper20261030.MetadataPointer
import DynamicOptimality.VisitedAncestors

/-! Request-serving executions for the existing decorated pointer model.
Metadata reads and writes remain charged. Serving a key requires an actual
read at that key, and erasure yields the shared ordinary BST execution. -/

namespace DynamicOptimality

open TangoSquared.MTR

variable {α : Type*}

theorem trace_erase_services {before after : Pointer.Cursor α} {visits : List α} {budget : Nat}
    (run : Pointer.Trace before visits after budget) :
    ∃ cost ≤ budget, Pointer.Trace before [] after cost := by
  induction run with
  | nil => exact ⟨0,le_rfl,.nil _⟩
  | step move rest ih =>
    obtain ⟨cost,bound,run⟩ := ih
    exact ⟨cost+1,by omega,.step move run⟩
  | serve atKey rest ih =>
    obtain ⟨cost,bound,run⟩ := ih
    exact ⟨cost,by omega,run⟩

theorem trace_select_service [DecidableEq α] {before after : Pointer.Cursor α} {visits : List α} {budget : Nat}
    (run : Pointer.Trace before visits after budget) {key : α} (member : key ∈ visits) :
    ∃ cost ≤ budget, Pointer.Trace before [key] after cost := by
  induction run with
  | nil => simp at member
  | step move rest ih =>
    obtain ⟨cost,bound,run⟩ := ih member
    exact ⟨cost+1,by omega,.step move run⟩
  | @serve before after first tail cost atKey rest ih =>
    obtain rfl | later := List.mem_cons.mp member
    · obtain ⟨cost,bound,run⟩ := trace_erase_services rest
      exact ⟨cost+1,by omega,.serve atKey run⟩
    · obtain ⟨cost,bound,run⟩ := ih later
      exact ⟨cost,by omega,run⟩

end DynamicOptimality

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open MTR
open DynamicOptimality

variable {α : Type*} {β : α → Type*}

theorem forget_root (tree : MTR.Tree (NodeRecord α β)) :
    (forgetTree tree).rootKey = tree.rootKey.map (fun entry => entry.2.1) := by cases tree <;> rfl

theorem forget_tree (cursor : Cursor α β) :
    (forgetCursor cursor).tree = forgetTree cursor.tree := by
  rcases cursor with ⟨focus,rest⟩
  induction rest generalizing focus with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | left entry right => exact ih (.node focus entry right)
    | right left entry => exact ih (.node left entry focus)

theorem root_record {cursor : Cursor α β} {key : α}
    (atKey : (forgetCursor cursor).focus.rootKey = some key) :
    ∃ entry, cursor.focus.rootKey = some entry ∧ entry.2.1 = key := by
  rcases cursor with ⟨focus,rest⟩
  cases focus with
  | empty => contradiction
  | node left entry right => exact ⟨entry,rfl,Option.some.inj atKey⟩

theorem step_ancestor_keys {before after : Cursor α β} (move : Step before after) :
    ∀ key ∈ ancestorKeys (forgetCursor after).ancestors, key ∈ pathKeys (forgetCursor before) := by
  cases move with
  | nav move => exact DynamicOptimality.step_ancestor_keys (forget_nav move)
  | write => intro key member; exact List.mem_append_right _ member
  | writeValue => intro key member; exact List.mem_append_right _ member

theorem trace_read_path_or_initial {before after : Cursor α β} {reads : List (NodeRecord α β)} {cost : Nat}
    (run : Trace before reads after cost) {key : α} (member : key ∈ pathKeys (forgetCursor after)) :
    key ∈ pathKeys (forgetCursor before) ∨
      ∃ reads', Trace before reads' after (cost+1) ∧ key ∈ reads'.map (fun entry => entry.2.1) := by
  induction run with
  | nil => exact .inl member
  | @step before middle after reads cost move rest ih =>
    obtain initial | ⟨reads',run,served⟩ := ih member
    · obtain atRoot | ancestor := List.mem_append.mp initial
      · obtain ⟨entry,atRecord,sameKey⟩ := root_record (Option.mem_toList.mp atRoot)
        exact .inr ⟨entry::reads,.step move (.read atRecord rest),by simp [sameKey]⟩
      · exact .inl (step_ancestor_keys move key ancestor)
    · exact .inr ⟨reads',.step move run,served⟩
  | read atRecord rest ih =>
    obtain initial | ⟨reads',run,served⟩ := ih member
    · exact .inl initial
    · exact .inr ⟨_::reads',.read atRecord run,List.mem_cons_of_mem _ served⟩

theorem trace_read_ancestor {tree : MTR.Tree (NodeRecord α β)} {after : Cursor α β}
    {reads : List (NodeRecord α β)} {cost : Nat}
    (run : Trace (.atRoot tree) reads after cost) {key : α} (member : key ∈ pathKeys (forgetCursor after)) :
    ∃ reads', Trace (.atRoot tree) reads' after (cost+1) ∧ key ∈ reads'.map (fun entry => entry.2.1) := by
  obtain initial | served := trace_read_path_or_initial run member
  · have atKey : (forgetCursor (.atRoot tree)).focus.rootKey = some key := by
      simpa only [pathKeys,forgetCursor,Pointer.Cursor.atRoot,List.map_nil,ancestorKeys,List.append_nil,Option.mem_toList] using initial
    obtain ⟨entry,atRecord,sameKey⟩ := root_record atKey
    exact ⟨entry::reads,.read atRecord run,by simp [sameKey]⟩
  · exact served

def Access (key : α) (before after : MTR.Tree (NodeRecord α β)) (cost : Nat) : Prop :=
  ∃ reads, Trace (.atRoot before) reads (.atRoot after) cost ∧ key ∈ reads.map (fun entry => entry.2.1)

inductive Execution : MTR.Tree (NodeRecord α β) → List α → MTR.Tree (NodeRecord α β) → Nat → Prop
  | nil (tree) : Execution tree [] tree 0
  | cons {before middle after key requests firstCost lastCost}
      (first : Access key before middle firstCost) (rest : Execution middle requests after lastCost) :
      Execution before (key::requests) after (firstCost+lastCost)

theorem trace_forget_reads {before after : Cursor α β} {reads : List (NodeRecord α β)} {cost : Nat}
    (run : Trace before reads after cost) :
    ∃ visits, Pointer.Trace (forgetCursor before) visits (forgetCursor after) cost ∧
      (reads.map (fun entry => entry.2.1)).Sublist visits := by
  induction run with
  | nil => exact ⟨[],.nil _,List.Sublist.refl []⟩
  | step move rest ih =>
    obtain ⟨visits,run,included⟩ := ih
    cases move with
    | nav move => exact ⟨visits,.step (forget_nav move) run,included⟩
    | write => exact ⟨_::visits,.serve rfl run,included.cons _⟩
    | writeValue => exact ⟨_::visits,.serve rfl run,included.cons _⟩
  | read atRecord rest ih =>
    obtain ⟨visits,run,included⟩ := ih
    refine ⟨_::visits,.serve ?_ run,included.cons_cons _⟩
    change (forgetTree _).rootKey = _
    rw [forget_root,atRecord]
    rfl

theorem Access.pointer [DecidableEq α] {before after : MTR.Tree (NodeRecord α β)} {key : α} {budget : Nat}
    (access : Access key before after budget) :
    ∃ cost ≤ budget, Pointer.Access key (forgetTree before) (forgetTree after) cost := by
  obtain ⟨reads,run,served⟩ := access
  obtain ⟨visits,pointer,included⟩ := trace_forget_reads run
  obtain ⟨cost,bound,selected⟩ := trace_select_service pointer (included.subset served)
  exact ⟨cost,bound,.atRoot _,rfl,selected⟩

theorem Execution.pointer [DecidableEq α] {before after : MTR.Tree (NodeRecord α β)} {requests : List α} {budget : Nat}
    (execution : Execution before requests after budget) :
    ∃ cost ≤ budget, Pointer.Execution (forgetTree before) requests (forgetTree after) cost := by
  induction execution with
  | nil => exact ⟨0,le_rfl,.nil _⟩
  | cons first rest ih =>
    obtain ⟨firstCost,firstBound,firstRun⟩ := first.pointer
    obtain ⟨lastCost,lastBound,lastRun⟩ := ih
    exact ⟨firstCost+lastCost,by omega,.cons firstRun lastRun⟩

end TangoSquared.Paper20261030.Auxiliary.Metadata
