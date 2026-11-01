import TangoSquared.Paper20261030.LocalBalance

/-!
# Pointer traces with explicit record updates

A record contains a cached size and the dependent pair of key and payload.
An update changes the cached size or payload at the current cursor; it
cannot change the key or any other record. Navigation and rotations are the
ordinary pointer operations on these records. Reads and writes each cost
one. Forgetting the sizes and payloads produces an ordinary key-pointer
trace, with a visit charged for each record read or write.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open TangoSquared.MTR

variable {α : Type*} {β : α → Type*}

abbrev Cursor (α : Type*) (β : α → Type*) := Pointer.Cursor (NodeRecord α β)

inductive Step : Cursor α β → Cursor α β → Prop
  | nav {c d} (h : Pointer.Step c d) : Step c d
  | write (l r : MTR.Tree (NodeRecord α β)) (old fresh : Nat) (entry : Sigma β)
      (ancestors : List (Pointer.Frame (NodeRecord α β))) :
      Step ⟨.node l (old,entry) r,ancestors⟩ ⟨.node l (fresh,entry) r,ancestors⟩
  | writeValue (l r : MTR.Tree (NodeRecord α β)) (size : Nat) (key : α)
      (old fresh : β key) (ancestors : List (Pointer.Frame (NodeRecord α β))) :
      Step ⟨.node l (size,⟨key,old⟩) r,ancestors⟩
        ⟨.node l (size,⟨key,fresh⟩) r,ancestors⟩

inductive Trace : Cursor α β → List (NodeRecord α β) → Cursor α β → Nat → Prop
  | nil (c) : Trace c [] c 0
  | step {c d e xs cost} (h : Step c d) (rest : Trace d xs e cost) :
      Trace c xs e (cost + 1)
  | read {c d entry xs cost} (atRecord : MTR.Tree.rootKey c.focus = some entry)
      (rest : Trace c xs d cost) : Trace c (entry :: xs) d (cost + 1)

theorem Trace.append {c d e : Cursor α β} {xs ys : List (NodeRecord α β)} {m n : Nat}
    (h : Trace c xs d m) (g : Trace d ys e n) : Trace c (xs ++ ys) e (m + n) := by
  induction h with
  | nil => simpa using g
  | step move rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.step move (ih g)
  | read atRecord rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.read atRecord (ih g)

theorem Trace.ofPointer {c d : Cursor α β} {xs : List (NodeRecord α β)} {cost : Nat}
    (h : Pointer.Trace c xs d cost) : Trace c xs d cost := by
  induction h with
  | nil => exact .nil _
  | step move rest ih => exact .step (.nav move) ih
  | serve atRecord rest ih => exact .read atRecord ih

def forgetTree : MTR.Tree (NodeRecord α β) → MTR.Tree α
  | .empty => .empty
  | .node l record r => .node (forgetTree l) record.2.1 (forgetTree r)

def forgetFrame : Pointer.Frame (NodeRecord α β) → Pointer.Frame α
  | .left record r => .left record.2.1 (forgetTree r)
  | .right l record => .right (forgetTree l) record.2.1

def forgetCursor (c : Cursor α β) : Pointer.Cursor α :=
  ⟨forgetTree c.focus,c.ancestors.map forgetFrame⟩

theorem forget_recordTree (t : Std.DTreeMap.Internal.Impl α β) :
    forgetTree (recordTree t) = erase t := by
  induction t <;> simp [recordTree,forgetTree,erase, *]

theorem forget_nav {c d : Cursor α β} (h : Pointer.Step c d) :
    Pointer.Step (forgetCursor c) (forgetCursor d) := by
  cases h
  · exact .left _ _ _ _ _ _
  · exact .right _ _ _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _
  · exact .rotateRight _ _ _ _ _ _
  · exact .rotateLeft _ _ _ _ _ _

/-- Record updates remain charged visits after erasure. The resulting
word is the observation word of this auxiliary operation, not the original
user request sequence. -/
theorem Trace.forget {c d : Cursor α β} {xs : List (NodeRecord α β)} {cost : Nat}
    (h : Trace c xs d cost) :
    ∃ visits, Pointer.Trace (forgetCursor c) visits (forgetCursor d) cost := by
  induction h with
  | nil => exact ⟨[],.nil _⟩
  | @step c d e xs cost move rest ih =>
    obtain ⟨visits, ht⟩ := ih
    cases move with
    | nav hm => exact ⟨visits,.step (forget_nav hm) ht⟩
    | write l r old fresh entry ancestors => exact ⟨entry.1 :: visits,.serve rfl ht⟩
    | writeValue l r size key old fresh ancestors => exact ⟨key :: visits,.serve rfl ht⟩
  | @read c d entry xs cost atRecord rest ih =>
    obtain ⟨visits, ht⟩ := ih
    have he : MTR.Tree.rootKey (forgetCursor c).focus = some entry.2.1 := by
      rcases c with ⟨focus,ancestors⟩
      cases focus with
      | empty => contradiction
      | node l record r =>
        have hh : record = entry := Option.some.inj atRecord
        subst record
        rfl
    exact ⟨entry.2.1 :: visits,.serve he ht⟩

end TangoSquared.Paper20261030.Auxiliary.Metadata
