import TangoSquared.Paper20261030.GapBSTRotationProgram

/-! Local access to the appendix's three physical record slots. A slot
flag identifies the represented logical vertex. Reads inspect just the
current physical node; writes first read its slots and preserve the other
two. Only one saved slot record and the supplied new value are needed. -/

namespace TangoSquared.Paper20261030.GapBST.Storage

open ColoredStorage DynamicOptimality.LocalProgram

variable {α ρ : Type*}

inductive Flag where
  | internal | leftLeaf | rightLeaf
  deriving DecidableEq

def flag (logical : SourcePointer.Cursor α ρ) : Flag :=
  match logical.focus with
  | .fork _ _ _ => .internal
  | .leaf _ _ => match logical.ancestors with
    | .right _ _ :: _ => .rightLeaf
    | _ => .leftLeaf

def Flag.get : Flag → Slots ρ → Option ρ
  | .internal => Slots.internal
  | .leftLeaf => Slots.left
  | .rightLeaf => Slots.right

def Flag.set (fresh : ρ) : Flag → Slots ρ → Slots ρ
  | .internal,slots => {slots with internal := some fresh}
  | .leftLeaf,slots => {slots with left := some fresh}
  | .rightLeaf,slots => {slots with right := some fresh}

theorem flag_read (logical : SourcePointer.Cursor α ρ) (slots : Slots ρ) :
    (flag logical).get slots = readSlot logical slots := by
  rcases logical with ⟨focus,rest⟩
  cases focus with
  | fork => rfl
  | leaf => cases rest with
    | nil => rfl
    | cons first rest => cases first <;> rfl

inductive ReadState (ρ : Type*) where
  | start (slot : Flag)
  | done (value : Option ρ)

def readProgram : Program (ReadState ρ) α (Slots ρ)
  | .start slot => .read (fun view => .done (slot.get view.entry.2.2))
  | .done _ => .halt

theorem read_program (logical : SourcePointer.Cursor α ρ) :
    ∃ reads, Run readProgram (.start (flag logical)) (cursor logical)
      (.done (some logical.focus.rootRecord)) (cursor logical) reads 1 := by
  obtain ⟨entry,atRecord,contains⟩ := cursor_record logical
  have flagged : (flag logical).get entry.2.2 = some logical.focus.rootRecord := by
    rw [flag_read]
    exact contains
  have observed : ∃ view, observe (cursor logical) = some view ∧ view.entry = entry := by
    cases focusEq : (cursor logical).focus with
    | empty => simp [focusEq,MTR.Tree.rootKey] at atRecord
    | node left value right =>
      have same : value = entry := by simpa only [focusEq,MTR.Tree.rootKey,Option.some.injEq] using atRecord
      exact ⟨⟨value,empty left,empty right⟩,by simp [observe,focusEq],same⟩
  obtain ⟨view,observed,same⟩ := observed
  refine ⟨[entry],?_⟩
  rw [← same] at flagged ⊢
  apply Run.next (entry := some view.entry) (cost := 0)
  · exact Step.read rfl observed
  · simpa only [readProgram,flagged] using (Run.halt (program := readProgram)
      (state := ReadState.done (some logical.focus.rootRecord)) (cursor := cursor logical) rfl)

inductive WriteState (ρ : Type*) where
  | start (slot : Flag)
  | write (slots : Slots ρ)
  | done

def writeProgram (fresh : ρ) : Program (WriteState ρ) α (Slots ρ)
  | .start slot => .read (fun view => .write (slot.set fresh view.entry.2.2))
  | .write slots => .write slots .done
  | .done => .halt

theorem write_slots_program (slot : Flag) (fresh : ρ) (left right : MTR.Tree (Auxiliary.NodeRecord α (fun _ => Slots ρ)))
    (size : Nat) (key : α) (slots : Slots ρ) (rest) :
    Run (writeProgram fresh) (.start slot) ⟨.node left (size,⟨key,slots⟩) right,rest⟩
      .done ⟨.node left (size,⟨key,slot.set fresh slots⟩) right,rest⟩ [(size,⟨key,slots⟩)] 2 := by
  apply Run.next (entry := some (size,⟨key,slots⟩)) (cost := 1)
  · apply Step.read (view := ⟨(size,⟨key,slots⟩),empty left,empty right⟩) <;> rfl
  apply Run.next (entry := none) (cost := 0)
  · apply Step.write; rfl
  exact Run.halt rfl

theorem write_program (logical : SourcePointer.Cursor α ρ) (fresh : ρ) :
    ∃ reads, Run (writeProgram fresh) (.start (flag logical)) (cursor logical)
      .done (cursor ⟨logical.focus.setRoot fresh,logical.ancestors⟩) reads 2 := by
  rcases logical with ⟨focus,rest⟩
  cases focus with
  | fork value left right => exact ⟨_,write_slots_program .internal fresh _ _ _ _ _ _⟩
  | leaf key value =>
    cases rest with
    | nil => exact ⟨_,write_slots_program .leftLeaf fresh _ _ _ _ _ _⟩
    | cons first rest => cases first with
      | left value right => exact ⟨_,write_slots_program .leftLeaf fresh _ _ _ _ _ _⟩
      | right left value => exact ⟨_,write_slots_program .rightLeaf fresh _ _ _ _ _ _⟩

end TangoSquared.Paper20261030.GapBST.Storage
