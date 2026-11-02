import ChaCha.Paper20261030.GapSourceObservationProgram
import DynamicOptimality.PointerRelabel

/-! The existing gap representation used by the local auxiliary compiler.
Its separator records carry the existing false component-entry bit; each
port root carries a true bit. Relabeling and gap substitution preserve
the identity of every adjacent move and rotation. -/

namespace DynamicOptimality.LocalProgram

open ChaCha.MTR

theorem navigate_relabel {α β : Type*} (f : α → β) {action : Move} {before after : Pointer.Cursor α}
    (moved : navigate action before = some after) :
    navigate action (Relabel.cursor f before) = some (Relabel.cursor f after) := by
  rcases before with ⟨focus,rest⟩
  cases action with
  | left => cases focus with
    | empty => simp [navigate] at moved
    | node left key right => cases left with
      | empty => simp [navigate] at moved
      | node a x b => cases Option.some.inj moved; rfl
  | right => cases focus with
    | empty => simp [navigate] at moved
    | node left key right => cases right with
      | empty => simp [navigate] at moved
      | node a x b => cases Option.some.inj moved; rfl
  | up => cases rest with
    | nil => simp [navigate] at moved
    | cons first rest => cases first with
      | left key right => cases Option.some.inj moved; rfl
      | right left key => cases Option.some.inj moved; rfl
  | rotateRight => cases focus with
    | empty => simp [navigate] at moved
    | node left key right => cases left with
      | empty => simp [navigate] at moved
      | node a x b => cases Option.some.inj moved; rfl
  | rotateLeft => cases focus with
    | empty => simp [navigate] at moved
    | node left key right => cases right with
      | empty => simp [navigate] at moved
      | node a x b => cases Option.some.inj moved; rfl

end DynamicOptimality.LocalProgram

namespace ChaCha.Paper20261030.GapSource

open MTR ColoredStorage DynamicOptimality

theorem navigate {α ρ : Type*} (ports : Nat → Source α ρ) (base : Nat)
    {action : LocalProgram.Move} {before after : Pointer.Cursor ρ}
    (moved : LocalProgram.navigate action before = some after) :
    SourceLocalProgram.navigate action (cursor ports base before) = some (cursor ports base after) := by
  rcases before with ⟨focus,rest⟩
  cases action with
  | left => cases focus with
    | empty => simp [LocalProgram.navigate] at moved
    | node left key right => cases left with
      | empty => simp [LocalProgram.navigate] at moved
      | node a x b =>
        cases Option.some.inj moved
        simp [cursor,frames,encode,PointerGraft.offset,Tree.size,SourceLocalProgram.navigate,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | right => cases focus with
    | empty => simp [LocalProgram.navigate] at moved
    | node left key right => cases right with
      | empty => simp [LocalProgram.navigate] at moved
      | node a x b =>
        cases Option.some.inj moved
        simp [cursor,frames,encode,PointerGraft.offset,Tree.size,SourceLocalProgram.navigate,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | up => cases rest with
    | nil => simp [LocalProgram.navigate] at moved
    | cons first rest => cases first with
      | left key right =>
        cases Option.some.inj moved
        simp [cursor,frames,encode,PointerGraft.offset,Tree.size,SourceLocalProgram.navigate,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      | right left key =>
        cases Option.some.inj moved
        simp [cursor,frames,encode,PointerGraft.offset,Tree.size,SourceLocalProgram.navigate,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | rotateRight => cases focus with
    | empty => simp [LocalProgram.navigate] at moved
    | node left key right => cases left with
      | empty => simp [LocalProgram.navigate] at moved
      | node a x b =>
        cases Option.some.inj moved
        simp [cursor,frames,encode,PointerGraft.offset,Tree.size,SourceLocalProgram.navigate,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | rotateLeft => cases focus with
    | empty => simp [LocalProgram.navigate] at moved
    | node left key right => cases right with
      | empty => simp [LocalProgram.navigate] at moved
      | node a x b =>
        cases Option.some.inj moved
        simp [cursor,frames,encode,PointerGraft.offset,Tree.size,SourceLocalProgram.navigate,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

namespace Controller

open SourcePointer SourceLocalProgram Auxiliary

variable {α κ ρ : Type*}

def encodedCursor (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat)
    (logical : Metadata.Cursor κ (fun _ => ρ)) : SourcePointer.Cursor α (MarkedRecord κ ρ) :=
  GapSource.cursor ports base (Relabel.cursor mark logical)

theorem unmark_mark (entry : Record κ ρ) : unmark (mark entry) = entry := by
  rcases entry with ⟨size,key,value⟩
  rfl

theorem encode_boundary (tree : RawTree (Record κ ρ)) (ports : Nat → Source α (MarkedRecord κ ρ))
    (marked : ∀ i, boundary (ports i).rootRecord = true) (base : Nat) :
    boundary (GapSource.encode (Relabel.tree mark tree) ports base).rootRecord = LocalProgram.empty tree := by
  cases tree with
  | empty => exact marked base
  | node => rfl

theorem read_cursor (ports : Nat → Source α (MarkedRecord κ ρ))
    (marked : ∀ i, boundary (ports i).rootRecord = true) (base : Nat)
    (logical : Metadata.Cursor κ (fun _ => ρ)) (view : LocalProgram.View κ ρ)
    (observed : LocalProgram.observe logical = some view) :
    ∃ reads, Run readProgram .start (encodedCursor ports base logical) (.done view)
      (encodedCursor ports base logical) reads 7 := by
  rcases logical with ⟨focus,rest⟩
  cases focus with
  | empty => simp [LocalProgram.observe] at observed
  | node left entry right =>
    cases Option.some.inj observed
    have run := read_fork (mark entry)
      (GapSource.encode (Relabel.tree mark left) ports (base+PointerGraft.offset (rest.map (Relabel.frame mark))))
      (GapSource.encode (Relabel.tree mark right) ports
        (base+PointerGraft.offset (rest.map (Relabel.frame mark))+(Relabel.tree mark left).size+1))
      (GapSource.frames ports base (Relabel.tree mark (.node left entry right)).size (rest.map (Relabel.frame mark)))
    rw [unmark_mark,encode_boundary left ports marked,encode_boundary right ports marked] at run
    exact ⟨_,run⟩

theorem move_cursor (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat)
    {action : LocalProgram.Move} {before after : Metadata.Cursor κ (fun _ => ρ)}
    (moved : LocalProgram.navigate action before = some after) :
    SourceLocalProgram.navigate action (encodedCursor ports base before) = some (encodedCursor ports base after) :=
  GapSource.navigate ports base (LocalProgram.navigate_relabel mark moved)

end Controller
end ChaCha.Paper20261030.GapSource
