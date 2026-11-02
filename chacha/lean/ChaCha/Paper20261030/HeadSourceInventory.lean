import ChaCha.Paper20261030.HeadBoundaryMetadata
import ChaCha.Paper20261030.SourceRecordInventory

set_option autoImplicit false

/-! The two exchanged logical components partition exactly the same
records as their inputs. Thus a joint initial uniqueness invariant implies
uniqueness of both output components, including records transferred from
the other component. Separate per-component uniqueness would not suffice. -/

namespace ChaCha.Paper20261030.HeadSourceInventory

open ColoredStorage

variable {α ρ η : Type*}

theorem exchanged (identifier : ρ → η) (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ)
    (depth : α) (headPart oldTail incomingTail : Source α ρ) :
    (Source.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)).inventory identifier +
      (Source.fork oldHigh (.leaf depth oldTerminal) oldTail).inventory identifier =
    (Source.fork low headPart (.fork oldHigh (.leaf depth oldTerminal) oldTail)).inventory identifier +
      (Source.fork incomingHigh (.leaf depth incomingTerminal) incomingTail).inventory identifier := by
  simp only [Source.inventory_fork,Source.inventory_leaf]
  ac_rfl

theorem unique (identifier : ρ → η) (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ)
    (depth : α) (headPart oldTail incomingTail : Source α ρ)
    (initial : ((Source.fork low headPart (.fork oldHigh (.leaf depth oldTerminal) oldTail)).inventory identifier +
      (Source.fork incomingHigh (.leaf depth incomingTerminal) incomingTail).inventory identifier).Nodup) :
    ((Source.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)).inventory identifier).Nodup ∧
      ((Source.fork oldHigh (.leaf depth oldTerminal) oldTail).inventory identifier).Nodup := by
  rw [← exchanged identifier low oldHigh incomingHigh oldTerminal incomingTerminal depth headPart oldTail incomingTail] at initial
  exact ⟨(Multiset.nodup_add.mp initial).1,(Multiset.nodup_add.mp initial).2.1⟩

end ChaCha.Paper20261030.HeadSourceInventory
