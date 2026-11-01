import TangoSquared.Paper20261030.HeadSourceInventory

set_option autoImplicit false

/-! Logical identifiers are owned by finitely many endpoint components.
The sum below is ghost state: a local controller neither stores the table
nor traverses it. Two-component head exchange preserves its value even
when identifiers move from one endpoint to the other. This supplies the
joint uniqueness premise of the concrete interior head program. -/

namespace TangoSquared.Paper20261030.GlobalPrimaryInventory

variable {α η : Type*} [DecidableEq α]

/-- All logical records owned by the finite set of primary endpoints. -/
def total (keys : Finset α) (owned : α → Multiset η) : Multiset η :=
  keys.sum owned

/-- Global uniqueness includes records in every untouched component. -/
def Unique (keys : Finset α) (owned : α → Multiset η) : Prop :=
  (total keys owned).Nodup

theorem split_pair (keys : Finset α) (owned : α → Multiset η) (old fresh : α)
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh) :
    total keys owned = owned old + owned fresh + total ((keys.erase old).erase fresh) owned := by
  have first := Finset.sum_erase_add (s := keys) owned oldMem
  have second := Finset.sum_erase_add (s := keys.erase old) owned
    (Finset.mem_erase.mpr ⟨different.symm,freshMem⟩)
  unfold total
  rw [← first,← second]
  ac_rfl

theorem member_le (keys : Finset α) (owned : α → Multiset η) (key : α)
    (member : key ∈ keys) : owned key ≤ total keys owned := by
  have split := Finset.sum_erase_add (s := keys) owned member
  rw [total,← split]
  exact le_add_self

theorem pair_le (keys : Finset α) (owned : α → Multiset η) (old fresh : α)
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh) :
    owned old + owned fresh ≤ total keys owned := by
  rw [split_pair keys owned old fresh oldMem freshMem different]
  exact le_self_add

theorem Unique.component {keys : Finset α} {owned : α → Multiset η}
    (unique : Unique keys owned) {key : α} (member : key ∈ keys) :
    (owned key).Nodup :=
  Multiset.nodup_of_le (member_le keys owned key member) unique

theorem Unique.pair {keys : Finset α} {owned : α → Multiset η}
    (unique : Unique keys owned) {old fresh : α}
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh) :
    (owned old + owned fresh).Nodup :=
  Multiset.nodup_of_le (pair_le keys owned old fresh oldMem freshMem different) unique

theorem Unique.disjoint {keys : Finset α} {owned : α → Multiset η}
    (unique : Unique keys owned) {old fresh : α}
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh) :
    Disjoint (owned old) (owned fresh) :=
  (Multiset.nodup_add.mp (unique.pair oldMem freshMem different)).2.2

/-- The only required relation on the changed components is the concrete
head endpoint's equality of their combined record inventories. -/
theorem replace_pair_total (keys : Finset α) (before after : α → Multiset η) (old fresh : α)
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh)
    (pair : after old + after fresh = before old + before fresh)
    (frame : ∀ key ∈ keys, key ≠ old → key ≠ fresh → after key = before key) :
    total keys after = total keys before := by
  rw [split_pair keys after old fresh oldMem freshMem different,
    split_pair keys before old fresh oldMem freshMem different,pair]
  congr 1
  apply Finset.sum_congr rfl
  intro key member
  obtain ⟨notFresh,member⟩ := Finset.mem_erase.mp member
  obtain ⟨notOld,member⟩ := Finset.mem_erase.mp member
  exact frame key member notOld notFresh

theorem Unique.replace_pair {keys : Finset α} {before after : α → Multiset η}
    (unique : Unique keys before) {old fresh : α}
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh)
    (pair : after old + after fresh = before old + before fresh)
    (frame : ∀ key ∈ keys, key ≠ old → key ≠ fresh → after key = before key) :
    Unique keys after := by
  unfold Unique
  rw [replace_pair_total keys before after old fresh oldMem freshMem different pair frame]
  exact unique

/-- Updating precisely the two exchanged endpoints preserves the global
inventory; the active/dormant order matches the head execution endpoints. -/
theorem update_pair_total (keys : Finset α) (owned : α → Multiset η) (old fresh : α)
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh)
    (dormant active : Multiset η)
    (pair : active + dormant = owned old + owned fresh) :
    total keys (Function.update (Function.update owned old dormant) fresh active) = total keys owned := by
  apply replace_pair_total keys owned _ old fresh oldMem freshMem different
  · simpa only [Function.update_self,Function.update_of_ne different,add_comm dormant active] using pair
  · intro key member notOld notFresh
    simp only [Function.update_of_ne notFresh,Function.update_of_ne notOld]

theorem Unique.update_pair {keys : Finset α} {owned : α → Multiset η}
    (unique : Unique keys owned) {old fresh : α}
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh)
    (dormant active : Multiset η)
    (pair : active + dormant = owned old + owned fresh) :
    Unique keys (Function.update (Function.update owned old dormant) fresh active) := by
  unfold Unique
  rw [update_pair_total keys owned old fresh oldMem freshMem different dormant active pair]
  exact unique

end TangoSquared.Paper20261030.GlobalPrimaryInventory
