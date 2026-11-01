import TangoSquared.Paper20261030.LocalStructuralParent
import TangoSquared.Paper20261030.SourceProgramRecordMap

/-! Pointwise record invariants under actual cursor navigation and local
root writes. These lemmas also apply to the opaque blocks and the entire
outer context of a local operation.
-/

namespace TangoSquared.Paper20261030.SourceRecordPredicate

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ : Type*}

def Holds (predicate : ρ → Prop) (source : Source α ρ) : Prop :=
  ∀ record ∈ source.inventory id, predicate record

theorem leaf (predicate : ρ → Prop) (key : α) (record : ρ) :
    Holds predicate (.leaf key record) ↔ predicate record := by
  simp only [Holds,Source.inventory_leaf,id_eq,Multiset.mem_singleton,forall_eq]

theorem fork (predicate : ρ → Prop) (record : ρ) (left right : Source α ρ) :
    Holds predicate (.fork record left right) ↔ predicate record ∧ Holds predicate left ∧ Holds predicate right := by
  simp only [Holds,Source.inventory_fork,id_eq,Multiset.mem_add,Multiset.mem_singleton,
    or_imp,forall_and,forall_eq,and_assoc]

theorem root (predicate : ρ → Prop) (source : Source α ρ) (valid : Holds predicate source) :
    predicate source.rootRecord := valid _ (Structural.root_mem_inventory id source)

theorem focused (predicate : ρ → Prop) (current : Cursor α ρ) (valid : Holds predicate current.tree) :
    predicate current.focus.rootRecord :=
  valid _ (Multiset.mem_of_le (Structural.inventory_le_plug id current.focus current.ancestors)
    (Structural.root_mem_inventory id current.focus))

theorem setRoot (predicate : ρ → Prop) (source : Source α ρ) (fresh : ρ)
    (valid : Holds predicate source) (good : predicate fresh) : Holds predicate (source.setRoot fresh) := by
  cases source with
  | leaf key record => exact (leaf predicate key fresh).mpr good
  | fork record left right =>
    obtain ⟨_,hl,hr⟩ := (fork predicate record left right).mp valid
    exact (fork predicate fresh left right).mpr ⟨good,hl,hr⟩

theorem context (predicate : ρ → Prop) (before after : Source α ρ) (outside : List (Frame α ρ))
    (localChange : Holds predicate before → Holds predicate after) :
    Holds predicate (plug before outside) → Holds predicate (plug after outside) := by
  induction outside generalizing before after with
  | nil => exact localChange
  | cons frame rest ih =>
    cases frame with
    | left record sibling =>
      apply ih
      intro valid
      obtain ⟨hr,hb,hs⟩ := (fork predicate record before sibling).mp valid
      exact (fork predicate record after sibling).mpr ⟨hr,localChange hb,hs⟩
    | right sibling record =>
      apply ih
      intro valid
      obtain ⟨hr,hs,hb⟩ := (fork predicate record sibling before).mp valid
      exact (fork predicate record sibling after).mpr ⟨hr,hs,localChange hb⟩

theorem write (predicate : ρ → Prop) (current : Cursor α ρ) (fresh : ρ)
    (valid : Holds predicate current.tree) (good : predicate fresh) :
    Holds predicate (plug (current.focus.setRoot fresh) current.ancestors) :=
  context predicate current.focus (current.focus.setRoot fresh) current.ancestors
    (fun atFocus => setRoot predicate current.focus fresh atFocus good) valid

theorem navigation (predicate : ρ → Prop) (action : DynamicOptimality.LocalProgram.Move)
    (before after : Cursor α ρ) (moved : navigate action before = some after)
    (valid : Holds predicate before.tree) : Holds predicate after.tree := by
  unfold Holds
  rw [← navigate_inventory id action moved]
  exact valid

end TangoSquared.Paper20261030.SourceRecordPredicate
