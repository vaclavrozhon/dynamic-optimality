import ChaCha.Paper20261030.SplayAuxiliaryAdapter
import ChaCha.Paper20261030.SplayAuxiliaryInventory
import ChaCha.Paper20261030.SplayAuxiliarySplice
import ChaCha.Paper20261030.MaintainedPrimaryComponents

/-!
# Persistent ordinary-splay components at primary endpoints

The endpoint table stores the actual unbalanced auxiliary and its complete
forest inventory. Validity refers to the same owner-indexed memory and
active or dormant source as the original Cha-Cha construction. Replacing
two endpoints retains every other component and its potential literally.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage RawComponent Decomposition
open PreferredProjection Secondary SecondaryDecomposition
open MultiSplay.Global.Preferred (Core)

variable {α ρ κ : Type*}

/-- The initial shape is the supplied reference shape. Its preferred paths
are marked, but no physical node or leaf payload is added. -/
def referenceComponent (key : ρ → κ) (right : ρ → Bool) : Source α ρ → RawComponent α κ
  | .leaf label record => terminal (.leaf label (key record))
  | .fork record left child =>
      if right record then
        prepend (key record) (referenceComponent key right left).closed
          (referenceComponent key right child)
      else
        append (referenceComponent key right left) (key record)
          (referenceComponent key right child).closed

theorem referenceComponent_represents (key : ρ → κ) (right : ρ → Bool) (reference : Source α ρ) :
    Decomposition.Represents key right reference (referenceComponent key right reference) := by
  induction reference with
  | leaf label record => exact .leaf (.refl _)
  | fork record left child ihl ihr =>
      cases direction : right record
      · simp only [referenceComponent,direction,Bool.false_eq_true,if_false]
        exact .left direction ihl ihr (.refl _)
      · simp only [referenceComponent,direction,if_true]
        exact .right direction ihl ihr (.refl _)

theorem referenceComponent_closed (key : ρ → κ) (right : ρ → Bool) (reference : Source α ρ) :
    (referenceComponent key right reference).closed = reference.mapRecords key := by
  induction reference with
  | leaf => rfl
  | fork record left child ihl ihr =>
      cases direction : right record <;>
        simp only [referenceComponent,direction,Bool.false_eq_true,if_false,if_true,
          prepend_closed,append_closed,ihl,ihr,Source.mapRecords]

namespace Global

structure Component where
  auxiliary : RawComponent Nat Nat
  trees : List (RawTree Nat)

def Component.Valid (reference : Source Nat Cached) (component : Component) : Prop :=
  Decomposition.Represents cutKey followsRight reference component.auxiliary ∧
    Core (referenceState followsRight reference) (referenceCuts cutKey reference)
      (referenceCuts id component.auxiliary.closed) component.trees

def Component.potential (component : Component) : Nat := forestPotential component.trees

noncomputable def Component.initial (reference : Source Nat Cached) : Component :=
  let represented := represented_realizes (referenceComponent_represents cutKey followsRight reference)
  ⟨referenceComponent cutKey followsRight reference,Classical.choose represented.inventory⟩

theorem Component.initial_valid (reference : Source Nat Cached) :
    (Component.initial reference).Valid reference :=
  ⟨referenceComponent_represents cutKey followsRight reference,
    Classical.choose_spec (represented_realizes
      (referenceComponent_represents cutKey followsRight reference)).inventory⟩

theorem Component.Valid.potential_bound {reference : Source Nat Cached} {component : Component}
    (valid : component.Valid reference) :
    component.potential ≤ (referenceCuts id component.auxiliary.closed).size *
      Nat.log 2 reference.shape.height := by
  simpa only [Component.potential,rawHeight_source] using core_potential_bound valid.2

abbrev Table (α : Type*) := α → Component

variable [DecidableEq α]

def Table.Valid {height : Nat} (reference : DepthTree 0 height) (primary : PrefRouter α)
    (perfect : primary.Perfect height) (memory : MemoryKey → Bool) (components : Table α) : Prop :=
  ∀ key ∈ primary.leaves,
    (components key).Valid (componentSource reference primary perfect memory key)

noncomputable def Table.initial {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (memory : MemoryKey → Bool) : Table α :=
  fun key => Component.initial (componentSource reference primary perfect memory key)

theorem Table.initial_valid {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (memory : MemoryKey → Bool) :
    Table.Valid reference primary perfect memory (Table.initial reference primary perfect memory) :=
  fun _ _ => Component.initial_valid _

theorem Table.Valid.active {height : Nat} {reference : DepthTree 0 height}
    {primary : PrefRouter α} {perfect : primary.Perfect height} {memory : MemoryKey → Bool}
    {components : Table α} (valid : Table.Valid reference primary perfect memory components) :
    (components primary.terminal).Valid (source reference (ownerBits primary primary.terminal memory)) := by
  simpa only [componentSource_active] using valid primary.terminal primary.terminal_mem

theorem Table.Valid.incoming {height d : Nat} (reference : DepthTree 0 height) (depth : d ≤ height)
    {request : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep request d before after)
    (distinct : before.leaves.Nodup) (perfect : before.Perfect height) (memory : MemoryKey → Bool)
    (components : Table α) (valid : Table.Valid reference before perfect memory components) :
    (components after.terminal).Valid
      (suffixSource reference (intervalUpdate d (ownerBits before after.terminal memory))
        d ⟨Nat.zero_le _,depth⟩) := by
  have member : after.terminal ∈ before.leaves := by rw [← step.leaves]; exact after.terminal_mem
  have represented := valid after.terminal member
  simpa only [componentSource,if_neg (step.endpoints_ne distinct).symm,
    step.incoming_componentStart distinct,Nat.add_sub_cancel_right] using represented

theorem Table.Valid.head_outputs {height d : Nat} (reference : DepthTree 0 height)
    (depth : d ≤ height) {request : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep request d before after) (distinct : before.leaves.Nodup)
    (perfect : before.Perfect height) (memory : MemoryKey → Bool)
    (components : Table α) (valid : Table.Valid reference before perfect memory components)
    (dormant active : Component)
    (activeValid : active.Valid
      (source reference (ownerBits after after.terminal (advanceDepth before request d memory))))
    (dormantValid : dormant.Valid
      (suffixSource reference (ownerBits after before.terminal (advanceDepth before request d memory))
        d ⟨Nat.zero_le _,depth⟩)) :
    Table.Valid reference after (step.perfect perfect) (advanceDepth before request d memory)
      (Function.update (Function.update components before.terminal dormant) after.terminal active) := by
  have endpoints := step.endpoints_ne distinct
  intro key member
  by_cases isNew : key = after.terminal
  · subst key
    simpa only [Function.update_self,componentSource_active] using activeValid
  · by_cases isOld : key = before.terminal
    · subst key
      have preparedOld : intervalUpdate d (ownerBits after before.terminal (advanceDepth before request d memory)) =
          ownerBits after before.terminal (advanceDepth before request d memory) := by
        rw [old_tail_prepared step distinct memory]
        exact intervalUpdate_idempotent _ _
      simpa only [Function.update_of_ne endpoints,Function.update_self,componentSource,if_neg endpoints,
        step.old_componentStart distinct,Nat.add_sub_cancel_right,preparedOld] using dormantValid
    · have oldMember : key ∈ before.leaves := by rw [← step.leaves]; exact member
      have frame := componentSource_other reference step distinct perfect oldMember isOld isNew memory
      simpa only [Function.update_of_ne isNew,Function.update_of_ne isOld,frame] using valid key oldMember

theorem Table.Valid.prepared_head_outputs {height d : Nat} (reference : DepthTree 0 height)
    (depth : d ≤ height) {request : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep request d before after) (distinct : before.leaves.Nodup)
    (perfect : before.Perfect height) (memory : MemoryKey → Bool)
    (components : Table α) (valid : Table.Valid reference before perfect memory components)
    (dormant active : Component)
    (activeValid : active.Valid
      (source reference (spliceBits d (intervalUpdate d (ownerBits before before.terminal memory))
        (intervalUpdate d (ownerBits before after.terminal memory)))))
    (dormantValid : dormant.Valid
      (suffixSource reference (intervalUpdate d (ownerBits before before.terminal memory))
        d ⟨Nat.zero_le _,depth⟩)) :
    Table.Valid reference after (step.perfect perfect) (advanceDepth before request d memory)
      (Function.update (Function.update components before.terminal dormant) after.terminal active) := by
  apply valid.head_outputs reference depth step distinct perfect memory components dormant active
  · rw [head_memory_transfer step distinct memory]
    rw [splice_prepared_suffix] at activeValid
    exact activeValid
  · rw [old_tail_prepared step distinct memory]
    exact dormantValid

/-- This state records logical memory and actual auxiliary shapes. Its
physical primary expansion and transitions are supplied separately. -/
structure State {height : Nat} (reference : DepthTree 0 height) (keyWord : List α) where
  memory : MemoryState α
  perfect : memory.primary.Perfect height
  components : Table α
  valid : Table.Valid reference memory.primary perfect memory.preference components
  word : memory.primary.leaves = keyWord

end Global
end ChaCha.Paper20261030.SplayAuxiliary
